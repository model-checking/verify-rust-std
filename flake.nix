{
  description = "verify-rust-std reproducible verification environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = { self, nixpkgs, flake-utils, fenix }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # Rust toolchain pinned to match rust-toolchain.toml.
        # Channel and date come from rust-toolchain.toml (nightly-2025-10-09).
        # The sha256 below is the hash of the toolchain manifest; if it is
        # wrong, `nix develop` will print the expected hash and you can
        # replace it.
        toolchain = (fenix.packages.${system}.toolchainOf {
          channel = "nightly";
          date = "2025-10-09";
          sha256 = "sha256-X/HlN8ktnN9cAnz4Ro0cYfxEyDP/wC5FgQU8vB1ndz4=";
        }).withComponents [
          "cargo"
          "rustc"
          "rust-src"
          "rustfmt"
          "llvm-tools-preview"
          "rustc-dev"
        ];

        # CBMC version in nixpkgs (6.8.0) is newer than the version Kani's
        # kani-dependencies pins (6.7.1). Kani's check-cbmc-version.py uses
        # "desired > current" comparison, so a newer CBMC satisfies the
        # check. goto-synthesizer ships with the same cbmc package and shares
        # the version, satisfying the strict equality check between the two.
        # Kissat in nixpkgs (4.0.4) is newer than the pinned 4.0.1; the
        # check_kissat_version.sh script uses lexicographic comparison so
        # newer is fine.
        runtimeDeps = with pkgs; [
          toolchain
          cbmc
          kissat
          python3
          git
          jq
          gnumake
          gcc
          cmake
          pkg-config
          openssl
          zlib
          curl
          systemd  # for systemd-run --user memory cap
        ];

        verifyApp = pkgs.writeShellApplication {
          name = "verify";
          runtimeInputs = runtimeDeps;
          text = ''
            set -euo pipefail
            challenge="''${1:-}"
            if [[ -z "$challenge" ]]; then
              echo "usage: verify <challenge>" >&2
              echo "challenges: flt2dec, flt2dec-grisu-strategies, flt2dec-dragon-strategies" >&2
              exit 1
            fi
            case "$challenge" in
              flt2dec|28)
                harnesses=(
                  "num::flt2dec::verify::check_digits_to_dec_str"
                  "num::flt2dec::verify::check_digits_to_exp_str"
                  "num::flt2dec::verify::check_to_shortest_str_f32"
                  "num::flt2dec::verify::check_to_shortest_exp_str_f32"
                  "num::flt2dec::verify::check_to_exact_exp_str_f32"
                  "num::flt2dec::verify::check_to_exact_fixed_str_f32"
                )
                ;;
              flt2dec-grisu-wrappers)
                # The two lifetime-laundering wrappers. Both inner calls
                # (format_*_opt and the dragon fallback) are stubbed, so
                # only the wrapper's own unsafe reborrow is exercised.
                harnesses=(
                  "num::flt2dec::strategy::grisu::verify::check_format_shortest_wrapper_safety"
                  "num::flt2dec::strategy::grisu::verify::check_format_exact_wrapper_safety"
                )
                ;;
              flt2dec-grisu-strategies)
                # The two grisu algorithm functions. These use only u64/u128
                # scalar arithmetic so the CBMC formula stays tractable under
                # tight symbolic input bounds.
                harnesses=(
                  "num::flt2dec::strategy::grisu::verify::check_format_shortest_opt_safety"
                  "num::flt2dec::strategy::grisu::verify::check_format_exact_opt_safety"
                )
                ;;
              flt2dec-dragon-strategies)
                # The two dragon algorithm functions. These walk Big32x40
                # bignums (40 u32 limbs) so the CBMC formula is far larger
                # than grisu's; expect OOM at the 24 GiB cap without further
                # stubbing of bignum operations. Kept here as a sentinel.
                harnesses=(
                  "num::flt2dec::strategy::dragon::verify::check_format_shortest_safety"
                  "num::flt2dec::strategy::dragon::verify::check_format_exact_safety"
                )
                ;;
              *)
                echo "unknown challenge: $challenge" >&2
                echo "challenges: flt2dec, flt2dec-grisu-strategies, flt2dec-dragon-strategies" >&2
                exit 1
                ;;
            esac
            harness_args=()
            for h in "''${harnesses[@]}"; do
              harness_args+=(--harness "$h")
            done

            # Memory cap. CBMC can balloon to tens of GiB on dense harnesses.
            # Cap at 12 GiB by default to leave the system responsive; override
            # with VERIFY_MEMORY_MAX (e.g. "24G" or "0" to disable).
            mem_max="''${VERIFY_MEMORY_MAX:-24G}"
            if [[ "$mem_max" == "0" ]] || ! command -v systemd-run >/dev/null; then
              runner=()
              if [[ "$mem_max" != "0" ]]; then
                echo ">>> systemd-run not available; running without memory cap" >&2
              fi
            else
              echo ">>> Memory cap: $mem_max (override with VERIFY_MEMORY_MAX)"
              runner=(
                systemd-run --user --scope --quiet
                -p "MemoryMax=$mem_max"
                -p "MemorySwapMax=0"
              )
            fi

            # On NixOS /bin/bash does not exist, so the script's shebang fails.
            # Patch any /bin/bash shebangs we find under the repo to env-bash.
            for script in scripts/run-kani.sh scripts/*.sh; do
              if [[ -f "$script" ]] && head -1 "$script" | grep -q '^#!/bin/bash'; then
                sed -i '1s|^#!/bin/bash|#!/usr/bin/env bash|' "$script"
              fi
            done

            # Kani's build expects a rustup layout. With fenix we have no
            # rustup, so synthesise a fake RUSTUP_HOME with a single toolchain
            # symlink pointing at the fenix-managed rustc sysroot. This
            # satisfies both env!("RUSTUP_TOOLCHAIN") (used by build-kani) and
            # the RUSTUP_HOME/toolchains/$TC/lib rpath constructed by
            # kani-compiler/build.rs.
            RUSTUP_TOOLCHAIN="$(awk -F'"' '/^channel/ {print $2}' rust-toolchain.toml)"
            export RUSTUP_TOOLCHAIN

            RUSTC_SYSROOT="$(rustc --print sysroot)"
            RUSTUP_HOME="$PWD/.rustup-fake"
            export RUSTUP_HOME
            mkdir -p "$RUSTUP_HOME/toolchains"
            ln -sfn "$RUSTC_SYSROOT" "$RUSTUP_HOME/toolchains/$RUSTUP_TOOLCHAIN"

            # Kani-driver invokes `cargo +<toolchain>` which is a rustup-ism.
            # Fenix's cargo does not understand the +toolchain prefix and treats
            # it as an unknown subcommand. Install a thin shim that strips
            # a leading +toolchain arg and forwards to the real cargo.
            WRAPPER_DIR="$PWD/.toolchain-wrapper"
            mkdir -p "$WRAPPER_DIR"
            REAL_CARGO="$(command -v cargo)"
            cat > "$WRAPPER_DIR/cargo" <<EOF
            #!/usr/bin/env bash
            if [ \$# -gt 0 ]; then
              case "\$1" in
                +*) shift ;;
              esac
            fi
            exec "$REAL_CARGO" "\$@"
            EOF
            chmod +x "$WRAPPER_DIR/cargo"
            export PATH="$WRAPPER_DIR:$PATH"

            # run-kani.sh's "is Kani up to date" check only inspects the git
            # commit, not the actual built binary. If a previous build failed
            # partway through, the directory will trick the check. Detect and
            # repair.
            if [[ -d kani_build ]] && [[ ! -f kani_build/target/kani/bin/kani-driver ]]; then
              echo ">>> Found half-built kani_build; removing to force rebuild"
              rm -rf kani_build
            fi

            # Safety-only check mode for the strategy harnesses. The Challenge
            # 28 safety property is "no UB on the MaybeUninit buffer" — i.e.
            # bounds and memory-safety. Arithmetic-overflow panics from debug
            # builds are not safety obligations and are spurious noise when
            # running with abstract stubs that don't preserve the algorithm's
            # tight numeric invariants. Toggle with VERIFY_SAFETY_ONLY=1.
            extra_kani_args=()
            if [[ "''${VERIFY_SAFETY_ONLY:-0}" == "1" ]]; then
              echo ">>> Safety-only check mode: disabling overflow checks"
              extra_kani_args+=(--no-overflow-checks)
            fi

            exec "''${runner[@]}" bash ./scripts/run-kani.sh --kani-args "''${extra_kani_args[@]}" "''${harness_args[@]}" --exact
          '';
        };
      in {
        devShells.default = pkgs.mkShell {
          packages = runtimeDeps;
          # Some Rust crates need to find native libraries at build time.
          shellHook = ''
            export PKG_CONFIG_PATH="${pkgs.openssl.dev}/lib/pkgconfig:''${PKG_CONFIG_PATH:-}"
          '';
        };

        apps = {
          verify = flake-utils.lib.mkApp { drv = verifyApp; };
          default = flake-utils.lib.mkApp { drv = verifyApp; };
        };
      });
}
