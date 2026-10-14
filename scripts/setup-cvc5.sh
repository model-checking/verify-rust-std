#!/bin/bash
set -euo pipefail

# Keep the arithmetic backend identical across CI platforms.
install_dir=${1:?Usage: setup-cvc5.sh INSTALL_DIRECTORY}
case "$(uname -s):$(uname -m)" in
    Linux:x86_64)
        package=cvc5-Linux-x86_64-static
        checksum=6d44abc233980a14d72cc5809287d27c3335b1d6ee863381d0b5ffcbd0d8de56
        ;;
    Darwin:arm64)
        package=cvc5-macOS-arm64-static
        checksum=18e0bd283d44f720f72bf80175169ef63e985628b7ba1502aaf812f57f981461
        ;;
    Darwin:x86_64)
        package=cvc5-macOS-x86_64-static
        checksum=bdde9557bbb9b812af270c3f418836c285957b3ed81385b87428d2d595ffbf47
        ;;
    *) echo 'Unsupported CVC5 platform' >&2; exit 2 ;;
esac

stamp="cvc5-1.2.1:$checksum"
if [[ -x "$install_dir/bin/cvc5" && -f "$install_dir/version" ]] &&
    [[ "$(cat "$install_dir/version")" == "$stamp" ]]; then
    exit 0
fi

mkdir -p "$install_dir"
staging=$(mktemp -d "$install_dir/download.XXXXXX")
trap 'rm -rf "$staging"' EXIT
curl --fail --location --retry 3 --silent --show-error \
    "https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/$package.zip" \
    --output "$staging/cvc5.zip"
actual=$(shasum -a 256 "$staging/cvc5.zip")
[[ "${actual%% *}" == "$checksum" ]] || { echo 'CVC5 checksum mismatch' >&2; exit 1; }
unzip -q "$staging/cvc5.zip" -d "$staging"
mkdir -p "$install_dir/bin"
cp "$staging/$package/bin/cvc5" "$install_dir/bin/cvc5"
cp -R "$staging/$package/licenses" "$install_dir/"
"$install_dir/bin/cvc5" --version
printf '%s\n' "$stamp" > "$install_dir/version"
