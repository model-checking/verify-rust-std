"""Assign flt2dec proofs to dedicated CI jobs without duplicating std partitions."""

import argparse
import json
import sys


DRAGON = "num::imp::flt2dec::strategy::dragon::dragon_verify"
GRISU = "num::imp::flt2dec::strategy::grisu::grisu_verify"
OPERATING_SYSTEMS = ["ubuntu-latest", "macos-latest"]


def proof_groups(pointer_width=None):
    if pointer_width is None:
        pointer_width = 64 if sys.maxsize > 2**32 else 32
    if pointer_width not in (16, 32, 64):
        raise ValueError("Expected a 16-, 32-, or 64-bit target")
    limb_count = 20 if pointer_width == 64 else 40
    groups = []

    # One CI matrix holds at most 256 jobs, so generator and cached proofs form a second ("long") job.
    def add(name, kind, harnesses, timeout_minutes, backend="native", harness_backends=None,
            matrix_job="core"):
        group = {"name": name, "kind": kind, "harnesses": harnesses,
                 "timeout_minutes": timeout_minutes, "backend": backend, "matrix_job": matrix_job}
        if harness_backends:
            group["harness_backends"] = harness_backends
        groups.append(group)

    for name, module, proof, batch_size, timeout_minutes in [
        ("dragon-exact", DRAGON, "check_format_exact", 4, 60),
        ("dragon-shortest", DRAGON, "check_format_shortest", 4, 60),
        ("grisu-exact", GRISU, "check_format_exact_opt", 4, 60),
        ("grisu-shortest", GRISU, "check_format_shortest_opt", 2, 120),
    ]:
        for width, count in ((32, 4), (64, 32)):
            for first in range(0, count, batch_size):
                last = first + batch_size - 1
                partition = f"f{width}" if count == batch_size else f"f{width}-{first:02d}-{last:02d}"
                backend = "cvc5" if name == "grisu-shortest" and (width == 32 or first == 0) else "native"
                harnesses = [f"{module}::f{width}_{group:02d}::{proof}" for group in range(first, last + 1)]
                # The native backend proved f64_01 in an earlier run;  only f64_00 keeps cvc5.
                native_harnesses = {harness: "native" for harness in harnesses
                                    if backend == "cvc5" and harness == f"{module}::f64_01::{proof}"}
                add(f"{name}-{partition}", f"generator-f{width}", harnesses, timeout_minutes, backend,
                    native_harnesses, matrix_job="long")
        add(f"{name}-fixed-exponent", "probe", [
            f"{module}::f64_exp_1023::{proof}"
        ], timeout_minutes)

    for mode in ("exact", "shortest"):
        add(f"grisu-{mode}-cached-power-39", "probe", [
            f"{GRISU}::f64_cached_power_39::check_format_{mode}_opt"
        ], 120 if mode == "shortest" else 60)

    add("dragon-exact-loop-frame", "equivalence", [
        f"{DRAGON}::check_exact_digit_loop_frame"
    ], 30)

    add("grisu-fractional-threshold-contract", "contract", [
        f"{GRISU}::check_advance_fraction_threshold"
    ], 30, "cvc5")

    foundations = {"contract": [], "equivalence": []}
    for name, module, proof, kind in [
        ("division-contract", DRAGON, "check_div_2pow10_contract", "contract"),
        ("limb-division-contract", DRAGON, "check_div_rem_digit_contract", "contract"),
        ("limb-multiplication-contract", DRAGON, "check_carrying_mul_add_contract", "contract"),
        ("bigint-small-division-contract", DRAGON, "check_div_rem_small_contract", "contract"),
        ("rounding-contract", "num::imp::flt2dec::rounding_verify", "check_round_up_contract", "contract"),
        ("grisu-exact-rounding-contract", GRISU, "check_round_exact_contract", "contract"),
        ("grisu-shortest-rounding-contract", GRISU, "check_round_shortest_contract", "contract"),
        ("grisu-shortest-normalization-contract", GRISU, "check_normalize_shortest", "contract"),
        ("grisu-rounded-multiplication-contract", GRISU, "check_rounded_multiply", "contract"),
        ("grisu-normalized-multiplication-contract", GRISU, "check_normalized_multiply", "contract"),
        ("grisu-shortest-scaling-partitioning", GRISU, "check_scale_shortest_partitioning", "equivalence"),
        ("comparison-equivalence", DRAGON, "check_comparison_models_agree", "equivalence"),
        ("zero-fill-equivalence", DRAGON, "check_fill_zeroes_model_agrees", "equivalence"),
        ("addition-equivalence", DRAGON, "check_add_model_agrees", "equivalence"),
        ("subtraction-equivalence", DRAGON, "check_sub_model_agrees", "equivalence"),
        ("bit-scan-equivalence", "num::imp::flt2dec::bit_scan_verify", "check_leading_zeros_models_agree", "equivalence"),
    ]:
        foundations[kind].append(f"{module}::{proof}")

    for kind, harnesses in foundations.items():
        for first in range(0, len(harnesses), 8):
            add(f"foundations-{kind}-{first:02d}", kind, harnesses[first:first + 8], 30)

    for first in range(0, 80, 10):
        last = first + 9
        harnesses = [f"{GRISU}::check_multiply_shortest_{group:02d}"
                     for group in range(first, last + 1)]
        if first == 0:
            harnesses.append(f"{GRISU}::check_decimal_termination")
            harnesses.extend(f"{GRISU}::check_fractional_encoding_{power:02d}"
                            for power in range(16))
        add(f"grisu-multiplication-contract-{first:02d}-{last:02d}", "contract", harnesses, 7, "cvc5")

    # Each cached multiplication proof needs more than the 7-minute arithmetic budget,
    # so these native SAT proofs get their own 60-minute groups of four.
    cached_lengths = ((16, 1), (32, 2), (64, 3), (128, 5), (256, 10)) if pointer_width == 64 else (
        (16, 2), (32, 3), (64, 5), (128, 10), (256, 19))
    cached_cases = [
        f"{DRAGON}::cached_mul_pow5_{power}::size_{size:02d}"
        for power, digits in cached_lengths
        for size in range(limb_count - digits + 1)
    ]
    for first in range(0, len(cached_cases), 4):
        last = min(first + 3, len(cached_cases) - 1)
        add(f"cached-multiplication-equivalence-{first:03d}-{last:03d}", "equivalence",
            cached_cases[first:last + 1], 60, matrix_job="long")

    for first in range(0, 80, 4):
        last = min(first + 3, 79)
        add(f"grisu-shortest-scaling-contract-{first:02d}-{last:02d}", "contract", [
            f"{GRISU}::check_scale_shortest_{group:02d}" for group in range(first, last + 1)
        ], 60)

    shift_cases = [
        f"{DRAGON}::shift_width_{total:02d}::size_{size:02d}"
        for total in range(limb_count + 1)
        for size in range(total + 1)
        if total - size < limb_count
    ]
    for first in range(0, len(shift_cases), 32):
        last = min(first + 31, len(shift_cases) - 1)
        add(f"bigint-shift-equivalence-{first:03d}-{last:03d}", "equivalence",
            shift_cases[first:last + 1], 7)

    for first in range(0, limb_count, 8):
        last = min(first + 7, limb_count - 1)
        add(f"small-multiplication-equivalence-{first:02d}-{last:02d}", "equivalence", [
            f"{DRAGON}::check_mul_small_model_agrees_{size:02d}"
            for size in range(first, last + 1)
        ], 30)

    for first in range(0, 65, 8):
        last = min(first + 7, 64)
        add(f"estimator-equivalence-{first:02d}-{last:02d}", "equivalence", [
            f"num::imp::flt2dec::estimator_verify::check_estimator_model_agrees_{bits:02d}"
            for bits in range(first, last + 1)
        ], 30)

    for first in range(0, 10, 8):
        last = min(first + 7, 9)
        add(f"decimal-division-equivalence-{first:02d}-{last:02d}", "equivalence", [
            f"{GRISU}::check_decimal_division_model_agrees_{exponent:02d}"
            for exponent in range(first, last + 1)
        ], 30)
    return groups


def remaining_harnesses(inventory):
    if inventory.get("file-version") != "0.1":
        raise ValueError("Expected kani-list.json file-version 0.1")
    listed = [
        harness
        for section in ("standard-harnesses", "contract-harnesses")
        for harnesses in inventory[section].values()
        for harness in harnesses
    ]
    dedicated = {harness for group in proof_groups() for harness in group["harnesses"]}
    missing = dedicated.difference(listed)
    if missing:
        raise ValueError("Dedicated flt2dec harnesses missing from kani list: " + ", ".join(sorted(missing)))
    # Keep unrecognized harnesses, including future flt2dec proofs, in the general suite.
    # Preserve the original list order and duplicates outside the dedicated catalog.
    return [harness for harness in listed if harness not in dedicated]


def proof_matrix(selected_groups=None, pointer_width=None, platform="both", grisu_probe="none",
                 matrix_job=None):
    groups = proof_groups(pointer_width)
    if grisu_probe not in ("none", "entry", "step"):
        raise ValueError("Unknown Grisu probe: " + str(grisu_probe))
    if matrix_job not in (None, "core", "long"):
        raise ValueError("Unknown matrix job: " + str(matrix_job))
    if grisu_probe != "none" and selected_groups is None:
        raise ValueError("Grisu probes require explicitly selected manual proof groups")
    if platform != "both" and platform not in OPERATING_SYSTEMS:
        raise ValueError("Unknown proof platform: " + str(platform))
    if platform != "both" and selected_groups is None:
        raise ValueError("Platform filtering requires explicitly selected manual proof groups")
    if selected_groups is not None:
        if not isinstance(selected_groups, list) or not selected_groups:
            raise ValueError("Select a nonempty JSON array of proof group names")
        if not all(isinstance(name, str) for name in selected_groups):
            raise ValueError("Every selected proof group name must be a string")
        selected = set(selected_groups)
        if len(selected) != len(selected_groups):
            raise ValueError("Selected proof group names must be distinct")
        known = {group["name"] for group in groups}
        unknown = selected - known
        if unknown:
            raise ValueError("Unknown proof groups: " + ", ".join(sorted(unknown)))
        groups = [dict(group, name="manual-" + group["name"], catalog_name=group["name"])
                  for group in groups if group["name"] in selected]
        if grisu_probe != "none":
            for group in groups:
                if not (group["catalog_name"].startswith("grisu-shortest-")
                        and group["kind"].startswith("generator-")):
                    raise ValueError("Grisu probes require shortest generator groups")
                phase = "base" if grisu_probe == "entry" else "step"
                group.update(name=f"probe-{grisu_probe}-" + group["catalog_name"],
                             probe_property=f"num::imp::flt2dec::strategy::grisu::generate_shortest.loop_invariant_{phase}.1",
                             timeout_minutes=3)
    # A manual selection splits between the two matrix jobs;  either part can be empty.
    if matrix_job is not None:
        groups = [group for group in groups if group["matrix_job"] == matrix_job]
    return {"os": OPERATING_SYSTEMS if platform == "both" else [platform], "group": groups}


def group_harnesses(group, backend=None):
    if backend not in (None, "native", "cvc5"):
        raise ValueError("Expected the native or cvc5 proof backend")
    overrides = group.get("harness_backends", {})
    return [harness for harness in group["harnesses"]
            if backend is None or overrides.get(harness, group["backend"]) == backend]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--matrix", action="store_true")
    mode.add_argument("--group", choices=[group["name"] for group in proof_groups()])
    mode.add_argument("--remaining", metavar="KANI_LIST_JSON")
    parser.add_argument("--matrix-groups", metavar="JSON",
                        help="Select manual proof groups with distinct check names")
    parser.add_argument("--matrix-platform", choices=["both", *OPERATING_SYSTEMS], default="both",
                        help="Select a platform only for explicitly selected manual groups")
    parser.add_argument("--backend", choices=["native", "cvc5"],
                        help="Select one backend's harnesses within a proof group")
    parser.add_argument("--matrix-grisu-probe", choices=["none", "entry", "step"], default="none",
                        help="Diagnose one loop property in selected manual Grisu groups")
    parser.add_argument("--matrix-job", choices=["core", "long"],
                        help="Keep only the groups of one CI matrix job")
    args = parser.parse_args()
    if args.matrix_groups is not None and not args.matrix:
        parser.error("--matrix-groups requires --matrix")
    if args.matrix_platform != "both" and not args.matrix:
        parser.error("--matrix-platform requires --matrix")
    if args.backend is not None and not args.group:
        parser.error("--backend requires --group")
    if args.matrix_grisu_probe != "none" and not args.matrix:
        parser.error("--matrix-grisu-probe requires --matrix")
    if args.matrix_job is not None and not args.matrix:
        parser.error("--matrix-job requires --matrix")
    if args.matrix:
        try:
            selected = json.loads(args.matrix_groups) if args.matrix_groups is not None else None
            matrix = proof_matrix(selected, platform=args.matrix_platform,
                                  grisu_probe=args.matrix_grisu_probe, matrix_job=args.matrix_job)
        except (ValueError, TypeError) as error:
            parser.error(str(error))
        print(json.dumps(matrix, separators=(",", ":")))
    elif args.group:
        group = next(group for group in proof_groups() if group["name"] == args.group)
        print("\n".join(group_harnesses(group, args.backend)))
    else:
        try:
            with open(args.remaining, encoding="utf-8") as source:
                remaining = remaining_harnesses(json.load(source))
        except (OSError, ValueError, KeyError, TypeError) as error:
            parser.error(str(error))
        if remaining:
            print("\n".join(remaining))


if __name__ == "__main__":
    sys.exit(main())
