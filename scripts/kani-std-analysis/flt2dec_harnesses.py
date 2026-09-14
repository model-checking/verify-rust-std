"""Assign flt2dec proofs to dedicated CI jobs without duplicating std partitions."""

import argparse
import json
import sys


DRAGON = "num::flt2dec::strategy::dragon::dragon_verify"
GRISU = "num::flt2dec::strategy::grisu::grisu_verify"
OPERATING_SYSTEMS = ["ubuntu-latest", "macos-latest"]


def proof_groups():
    groups = []

    def add(name, kind, harnesses):
        groups.append({"name": name, "kind": kind, "harnesses": harnesses})

    for name, module, proof in [
        ("dragon-exact", DRAGON, "check_format_exact"),
        ("dragon-shortest", DRAGON, "check_format_shortest"),
        ("grisu-exact", GRISU, "check_format_exact_opt"),
        ("grisu-shortest", GRISU, "check_format_shortest_opt"),
    ]:
        add(f"{name}-f32", "generator-f32", [
            f"{module}::f32_{group:02d}::{proof}" for group in range(4)
        ])
        for first in range(0, 32, 4):
            add(f"{name}-f64-{first:02d}-{first + 3:02d}", "generator-f64", [
                f"{module}::f64_{group:02d}::{proof}" for group in range(first, first + 4)
            ])
        add(f"{name}-fixed-exponent", "probe", [
            f"{module}::f64_exp_1023::{proof}"
        ])

    for mode in ("exact", "shortest"):
        add(f"grisu-{mode}-cached-power-39", "probe", [
            f"{GRISU}::f64_cached_power_39::check_format_{mode}_opt"
        ])

    for name, module, proof, kind in [
        ("division-contract", DRAGON, "check_div_2pow10_contract", "contract"),
        ("limb-division-contract", DRAGON, "check_div_rem_digit_contract", "contract"),
        ("bigint-small-division-contract", DRAGON, "check_div_rem_small_contract", "contract"),
        ("rounding-contract", "num::flt2dec::rounding_verify", "check_round_up_contract", "contract"),
        ("grisu-exact-rounding-contract", GRISU, "check_round_exact_contract", "contract"),
        ("grisu-shortest-rounding-contract", GRISU, "check_round_shortest_contract", "contract"),
        ("comparison-equivalence", DRAGON, "check_comparison_models_agree", "equivalence"),
        ("bit-scan-equivalence", "num::flt2dec::bit_scan_verify", "check_leading_zeros_models_agree", "equivalence"),
    ]:
        add(name, kind, [f"{module}::{proof}"])

    for first in range(0, 65, 8):
        last = min(first + 7, 64)
        add(f"estimator-equivalence-{first:02d}-{last:02d}", "equivalence", [
            f"num::flt2dec::estimator_verify::check_estimator_model_agrees_{bits:02d}"
            for bits in range(first, last + 1)
        ])
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument("--matrix", action="store_true")
    mode.add_argument("--group", choices=[group["name"] for group in proof_groups()])
    mode.add_argument("--remaining", metavar="KANI_LIST_JSON")
    args = parser.parse_args()
    if args.matrix:
        print(json.dumps({"os": OPERATING_SYSTEMS, "group": proof_groups()}, separators=(",", ":")))
    elif args.group:
        group = next(group for group in proof_groups() if group["name"] == args.group)
        print("\n".join(group["harnesses"]))
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
