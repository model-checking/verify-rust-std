"""Assign flt2dec proofs to dedicated CI jobs without duplicating std partitions."""

import argparse
import json
import sys


DRAGON = "num::imp::flt2dec::strategy::dragon::dragon_verify"
GRISU = "num::imp::flt2dec::strategy::grisu::grisu_verify"
OPERATING_SYSTEMS = ["ubuntu-latest", "macos-latest"]
# Grisu shortest partitions that the Rust macro proves in eight exponent slices.
SLICED_SHORTEST = {"f32_00", "f32_01", "f32_02", "f32_03", "f64_00"}
# A manual Grisu probe checks one loop-contract property in place of the whole harness.
GRISU_PROBES = {
    "entry": "num::imp::flt2dec::strategy::grisu::generate_shortest.loop_invariant_base.1",
    "step": "num::imp::flt2dec::strategy::grisu::generate_shortest.loop_invariant_step.1",
    "integral-step": "num::imp::flt2dec::strategy::grisu::generate_integral_digits.loop_invariant_step.1",
}
# Dragon shortest scaling:  dragon.rs estimates K = floor((nbits + exp) * DRAGON_K_ESTIMATE / 2^32)
# for nbits in 2..=55 and proves windows 000..127 one (window, K) pair at a time.
DRAGON_K_ESTIMATE = 1292913986
DRAGON_FIXED_K_WINDOWS = 128
# Windows 000 and 001 at K = -319..-311 are the slow band (routing ruling s46).
DRAGON_SLOW_BAND = range(-319, -310)
# Pairs that timed out at 30 or 60 minutes in their group of eight or four (run 39215660085,
# ubuntu or macOS):  each runs alone at 180 minutes, its group keeps the other pairs (ruling s54 (a)).
DRAGON_SLOW_PAIRS = (
    (1, -310), (1, -314), (6, -285), (6, -286), (7, -283), (23, -206), (28, -184), (29, -175),
    (34, -154), (34, -155), (46, -91), (46, -92), (46, -93), (46, -94), (46, -95), (47, -90),
)
# Pairs whose proof splits on the exponent (dragon.rs `kNNN => K => [eNN => offset]`):  pair -> the
# exponent offsets of its pieces;  each piece covers 4 exponents and runs alone at 180 minutes.
# Each pair here hit the 180-minute cap alone:  (0, -317) in the slow band, the rest as slow pairs.
# They run in 4 pieces of 4 exponents;  the 11 pairs whose pieces hit the cap again run in
# 16 pieces of 1 exponent.
DRAGON_SPLIT_PAIRS = {
    **{pair: (0, 4, 8, 12) for pair in ((0, -317), (29, -172), (47, -91))},
    **{pair: tuple(range(16)) for pair in (
        (23, -200), (23, -201), (23, -202), (23, -203), (23, -204), (23, -205), (28, -183),
        (29, -173), (29, -174), (34, -151), (34, -152), (34, -153),
    )},
}
# Pieces of the 16-piece split pairs that hit the 180-minute cap with CaDiCaL on ubuntu or macOS
# (w023 K = -202 e00 also with Kissat):  pair -> the exponent offsets of those pieces.  No group
# runs them and the general suite skips them, so CI leaves them unproved (ruling s76 (c)).
DRAGON_UNPROVED_PIECES = {
    (23, -200): (4, 5, 6), (23, -201): (1, 2, 3, 4, 5), (23, -202): (0, 1, 2, 3, 4),
    (23, -203): (0, 1, 2), (23, -204): (0, 1, 2), (23, -205): (0,), (28, -183): (0, 1),
    (29, -173): (0, 1), (29, -174): (0, 1), (34, -151): (0, 1, 2, 3, 4, 5), (34, -152): (0, 1, 2),
    (34, -153): (0, 1, 3),
}
# One CI matrix holds at most 256 jobs:  core, long (generator and cached proofs), and the fixed-K
# pairs in four:  dragon-a (windows 000..033), dragon-b (034..067), dragon-c (068..097), dragon-d (098..127).
# The pieces of the split pairs run in two more:  dragon-e (offsets 0..7) and dragon-f (8..15).
MATRIX_JOBS = ("core", "long", "dragon-a", "dragon-b", "dragon-c", "dragon-d", "dragon-e",
               "dragon-f")


def dragon_window_exponents(window):
    """The first and last exponent of one 16-exponent Dragon scaling window."""
    first = -1076 + 16 * window
    return first, min(first + 15, 970)


def dragon_fixed_k_range(window):
    """The K values of one window:  the estimate at (2, first) through the estimate at (55, last)."""
    first, last = dragon_window_exponents(window)
    return range(((2 + first) * DRAGON_K_ESTIMATE) >> 32, (((55 + last) * DRAGON_K_ESTIMATE) >> 32) + 1)


def dragon_fixed_k_pairs():
    """Every (window, K) pair of the fixed-K proofs (windows 000..127), in (window, K) order."""
    return [(window, k) for window in range(DRAGON_FIXED_K_WINDOWS) for k in dragon_fixed_k_range(window)]


def dragon_fixed_k_name(window, k):
    """The catalog name part of one pair:  `000-k324` for K = -324, `063-p000` for K = 0."""
    return f"{window:03d}-{'k' if k < 0 else 'p'}{abs(k):03d}"


def dragon_fixed_k_harness(window, k):
    """The Kani harness of one pair:  module wNNN holds one module kNNN (K < 0) or pNNN (K >= 0)."""
    return f"{DRAGON}::dragon_scale_fixed_k::w{window:03d}::{'k' if k < 0 else 'p'}{abs(k):03d}::check_scale_shortest"


def dragon_fixed_k_piece_harness(window, k, offset):
    """The Kani harness of one piece of a split pair:  module eNN (NN = offset) inside the pair module."""
    pair = dragon_fixed_k_harness(window, k).removesuffix("::check_scale_shortest")
    return f"{pair}::e{offset:02d}::check_scale_shortest"


def dragon_unproved_harnesses():
    """The Kani harnesses of the unproved pieces (DRAGON_UNPROVED_PIECES), in pair and offset order."""
    return [dragon_fixed_k_piece_harness(window, k, offset)
            for (window, k), offsets in DRAGON_UNPROVED_PIECES.items() for offset in offsets]


def dragon_matrix_job(window):
    """Windows 000..033 run in the dragon-a matrix job, 034..067 in dragon-b, 068..097 in dragon-c
    and 098..127 in dragon-d."""
    return next(job for first, job in ((98, "dragon-d"), (68, "dragon-c"), (34, "dragon-b"), (0, "dragon-a"))
                if window >= first)


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
                # Neither cvc5 nor kissat proves a sliced Grisu shortest partition whole;
                # the slice groups below hold it instead.  f64-00-01 keeps only f64_01.
                harnesses = [f"{module}::f{width}_{group:02d}::{proof}" for group in range(first, last + 1)
                             if name != "grisu-shortest" or f"f{width}_{group:02d}" not in SLICED_SHORTEST]
                if harnesses:
                    add(f"{name}-{partition}", f"generator-f{width}", harnesses, timeout_minutes,
                        matrix_job="long")
        # Each slice holds eight exponents;  the eight slices of a partition form the partition.
        for partition in sorted(SLICED_SHORTEST) if name == "grisu-shortest" else []:
            for index in range(8):
                add(f"{name}-{partition.replace('_', '-')}-slice-{index}", f"generator-{partition[:3]}",
                    [f"{module}::{partition}::s{index}::{proof}"], timeout_minutes, matrix_job="long")
        add(f"{name}-fixed-exponent", "probe", [
            f"{module}::f64_exp_1023::{proof}"
        ], timeout_minutes)

    # Diagnostic value-range probes (branch g4-diag-s19 only):  each adds one assumption on the
    # scaled width to a hard shortest slice.  The covers show that each assumption admits an input.
    for probe, partition, index in [("p0", "f32_03", 4), ("p1", "f32_03", 4), ("p2", "f32_03", 4),
                                    ("p3", "f32_03", 4), ("p5", "f32_00", 0), ("p5", "f64_00", 0)]:
        add(f"grisu-shortest-{partition.replace('_', '-')}-slice-{index}-{probe}", f"generator-{partition[:3]}",
            [f"{GRISU}::probe_{probe}::{partition}_s{index}::check_format_shortest_opt"], 120,
            matrix_job="long")
    add("grisu-shortest-probe-covers", "probe", [
        f"{GRISU}::probe_covers::{name}"
        for name in ("p0_f32_03_s4", "p1_f32_03_s4", "p2_f32_03_s4", "p1_f32_00_s0", "p1_f64_00_s0")
    ], 30)

    # Ubuntu proved the shortest probe in 65 minutes;  macOS is about twice as slow.
    for mode in ("exact", "shortest"):
        add(f"grisu-{mode}-cached-power-39", "probe", [
            f"{GRISU}::f64_cached_power_39::check_format_{mode}_opt"
        ], 180 if mode == "shortest" else 60)

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
        ("dragon-shortest-scaling-partitioning", DRAGON, "check_dragon_scale_partitioning", "equivalence"),
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

    # Windows 000..127:  one fixed-K proof per (window, K) pair, and the estimate range the pairs cover.
    add("dragon-shortest-scaling-k-range", "equivalence", [f"{DRAGON}::check_dragon_scale_k_range"], 30)

    def add_fixed_k(pairs, timeout_minutes):
        first, last = pairs[0], pairs[-1]
        suffix = dragon_fixed_k_name(*first) + ("" if first == last else "-" + dragon_fixed_k_name(*last))
        add("dragon-shortest-scaling-fixed-k-" + suffix, "contract",
            [dragon_fixed_k_harness(window, k) for window, k in pairs], timeout_minutes,
            matrix_job=dragon_matrix_job(first[0]))

    def in_slow_band(window, k):
        return window in (0, 1) and k in DRAGON_SLOW_BAND

    # Routing (ruling s46):  the slow band runs window 000 at 180 minutes alone and window 001 at
    # 60 minutes in fours;  every other pair runs at 30 minutes in eights, contiguous in
    # (window, K) order within its matrix job.  The chunks form first;  then each slow pair
    # (ruling s54 (a)) leaves its chunk, so the other group names stay, and runs alone at
    # 180 minutes.  A split pair leaves its chunk the same way and runs one group per piece;
    # the pieces run in two matrix jobs of their own (256 jobs over both platforms):  offsets
    # 0..7 in dragon-e and 8..15 in dragon-f.  The unproved pieces (DRAGON_UNPROVED_PIECES) run no group.
    def add_fixed_k_chunks(pairs, batch_size, timeout_minutes):
        for first in range(0, len(pairs), batch_size):
            chunk = [pair for pair in pairs[first:first + batch_size]
                     if pair not in DRAGON_SLOW_PAIRS and pair not in DRAGON_SPLIT_PAIRS]
            if chunk:
                add_fixed_k(chunk, timeout_minutes)

    for window, batch_size, timeout_minutes in ((0, 1, 180), (1, 4, 60)):
        add_fixed_k_chunks([(window, k) for k in DRAGON_SLOW_BAND], batch_size, timeout_minutes)
    for job in ("dragon-a", "dragon-b", "dragon-c", "dragon-d"):
        add_fixed_k_chunks([(window, k) for window, k in dragon_fixed_k_pairs()
                            if dragon_matrix_job(window) == job and not in_slow_band(window, k)], 8, 30)
    for pair in DRAGON_SLOW_PAIRS:
        add_fixed_k([pair], 180)
    for (window, k), offsets in DRAGON_SPLIT_PAIRS.items():
        unproved = DRAGON_UNPROVED_PIECES.get((window, k), ())
        for offset in (offset for offset in offsets if offset not in unproved):
            add(f"dragon-shortest-scaling-fixed-k-{dragon_fixed_k_name(window, k)}-e{offset:02d}", "contract",
                [dragon_fixed_k_piece_harness(window, k, offset)], 180, matrix_job="dragon-" + "ef"[offset >= 8])

    # The index 51 proof (group 29) does not finish on the whole domain, so grisu.rs proves
    # it in two pieces that split on the top bit of v and together cover every input.
    for first in range(0, 80, 10):
        last = first + 9
        harnesses = [f"{GRISU}::check_multiply_shortest_{group:02d}{piece}"
                     for group in range(first, last + 1)
                     for piece in (("_v0", "_v1") if group == 29 else ("",))]
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
    # The unproved pieces (DRAGON_UNPROVED_PIECES) run in no group and not in the general suite.
    dedicated = {harness for group in proof_groups() for harness in group["harnesses"]}.union(
        dragon_unproved_harnesses())
    missing = dedicated.difference(listed)
    if missing:
        raise ValueError("Dedicated flt2dec harnesses missing from kani list: " + ", ".join(sorted(missing)))
    # Keep unrecognized harnesses, including future flt2dec proofs, in the general suite.
    # Preserve the original list order and duplicates outside the dedicated catalog.
    return [harness for harness in listed if harness not in dedicated]


def proof_matrix(selected_groups=None, pointer_width=None, platform="both", grisu_probe="none",
                 matrix_job=None):
    groups = proof_groups(pointer_width)
    if grisu_probe != "none" and grisu_probe not in GRISU_PROBES:
        raise ValueError("Unknown Grisu probe: " + str(grisu_probe))
    if matrix_job not in (None, *MATRIX_JOBS):
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
        # `matrix-job:dragon-a` selects every catalog group of that matrix job.
        jobs = {name[len("matrix-job:"):] for name in selected if name.startswith("matrix-job:")}
        if not jobs <= set(MATRIX_JOBS):
            raise ValueError("Unknown matrix jobs: " + ", ".join(sorted(jobs - set(MATRIX_JOBS))))
        selected = {name for name in selected if not name.startswith("matrix-job:")} | {
            group["name"] for group in groups if group["matrix_job"] in jobs}
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
                group.update(name=f"probe-{grisu_probe}-" + group["catalog_name"],
                             probe_property=GRISU_PROBES[grisu_probe], timeout_minutes=3)
    # A manual selection splits between the matrix jobs;  any part can be empty.
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
    parser.add_argument("--matrix-grisu-probe", choices=["none", *GRISU_PROBES], default="none",
                        help="Diagnose one loop property in selected manual Grisu groups")
    parser.add_argument("--matrix-job", choices=list(MATRIX_JOBS),
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
