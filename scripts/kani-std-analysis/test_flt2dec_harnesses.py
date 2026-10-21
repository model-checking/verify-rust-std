from pathlib import Path
import re
import unittest

from flt2dec_harnesses import (
    DRAGON, DRAGON_SLOW_BAND, DRAGON_SLOW_PAIRS, DRAGON_SPLIT_PAIRS, MATRIX_JOBS, OPERATING_SYSTEMS,
    dragon_fixed_k_harness, dragon_fixed_k_piece_harness,
    dragon_fixed_k_pairs, group_harnesses, proof_groups, proof_matrix, remaining_harnesses,
)


class Flt2decHarnessesTests(unittest.TestCase):
    def test_default_matrix_keeps_every_group_on_both_platforms(self):
        for width in (16, 32, 64):
            with self.subTest(pointer_width=width):
                matrix = proof_matrix(pointer_width=width)
                self.assertEqual(matrix["os"], OPERATING_SYSTEMS)
                self.assertEqual(matrix["group"], proof_groups(width))

    def test_manual_matrix_keeps_group_contents_and_distinct_check_names(self):
        names = ["grisu-shortest-f64-02-03", "dragon-exact-loop-frame",
                 "grisu-multiplication-contract-20-29", "cached-multiplication-equivalence-000-003"]
        matrix = proof_matrix(names)
        self.assertEqual(matrix["os"], OPERATING_SYSTEMS)
        self.assertEqual({group["catalog_name"] for group in matrix["group"]}, set(names))
        original = {group["name"]: group for group in proof_groups()}
        for group in matrix["group"]:
            self.assertEqual(group["name"], "manual-" + group["catalog_name"])
            for field in ("harnesses", "kind", "backend", "timeout_minutes", "harness_backends", "matrix_job"):
                self.assertEqual(group.get(field), original[group["catalog_name"]].get(field))

    def test_invalid_manual_matrix_selection_fails(self):
        for selection in ([], {}, "dragon-exact-loop-frame", [0], ["unknown"],
                          ["dragon-exact-loop-frame", "dragon-exact-loop-frame"]):
            with self.subTest(selection=selection), self.assertRaises(ValueError):
                proof_matrix(selection)

    def test_platform_selection_requires_explicit_manual_groups(self):
        names = ["dragon-exact-loop-frame"]
        for platform in OPERATING_SYSTEMS:
            with self.subTest(platform=platform):
                matrix = proof_matrix(names, platform=platform)
                self.assertEqual(matrix["os"], [platform])
                self.assertEqual(matrix["group"], proof_matrix(names)["group"])
                with self.assertRaises(ValueError):
                    proof_matrix(platform=platform)
        with self.assertRaises(ValueError):
            proof_matrix(names, platform="windows-latest")

    def test_loop_probes_have_distinct_names_and_keep_the_selected_harnesses(self):
        name = "grisu-shortest-f64-02-03"
        original = next(group for group in self.groups if group["name"] == name)
        for probe, function, phase in (("entry", "generate_shortest", "base"),
                                       ("step", "generate_shortest", "step"),
                                       ("integral-step", "generate_integral_digits", "step")):
            matrix = proof_matrix([name], grisu_probe=probe)
            group, = matrix["group"]
            with self.subTest(probe=probe):
                self.assertEqual(group["name"], f"probe-{probe}-{name}")
                self.assertEqual(group["catalog_name"], name)
                self.assertEqual(group["harnesses"], original["harnesses"])
                self.assertEqual(group["timeout_minutes"], 3)
                self.assertEqual(group["probe_property"],
                                 f"num::imp::flt2dec::strategy::grisu::{function}."
                                 f"loop_invariant_{phase}.1")
                self.assertEqual(matrix["os"], OPERATING_SYSTEMS)
        self.assertTrue(all("probe_property" not in group for group in proof_matrix()["group"]))

    def test_loop_probes_reject_automatic_and_unrelated_groups(self):
        for probe in ("entry", "step", "integral-step", "unknown"):
            with self.subTest(probe=probe), self.assertRaises(ValueError):
                proof_matrix(grisu_probe=probe)
        for name in ("dragon-exact-loop-frame", "grisu-shortest-scaling-contract-00-03"):
            with self.subTest(group=name), self.assertRaises(ValueError):
                proof_matrix([name], grisu_probe="entry")

    def setUp(self):
        self.groups = proof_groups()
        self.dedicated = [harness for group in self.groups for harness in group["harnesses"]]
        self.inventory = {
            "file-version": "0.1",
            "standard-harnesses": {"generators": self.dedicated[:144]},
            "contract-harnesses": {"other": self.dedicated[144:]},
        }

    def test_complete_disjoint_batches_on_both_platforms(self):
        self.assertEqual(OPERATING_SYSTEMS, ["ubuntu-latest", "macos-latest"])
        # The diagnostic probes (branch g4-diag-s19 only) add groups, so the counts skip them.
        real = [group for group in self.groups if "::probe_" not in group["harnesses"][0]]
        self.assertEqual(len(real), 596)
        self.assertEqual(len({group["name"] for group in self.groups}), len(self.groups))
        self.assertEqual(sum(len(group["harnesses"]) for group in real), 3585)
        self.assertEqual(len(set(self.dedicated)), len(self.dedicated))
        for part in MATRIX_JOBS:
            parts = [group for group in proof_matrix(matrix_job=part)["group"]
                     if "::probe_" not in group["harnesses"][0]]
            self.assertLessEqual(len(parts) * len(OPERATING_SYSTEMS), 256)
        for group in self.groups:
            minutes = group["timeout_minutes"]
            with self.subTest(group=group["name"]):
                self.assertTrue(group["harnesses"])
                self.assertIn(minutes, (7, 30, 60, 120, 180))
                self.assertLessEqual(minutes * len(group["harnesses"]), 240)

    def test_shift_models_cover_all_safe_whole_limb_offsets(self):
        for width, limbs in ((16, 40), (32, 40), (64, 20)):
            groups = proof_groups(pointer_width=width)
            cases = [harness for group in groups
                     if group["name"].startswith("bigint-shift-equivalence-")
                     for harness in group["harnesses"]]
            positions = [(int(name.split("::")[-2].rsplit("_", 1)[1]),
                          int(name.rsplit("_", 1)[1])) for name in cases]
            routed = {(size, total - size) for total, size in positions}
            expected = {(size, digits) for size in range(limbs + 1)
                        for digits in range(limbs) if size + digits <= limbs}
            with self.subTest(pointer_width=width):
                self.assertEqual(routed, expected)
                self.assertEqual(len(cases), len(expected))

    def test_ci_matrix_fits_the_job_limit(self):
        # The matrix job runs on a 64-bit host, so only that catalog is expanded.
        # Each flt2dec matrix job holds at most 256 jobs.
        for part in MATRIX_JOBS:
            with self.subTest(matrix_job=part):
                matrix = proof_matrix(pointer_width=64, matrix_job=part)
                self.assertTrue(matrix["group"])
                self.assertLessEqual(len(matrix["group"]) * len(matrix["os"]), 256)

    def test_matrix_jobs_split_every_catalog(self):
        for width in (16, 32, 64):
            groups = proof_groups(width)
            parts = {part: proof_matrix(pointer_width=width, matrix_job=part)["group"]
                     for part in MATRIX_JOBS}
            with self.subTest(pointer_width=width):
                self.assertTrue(all(group["matrix_job"] in parts for group in groups))
                self.assertTrue(all(group["matrix_job"] == part
                                    for part, selected in parts.items() for group in selected))
                self.assertEqual(sorted(group["name"] for selected in parts.values() for group in selected),
                                 sorted(group["name"] for group in groups))

    def test_generator_and_cached_groups_run_in_the_long_job(self):
        for group in self.groups:
            in_long_job = (group["kind"].startswith("generator-")
                           or group["name"].startswith("cached-multiplication-equivalence-"))
            in_dragon_job = group["name"].startswith(("dragon-shortest-scaling-fixed-k-",
                                                      "dragon-shortest-scaling-contract-"))
            with self.subTest(group=group["name"]):
                if in_dragon_job:
                    self.assertIn(group["matrix_job"], ("dragon-a", "dragon-b", "dragon-c", "dragon-d"))
                else:
                    self.assertEqual(group["matrix_job"], "long" if in_long_job else "core")

    def test_manual_selection_splits_between_matrix_jobs(self):
        names = ["dragon-exact-loop-frame", "grisu-exact-f32"]
        for part, name in (("core", "dragon-exact-loop-frame"), ("long", "grisu-exact-f32")):
            with self.subTest(matrix_job=part):
                matrix = proof_matrix(names, matrix_job=part)
                self.assertEqual([group["catalog_name"] for group in matrix["group"]], [name])
        self.assertEqual(proof_matrix(["dragon-exact-loop-frame"], matrix_job="long")["group"], [])
        for part in ("all", ""):
            with self.subTest(matrix_job=part), self.assertRaises(ValueError):
                proof_matrix(matrix_job=part)

    def test_matrix_job_selection_expands_to_every_group_of_the_job(self):
        matrix = proof_matrix(["matrix-job:dragon-a", "matrix-job:dragon-b"])
        self.assertEqual(matrix["os"], OPERATING_SYSTEMS)
        self.assertEqual(sorted(group["catalog_name"] for group in matrix["group"]),
                         sorted(group["name"] for group in self.groups
                                if group["matrix_job"] in ("dragon-a", "dragon-b")))
        self.assertEqual(proof_matrix(["matrix-job:dragon-a"], matrix_job="core")["group"], [])
        self.assertEqual(len(proof_matrix(["matrix-job:dragon-a"], matrix_job="dragon-a")["group"]),
                         len(proof_matrix(matrix_job="dragon-a")["group"]))
        with self.assertRaises(ValueError):
            proof_matrix(["matrix-job:unknown"])

    def test_dragon_fixed_k_groups_cover_every_pair_once_with_the_band_routing(self):
        pairs = dragon_fixed_k_pairs()
        self.assertEqual(len(pairs), 2748)
        self.assertEqual((pairs[0], pairs[21], pairs[22], pairs[-1]),
                         ((0, -324), (0, -303), (1, -319), (127, 308)))
        self.assertEqual(sum(1 for _, k in pairs if k >= 0), 1342)
        groups = [group for group in self.groups
                  if group["name"].startswith("dragon-shortest-scaling-fixed-k-")]
        routed = [(group, int(window), (-1 if sign == "k" else 1) * int(k), piece)
                  for group in groups for harness in group["harnesses"]
                  for window, sign, k, piece in re.findall(
                      r"::w(\d{3})::([kp])(\d{3})(?:::e(\d{2}))?::check_scale_shortest$", harness)]
        self.assertEqual(len(routed), sum(len(group["harnesses"]) for group in groups))
        # A split pair routes once per piece:  its first piece stands for the pair.
        self.assertEqual(sorted((window, k) for _, window, k, piece in routed if piece in ("", "00")),
                         pairs)
        self.assertEqual([harness for group in groups for harness in group["harnesses"]
                          if harness == dragon_fixed_k_harness(0, -324)],
                         [f"{DRAGON}::dragon_scale_fixed_k::w000::k324::check_scale_shortest"])
        for group, window, k, piece in routed:
            in_band = window in (0, 1) and k in DRAGON_SLOW_BAND
            slow = (window, k) in DRAGON_SLOW_PAIRS or (window, k) in DRAGON_SPLIT_PAIRS
            minutes, batch_size = ((180, 1) if slow or (in_band and window == 0)
                                   else (60, 4) if in_band else (30, 8))
            with self.subTest(group=group["name"], window=window, k=k):
                self.assertEqual(group["matrix_job"], "dragon-" + "cd"[int(piece) >= 8] if piece else
                                 "dragon-" + "abcd"[(window >= 34) + (window >= 68) + (window >= 98)])
                self.assertEqual(group["timeout_minutes"], minutes)
                self.assertLessEqual(len(group["harnesses"]), batch_size)
        self.assertEqual(len(DRAGON_SLOW_PAIRS), 16)
        self.assertEqual(sum(1 for group in groups if group["timeout_minutes"] == 180), 84)
        self.assertEqual(sum(1 for group in groups if group["timeout_minutes"] == 60), 3)
        self.assertEqual(tuple(len(proof_matrix(matrix_job=job)["group"])
                               for job in ("dragon-a", "dragon-b", "dragon-c", "dragon-d")), (108, 100, 111, 111))

    def test_all_float_partitions_and_equivalence_cases_remain(self):
        self.assertIn(
            "num::imp::flt2dec::strategy::dragon::dragon_verify::check_exact_digit_loop_frame",
            self.dedicated,
        )
        # The diagnostic probes (branch g4-diag-s19 only) repeat slices, so they stay out.
        generators = [group for group in self.groups if group["kind"].startswith("generator-")
                      and "::probe_" not in group["harnesses"][0]]
        self.assertEqual(sum(len(group["harnesses"]) for group in generators), 179)
        for family in ("dragon-exact", "dragon-shortest", "grisu-exact", "grisu-shortest"):
            targets = [harness for group in generators if group["name"].startswith(family + "-")
                       for harness in group["harnesses"]]
            # A slice harness adds an `sN` module below its partition module.
            partitions = {next(part for part in harness.split("::") if part.startswith(("f32_", "f64_")))
                          for harness in targets}
            self.assertEqual(partitions, {f"f32_{i:02d}" for i in range(4)} |
                             {f"f64_{i:02d}" for i in range(32)})
        cases = [harness for group in self.groups if group["name"].startswith("estimator-")
                 for harness in group["harnesses"]]
        self.assertEqual({int(harness.rsplit("_", 1)[1]) for harness in cases}, set(range(65)))
        multiplication = [harness for group in self.groups
                          if group["name"].startswith("small-multiplication-")
                          for harness in group["harnesses"]]
        self.assertEqual({int(harness.rsplit("_", 1)[1]) for harness in multiplication}, set(range(20)))

        for width, limb_count in ((16, 40), (32, 40), (64, 20)):
            with self.subTest(pointer_width=width):
                cases = [harness for group in proof_groups(width)
                         if group["name"].startswith("small-multiplication-")
                         for harness in group["harnesses"]]
                self.assertEqual({int(harness.rsplit("_", 1)[1]) for harness in cases},
                                 set(range(limb_count)))
        division = [harness for group in self.groups
                    if group["name"].startswith("decimal-division-")
                    for harness in group["harnesses"]]
        self.assertEqual({int(harness.rsplit("_", 1)[1]) for harness in division}, set(range(10)))
        scaling = [harness for group in self.groups
                   if group["name"].startswith("grisu-shortest-scaling-contract-")
                   for harness in group["harnesses"]]
        self.assertEqual({int(harness.rsplit("_", 1)[1]) for harness in scaling}, set(range(80)))

    def test_arithmetic_backend_covers_every_cached_power(self):
        arithmetic = [harness for group in self.groups
                      for harness in group_harnesses(group, "cvc5")]
        prefix = "num::imp::flt2dec::strategy::grisu::grisu_verify::"
        expected = {f"{prefix}check_multiply_shortest_{index:02d}"
                    for index in range(80) if index != 29}
        expected.update(f"{prefix}check_multiply_shortest_29_{piece}" for piece in ("v0", "v1"))
        expected.add(f"{prefix}check_decimal_termination")
        expected.add(f"{prefix}check_advance_fraction_threshold")
        expected.update(f"{prefix}check_fractional_encoding_{power:02d}" for power in range(16))
        self.assertEqual(set(arithmetic), expected)
        self.assertEqual(len(arithmetic), len(expected))
        self.assertIn(f"{prefix}check_rounded_multiply", self.dedicated)
        self.assertIn(f"{prefix}check_normalized_multiply", self.dedicated)

    def test_backend_split_keeps_every_harness_exactly_once(self):
        for width in (16, 32, 64):
            for group in proof_groups(width):
                with self.subTest(pointer_width=width, group=group["name"]):
                    native = group_harnesses(group, "native")
                    arithmetic = group_harnesses(group, "cvc5")
                    self.assertEqual(group_harnesses(group), group["harnesses"])
                    self.assertCountEqual(native + arithmetic, group["harnesses"])
                    self.assertTrue(set(native).isdisjoint(arithmetic))
                    self.assertTrue(set(group.get("harness_backends", {})) <= set(group["harnesses"]))
                    self.assertTrue(all(harness in native for harness in group["harnesses"]
                                        if "::cached_mul_pow5_" in harness))
        with self.assertRaises(ValueError):
            group_harnesses(self.groups[0], "unknown")

    def test_cached_big_multiplication_covers_every_native_coefficient(self):
        root = Path(__file__).resolve().parents[2]
        source = (root / "library/core/src/num/imp/flt2dec/strategy/dragon.rs").read_text()
        start = source.index("pub fn mul_pow10(")
        body = source[start:source.index("\n}\n", start)]
        called = re.findall(r"\.mul_digits\(&POW5TO(\d+)\)", body)
        self.assertEqual(len(called), len(re.findall(r"\.mul_digits\(", body)))
        declared = re.findall(r"cached_mul_pow5_(\d+)\s*=>\s*POW5TO(\d+)", source)
        self.assertTrue(all(case == coefficient for case, coefficient in declared))
        self.assertEqual({case for case, _ in declared}, set(called))
        routed = {re.search(r"::cached_mul_pow5_(\d+)::", harness).group(1)
                  for harness in self.dedicated if "::cached_mul_pow5_" in harness}
        self.assertEqual(routed, set(called))

    def test_cached_big_multiplication_covers_every_accepted_size(self):
        for width in (16, 32, 64):
            digit_bits = 64 if width == 64 else 32
            capacity = 1280 // digit_bits
            groups = proof_groups(pointer_width=width)
            cases = [harness for group in groups for harness in group["harnesses"]
                     if "::cached_mul_pow5_" in harness]
            routed = {tuple(map(int, re.search(r"::cached_mul_pow5_(\d+)::size_(\d+)$",
                                               harness).groups())) for harness in cases}
            expected = {(power, size) for power in (16, 32, 64, 128, 256)
                        for size in range(capacity + 1 -
                                          ((5 ** power).bit_length() + digit_bits - 1) // digit_bits)}
            with self.subTest(pointer_width=width):
                self.assertEqual(routed, expected)
                self.assertEqual(len(cases), len(expected))
                for group in groups:
                    self.assertLessEqual(group["timeout_minutes"] * len(group["harnesses"]), 240)

    def test_sliced_grisu_shortest_partitions_cover_every_exponent(self):
        prefix = "num::imp::flt2dec::strategy::grisu::grisu_verify::"
        partitions = ("f32_00", "f32_01", "f32_02", "f32_03", "f64_00")
        slices = [group for group in self.groups
                  if group["name"].startswith("grisu-shortest-") and "-slice-" in group["name"]
                  and "::probe_" not in group["harnesses"][0]]
        self.assertEqual(sorted(harness for group in slices for harness in group["harnesses"]),
                         sorted(f"{prefix}{partition}::s{index}::check_format_shortest_opt"
                                for partition in partitions for index in range(8)))
        for group in slices:
            with self.subTest(group=group["name"]):
                self.assertEqual(len(group["harnesses"]), 1)
                self.assertEqual((group["backend"], group["matrix_job"], group["timeout_minutes"]),
                                 ("native", "long", 120))
                self.assertNotIn("harness_backends", group)
        # The slices replace the whole shortest harness;  the exact harness stays whole.
        for partition in partitions:
            with self.subTest(partition=partition):
                self.assertNotIn(f"{prefix}{partition}::check_format_shortest_opt", self.dedicated)
                self.assertIn(f"{prefix}{partition}::check_format_exact_opt", self.dedicated)
        group = next(group for group in self.groups if group["name"] == "grisu-shortest-f64-00-01")
        self.assertEqual(group["harnesses"], [f"{prefix}f64_01::check_format_shortest_opt"])
        self.assertEqual(group["backend"], "native")
        self.assertNotIn("harness_backends", group)

    def test_cached_big_multiplication_uses_dedicated_native_groups(self):
        for width in (16, 32, 64):
            for group in proof_groups(pointer_width=width):
                cached = [harness for harness in group["harnesses"] if "::cached_mul_pow5_" in harness]
                dedicated = group["name"].startswith("cached-multiplication-equivalence-")
                with self.subTest(pointer_width=width, group=group["name"]):
                    self.assertEqual(cached, group["harnesses"] if dedicated else [])
                    if dedicated:
                        self.assertNotIn("harness_backends", group)
                        self.assertEqual(
                            (group["kind"], group["backend"], group["timeout_minutes"]),
                            ("equivalence", "native", 60))
                        self.assertLessEqual(len(group["harnesses"]), 4)
        names = [group["name"] for group in proof_groups(pointer_width=64)
                 if group["name"].startswith("cached-multiplication-equivalence-")]
        self.assertEqual(len(names), 21)
        self.assertEqual(names[0], "cached-multiplication-equivalence-000-003")
        self.assertEqual(names[-1], "cached-multiplication-equivalence-080-083")

    def test_cached_power_catalog_matches_rust_declarations(self):
        root = Path(__file__).resolve().parents[2]
        source = (root / "library/core/src/num/imp/flt2dec/strategy/grisu.rs").read_text()
        for macro, prefix, expected_index, pieces in (
            ("check_scale_shortest_partition", "check_scale_shortest", lambda group: group, {}),
            ("verify_multiply_shortest", "check_multiply_shortest", lambda group: 80 - group,
             {29: ("v0", "v1")}),
        ):
            pattern = (rf"{macro}!\(\s*({prefix}_(\d+)(?:_(v\d))?)\s*,"
                       rf"(?:\s*scaling_cache_index_\d+\s*,)?\s*(\d+)\s*[,)]")
            declarations = re.findall(pattern, source)
            expected = {(group, piece, expected_index(group)) for group in range(80)
                        for piece in pieces.get(group, ("",))}
            with self.subTest(macro=macro):
                self.assertEqual(len(declarations), len(expected))
                self.assertEqual({(int(group), piece, int(index))
                                  for _, group, piece, index in declarations}, expected)
                declared = {name for name, _, _, _ in declarations}
                routed = {name.rsplit("::", 1)[1] for name in self.dedicated
                          if re.fullmatch(prefix + r"_\d+(?:_v\d)?", name.rsplit("::", 1)[1])}
                self.assertEqual(declared, routed)
        # The two pieces of the index 51 proof must cover every u64 value of v.
        split = re.findall(r"verify_multiply_shortest!\(\s*check_multiply_shortest_29_(v\d)\s*,"
                           r"\s*51\s*,\s*([^,]+?)\s*,\s*([^,)]+?)\s*[,)]", source)
        self.assertEqual(split, [("v0", "0", "1 << 63"), ("v1", "1 << 63", "1 << 64")])

    def test_dragon_split_pairs_run_one_group_per_piece(self):
        self.assertEqual(len(DRAGON_SPLIT_PAIRS), 15)
        self.assertEqual(set(DRAGON_SPLIT_PAIRS) & set(DRAGON_SLOW_PAIRS), set())
        names = {group["name"]: group for group in self.groups}
        harnesses = [harness for group in self.groups for harness in group["harnesses"]]
        for (window, k), offsets in DRAGON_SPLIT_PAIRS.items():
            plain = f"dragon-shortest-scaling-fixed-k-{window:03d}-{'k' if k < 0 else 'p'}{abs(k):03d}"
            with self.subTest(window=window, k=k):
                self.assertEqual(offsets, (0, 4, 8, 12))
                self.assertNotIn(plain, names)
                self.assertNotIn(dragon_fixed_k_harness(window, k), harnesses)
                for offset in offsets:
                    group = names[f"{plain}-e{offset:02d}"]
                    self.assertEqual(group["harnesses"], [dragon_fixed_k_piece_harness(window, k, offset)])
                    self.assertEqual(group["timeout_minutes"], 180)
                    self.assertEqual(group["matrix_job"], "dragon-" + "cd"[offset >= 8])
        self.assertEqual(dragon_fixed_k_piece_harness(0, -317, 0),
                         f"{DRAGON}::dragon_scale_fixed_k::w000::k317::e00::check_scale_shortest")

    def test_only_exact_catalog_names_are_removed(self):
        retained = ["num::imp::flt2dec::check_wrapper", "num::imp::flt2dec::check_future_proof",
                    self.dedicated[0] + "_extra", "unrelated::proof", "unrelated::proof"]
        self.inventory["standard-harnesses"]["retained"] = retained[:3]
        self.inventory["contract-harnesses"]["retained"] = retained[3:]
        self.assertEqual(remaining_harnesses(self.inventory), retained)

    def test_missing_dedicated_harness_fails(self):
        self.inventory["standard-harnesses"]["generators"].pop()
        with self.assertRaisesRegex(ValueError, "Dedicated flt2dec harnesses missing"):
            remaining_harnesses(self.inventory)

    def test_unknown_inventory_version_fails(self):
        self.inventory["file-version"] = "0.2"
        with self.assertRaisesRegex(ValueError, "file-version 0.1"):
            remaining_harnesses(self.inventory)

    def test_empty_remaining_inventory(self):
        self.assertEqual(remaining_harnesses(self.inventory), [])


if __name__ == "__main__":
    unittest.main()
