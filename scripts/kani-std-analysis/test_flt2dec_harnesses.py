from pathlib import Path
import re
import unittest

from flt2dec_harnesses import (
    OPERATING_SYSTEMS, group_harnesses, proof_groups, proof_matrix, remaining_harnesses,
)


class Flt2decHarnessesTests(unittest.TestCase):
    def test_default_matrix_keeps_every_group_on_both_platforms(self):
        for width in (16, 32, 64):
            with self.subTest(pointer_width=width):
                matrix = proof_matrix(pointer_width=width)
                self.assertEqual(matrix["os"], OPERATING_SYSTEMS)
                self.assertEqual(matrix["group"], proof_groups(width))

    def test_manual_matrix_keeps_group_contents_and_distinct_check_names(self):
        names = ["grisu-shortest-f32-00-01", "dragon-exact-loop-frame",
                 "grisu-multiplication-contract-20-29", "cached-multiplication-equivalence-000-003"]
        matrix = proof_matrix(names)
        self.assertEqual(matrix["os"], OPERATING_SYSTEMS)
        self.assertEqual({group["catalog_name"] for group in matrix["group"]}, set(names))
        original = {group["name"]: group for group in proof_groups()}
        for group in matrix["group"]:
            self.assertEqual(group["name"], "manual-" + group["catalog_name"])
            for field in ("harnesses", "kind", "backend", "timeout_minutes", "harness_backends"):
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
        name = "grisu-shortest-f32-00-01"
        original = next(group for group in self.groups if group["name"] == name)
        for probe, phase in (("entry", "base"), ("step", "step")):
            matrix = proof_matrix([name], grisu_probe=probe)
            group, = matrix["group"]
            with self.subTest(probe=probe):
                self.assertEqual(group["name"], f"probe-{probe}-{name}")
                self.assertEqual(group["catalog_name"], name)
                self.assertEqual(group["harnesses"], original["harnesses"])
                self.assertEqual(group["timeout_minutes"], 3)
                self.assertEqual(group["probe_property"],
                                 "num::imp::flt2dec::strategy::grisu::generate_shortest."
                                 f"loop_invariant_{phase}.1")
                self.assertEqual(matrix["os"], OPERATING_SYSTEMS)
        self.assertTrue(all("probe_property" not in group for group in proof_matrix()["group"]))

    def test_loop_probes_reject_automatic_and_unrelated_groups(self):
        for probe in ("entry", "step", "unknown"):
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
        self.assertEqual(len(self.groups), 127)
        self.assertEqual(len({group["name"] for group in self.groups}), 127)
        self.assertEqual(len(self.dedicated), 754)
        self.assertEqual(len(set(self.dedicated)), 754)
        self.assertLessEqual(len(self.groups) * len(OPERATING_SYSTEMS), 256)
        for group in self.groups:
            minutes = group["timeout_minutes"]
            with self.subTest(group=group["name"]):
                self.assertTrue(group["harnesses"])
                self.assertIn(minutes, (7, 30, 60, 120))
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
        # Narrower catalogs keep their routing tests but exceed one matrix.
        self.assertLessEqual(len(proof_groups(pointer_width=64)) * len(OPERATING_SYSTEMS), 256)

    def test_all_float_partitions_and_equivalence_cases_remain(self):
        self.assertIn(
            "num::imp::flt2dec::strategy::dragon::dragon_verify::check_exact_digit_loop_frame",
            self.dedicated,
        )
        generators = [group for group in self.groups if group["kind"].startswith("generator-")]
        self.assertEqual(sum(len(group["harnesses"]) for group in generators), 144)
        for family in ("dragon-exact", "dragon-shortest", "grisu-exact", "grisu-shortest"):
            targets = [harness for group in generators if group["name"].startswith(family + "-")
                       for harness in group["harnesses"]]
            partitions = {harness.split("::")[-2] for harness in targets}
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
        expected = {f"{prefix}check_multiply_shortest_{index:02d}" for index in range(80)}
        expected.add(f"{prefix}check_decimal_termination")
        expected.add(f"{prefix}check_advance_fraction_threshold")
        expected.update(f"{prefix}check_fractional_encoding_{power:02d}" for power in range(16))
        expected.update(f"{prefix}f{width}_{index:02d}::check_format_shortest_opt"
                        for width, count in ((32, 4), (64, 2)) for index in range(count))
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

    def test_native_grisu_shortest_partition_leaves_its_cvc5_group(self):
        group = next(group for group in proof_groups(pointer_width=64)
                     if group["name"] == "grisu-shortest-f64-00-01")
        self.assertEqual(group["backend"], "cvc5")
        self.assertEqual([harness.rsplit("::", 2)[1] for harness in group_harnesses(group, "native")],
                         ["f64_01"])
        self.assertEqual([harness.rsplit("::", 2)[1] for harness in group_harnesses(group, "cvc5")],
                         ["f64_00"])

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
        for macro, prefix, expected_index in (
            ("check_scale_shortest_partition", "check_scale_shortest", lambda group: group),
            ("verify_multiply_shortest", "check_multiply_shortest", lambda group: 80 - group),
        ):
            pattern = rf"{macro}!\(\s*({prefix}_(\d+))\s*,(?:\s*scaling_cache_index_\d+\s*,)?\s*(\d+)\s*\)"
            declarations = re.findall(pattern, source)
            with self.subTest(macro=macro):
                self.assertEqual(len(declarations), 80)
                self.assertEqual({(int(group), int(index)) for _, group, index in declarations},
                                 {(group, expected_index(group)) for group in range(80)})
                declared = {name for name, _, _ in declarations}
                routed = {name.rsplit("::", 1)[1] for name in self.dedicated
                          if re.fullmatch(prefix + r"_\d+", name.rsplit("::", 1)[1])}
                self.assertEqual(declared, routed)

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
