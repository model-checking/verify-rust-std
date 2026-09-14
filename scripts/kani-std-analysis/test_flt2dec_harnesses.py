import unittest

from flt2dec_harnesses import OPERATING_SYSTEMS, proof_groups, remaining_harnesses


class Flt2decHarnessesTests(unittest.TestCase):
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
        self.assertEqual(len(self.groups), 77)
        self.assertEqual(len({group["name"] for group in self.groups}), 77)
        self.assertEqual(len(self.dedicated), 275)
        self.assertEqual(len(set(self.dedicated)), 275)
        self.assertLessEqual(len(self.groups) * len(OPERATING_SYSTEMS), 256)
        for group in self.groups:
            minutes = group["timeout_minutes"]
            with self.subTest(group=group["name"]):
                self.assertTrue(group["harnesses"])
                self.assertIn(minutes, (30, 60, 120))
                self.assertLessEqual(minutes * len(group["harnesses"]), 240)

    def test_all_float_partitions_and_equivalence_cases_remain(self):
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
        self.assertEqual({int(harness.rsplit("_", 1)[1]) for harness in multiplication}, set(range(40)))
        division = [harness for group in self.groups
                    if group["name"].startswith("decimal-division-")
                    for harness in group["harnesses"]]
        self.assertEqual({int(harness.rsplit("_", 1)[1]) for harness in division}, set(range(10)))

    def test_only_exact_catalog_names_are_removed(self):
        retained = ["num::flt2dec::check_wrapper", "num::flt2dec::check_future_proof",
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
