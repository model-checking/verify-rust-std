#!/usr/bin/env python3
"""Exercise stale-source and omitted-contract failures without a compiler."""

import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest


PACKAGE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True
SPEC = importlib.util.spec_from_file_location("check_sources", PACKAGE / "check_sources.py")
CHECKER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECKER)


class SourceGateTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory(prefix="vrs602-source-check-")
        self.addCleanup(self.temporary.cleanup)
        self.repo = Path(self.temporary.name)
        self.package = self.repo / "verifast-proofs/core/iter/adapters"
        self.manifest = json.loads(CHECKER.read_file(PACKAGE / "source-map.json"))
        paths = ["source-map.json", "original/lib.rs", "verified/lib.rs"]
        for entry in self.manifest["sources"]:
            paths.extend((entry["snapshot"], entry["projection"],
                          "verified/" + Path(entry["projection"]).name))
            upstream = self.repo / entry["upstream"]
            upstream.parent.mkdir(parents=True, exist_ok=True)
            upstream.write_bytes(CHECKER.read_file(PACKAGE / entry["snapshot"]))
        for relative in paths:
            destination = self.package / relative
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(CHECKER.read_file(PACKAGE / relative))

    def check(self):
        return CHECKER.check(package=self.package, repo=self.repo)

    def alter(self, relative, before, after):
        path = self.package / relative
        text = path.read_text()
        self.assertIn(before, text)
        path.write_text(text.replace(before, after, 1))

    def test_current_inputs_and_array_return_signatures(self):
        self.assertEqual(self.check(), 2)

    def test_upstream_drift(self):
        path = self.repo / self.manifest["sources"][0]["upstream"]
        path.write_bytes(path.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "std source differs"):
            self.check()

    def test_snapshot_drift(self):
        path = self.package / self.manifest["sources"][0]["snapshot"]
        path.write_bytes(path.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "snapshot hash changed"):
            self.check()

    def test_projection_drift(self):
        self.alter("original/step_by.rs", "self.step_minus_one, 1", "self.step_minus_one, 2")
        with self.assertRaisesRegex(ValueError, "original projection differs"):
            self.check()

    def test_ordinary_comment_does_not_count_as_contract(self):
        self.alter("verified/step_by.rs", "//@ req", "// req")
        with self.assertRaisesRegex(ValueError, "missing req for original_step"):
            self.check()

    def test_missing_unwind_clause(self):
        self.alter("verified/step_by.rs", "//@ on_unwind_ens false;", "")
        with self.assertRaisesRegex(ValueError, "missing on_unwind_ens"):
            self.check()

    def test_suppressed_method(self):
        self.alter("verified/step_by.rs", "    #[inline]", "    #[cfg(any())]\n    #[inline]")
        with self.assertRaisesRegex(ValueError, "verification bypass"):
            self.check()

    def test_assumption(self):
        self.alter("verified/step_by.rs", "//@ on_unwind_ens false;",
                   "//@ on_unwind_ens false;\n        //@ assume(false);")
        with self.assertRaisesRegex(ValueError, "verification bypass"):
            self.check()

    def test_changed_crate_root(self):
        self.alter("verified/lib.rs", "mod step_by;", "")
        with self.assertRaisesRegex(ValueError, "crate roots must match"):
            self.check()


if __name__ == "__main__":
    unittest.main()
