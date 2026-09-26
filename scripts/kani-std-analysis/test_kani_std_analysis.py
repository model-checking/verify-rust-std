import unittest

from kani_std_analysis import strip_crate_prefix


class StripCratePrefixTest(unittest.TestCase):
    # Pinned to Kani's `strip_local_crate_prefix`: only a crate-root qualifier
    # is dropped, a path segment that merely shares the crate's name is kept.
    def test_matches_kani(self):
        cases = [
            # crate, scanner name, expected `kani list` name
            ("core", "<char as core::ascii::AsciiExt>::is_ascii",
             "<char as ascii::AsciiExt>::is_ascii"),
            ("core", "core::core_simd::vector::Simd", "core_simd::vector::Simd"),
            ("core", "ptr::align_offset", "ptr::align_offset"),
            ("core", "alloc::vec::Vec", "alloc::vec::Vec"),
            # Not idempotent, like Kani's copy: apply exactly once.
            ("main", "main::main::{closure#0}", "main::{closure#0}"),
            ("core", "core::core::foo", "core::foo"),
        ]
        for crate, name, expected in cases:
            with self.subTest(name=name):
                self.assertEqual(strip_crate_prefix(name, crate), expected)


if __name__ == "__main__":
    unittest.main()
