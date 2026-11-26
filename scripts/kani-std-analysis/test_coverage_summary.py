import json
import os
import tempfile
import unittest

from coverage_summary import read, summarize

MISSING = 'Missing Arbitrary implementation for argument(s)'


def analyzer_output(core, alloc=None, std=None):
    """Directory with analyzer JSON; each crate is (chosen names, skipped)."""
    directory = tempfile.mkdtemp()
    crates = {'core': core, 'alloc': alloc or ([], {}), 'std': std or ([], {})}
    for crate, (chosen, skipped) in crates.items():
        path = os.path.join(directory, f'{crate}_autoharness_data.json')
        with open(path, 'w') as f:
            json.dump({
                'chosen': [[name, 'safe'] for name in chosen],
                'skipped': {
                    name: {'reason': reason, 'safety': 'safe', 'types': []}
                    for name, reason in skipped.items()},
            }, f)
    return directory


BASE = analyzer_output(
    (['kept', 'broken', 'removed'], {
        'unblocked': 'Generic Function',
        'needs_arbitrary': MISSING,
        'bounded': 'Requires --bounded-arguments for argument(s)',
        'no_body': 'The function does not have a body',
        'kani_harness': 'Kani implementation',
    }),
    std=(['kept'], {}))
HEAD = analyzer_output(
    # The same printed name twice counts twice, as in the analyzer's tables.
    (['kept', 'unblocked', 'added', 'twin', 'twin'], {
        'broken': MISSING,
        'needs_arbitrary': MISSING,
        'bounded': 'Requires --bounded-arguments for argument(s)',
        'no_body': 'The function does not have a body',
        'kani_harness': 'Kani implementation',
        'another_kani_harness': 'Kani implementation',
        'filtered': 'Did not match provided filters',
    }),
    std=(['kept'], {}))


class CoverageSummaryTest(unittest.TestCase):
    def test_without_base(self):
        self.assertEqual(summarize(read(BASE)), '\n'.join([
            '### Functions autoharness can handle',
            '',
            '| | Functions |',
            '| --- | ---: |',
            '| Harness generated | 4 |',
            '| No harness: generic function | 1 |',
            '| No harness: an argument type has no `kani::Arbitrary` | 1 |',
            '| No harness: needs `--bounded-arguments` | 1 |',
            # Kani's own functions are not counted anywhere.
            '| No harness: other reason | 1 |',
            '',
            'Counts cover core, alloc and std. A generated harness is not a '
            'proof yet: CI runs only the harnesses counted below.',
            '',
        ]))

    def test_with_base(self):
        self.assertEqual(summarize(read(HEAD), read(BASE)), '\n'.join([
            '### Functions autoharness can handle',
            '',
            '| | Base | This run | Change |',
            '| --- | ---: | ---: | ---: |',
            '| Harness generated | 4 | 6 | +2 |',
            '| No harness: generic function | 1 | 0 | -1 |',
            '| No harness: an argument type has no `kani::Arbitrary` '
            '| 1 | 2 | +1 |',
            '| No harness: needs `--bounded-arguments` | 1 | 1 | 0 |',
            '| No harness: other reason | 1 | 1 | 0 |',
            '',
            '#### Can now get a harness (3)',
            '',
            '- `core: added`: not in the library → harness generated',
            '- `core: twin`: not in the library → harness generated',
            '- `core: unblocked`: generic function → harness generated',
            '',
            '#### Can no longer get a harness (2)',
            '',
            '- `core: broken`: harness generated → '
            'an argument type has no `kani::Arbitrary`',
            '- `core: removed`: harness generated → not in the library',
            '',
            'Counts cover core, alloc and std. A generated harness is not a '
            'proof yet: CI runs only the harnesses counted below.',
            '',
        ]))

    def test_no_change(self):
        summary = summarize(read(BASE), read(BASE))
        self.assertIn('| Harness generated | 4 | 4 | 0 |', summary)
        self.assertNotIn('####', summary)

    def test_missing_crate_is_an_error(self):
        directory = analyzer_output(([], {}))
        os.remove(os.path.join(directory, 'std_autoharness_data.json'))
        with self.assertRaises(FileNotFoundError):
            read(directory)


if __name__ == '__main__':
    unittest.main()
