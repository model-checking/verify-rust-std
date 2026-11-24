import unittest

from autoharness_report import comment
from coverage_summary import read
from results_summary import harness_verdicts
from test_coverage_summary import BASE, HEAD, analyzer_output


def verdicts(**harnesses):
    """Verdicts of automatic harnesses given as name='SUCCESSFUL' or 'FAILED'."""
    return harness_verdicts([
        {'result': {'harness': name, 'is_autoharness': True,
                    'result': result, 'time': '1'}}
        for name, result in harnesses.items()])


class CommentTest(unittest.TestCase):
    def comment(self, head, base, coverage=(BASE, BASE)):
        return comment(read(coverage[0]), head, read(coverage[1]), base,
                       'Nov 10 · 8089282')

    def test_newly_verified(self):
        text = self.comment(verdicts(kept='SUCCESSFUL', broken='SUCCESSFUL'),
                            verdicts(kept='SUCCESSFUL'))
        self.assertTrue(text.startswith(
            '## +1 harness verified in CI\n\n**What this means:** CI now '
            'proves 1 more function on every pull request. Which functions '
            'have a harness did not change.\n'))
        self.assertIn('| Step |  | Main<br>Nov 10 · 8089282 '
                      '| This pull request |', text)
        self.assertIn('Kani proved it | █████░░░░░░░░░░░░░░░ | 1 | **2** (+1) |',
                      text)
        self.assertIn('**Newly verified**\n\n- `broken`', text)
        self.assertIn('Compared with `main` at Nov 10, commit 8089282.', text)

    def test_regression_comes_first(self):
        text = self.comment(verdicts(kept='FAILED', broken='SUCCESSFUL'),
                            verdicts(kept='SUCCESSFUL'))
        self.assertTrue(text.startswith(
            '## ✗ 1 harness no longer verifies\n\n**What this means:** '
            'A proof that passes on `main` does not pass with this change: '
            'it fails or is no longer run. Check it before merging. CI now '
            'proves 1 more function'))
        self.assertIn('**No longer verified**\n\n- `kept`', text)

    def test_one_crate_of_two_regresses(self):
        # The same harness name runs once per crate.
        def run(result):
            return {'result': {'harness': 'twin', 'is_autoharness': True,
                               'result': result, 'time': '1'}}
        text = self.comment(
            harness_verdicts([run('SUCCESSFUL'), run('FAILED')]),
            harness_verdicts([run('SUCCESSFUL'), run('SUCCESSFUL')]))
        self.assertTrue(text.startswith('## ✗ 1 harness no longer verifies\n'))
        self.assertIn('**No longer verified**\n\n- `twin`', text)

    def test_new_harness_fails(self):
        text = self.comment(verdicts(kept='SUCCESSFUL', broken='FAILED'),
                            verdicts(kept='SUCCESSFUL'))
        self.assertTrue(text.startswith(
            '## ✗ 1 more harness fails\n\n**What this means:** '
            '1 more harness fails than on `main`. Which functions'))
        self.assertIn('**Failing**\n\n- `broken`', text)

    def test_other_change_is_not_no_change(self):
        timed_out = harness_verdicts([{'result': {
            'harness': 'slow', 'is_autoharness': True, 'result': 'FAILED',
            'time': 'TO'}}])
        text = self.comment(verdicts(slow='FAILED'), timed_out)
        self.assertTrue(text.startswith(
            '## 1 harness result changed\n\n**What this means:** 1 harness '
            'that does not verify on `main` changed in another way, for '
            'example from timed out to failed. Which functions'))
        self.assertIn('**Other changes**\n\n- `slow`', text)
        self.assertIn('- `slow`: Timed out → Failed', text)

    def test_one_function_can_now_get_a_harness(self):
        one_more = analyzer_output((['kept', 'broken', 'removed', 'new'], {}),
                                   std=(['kept'], {}))
        text = self.comment(verdicts(), verdicts(), coverage=(one_more, BASE))
        self.assertIn('for 1 more function. CI does not run it yet. To '
                      'verify it, list it in `kani.yml`.', text)

    def test_large_counts_have_separators(self):
        many = verdicts(**{f'h{i}': 'SUCCESSFUL' for i in range(1200)})
        text = self.comment(many, verdicts())
        self.assertTrue(text.startswith('## +1,200 harnesses verified in CI'))
        self.assertIn('| Verified | 0 | 1,200 | +1,200 |', text)
        self.assertIn('#### Newly verified (1,200)', text)
        self.assertIn('- and 1,190 more\n', text)
        self.assertIn('- and 1,150 more\n', text)

    def test_no_analyzer_output(self):
        text = comment(None, verdicts(kept='SUCCESSFUL'), None,
                       verdicts(kept='SUCCESSFUL'))
        self.assertIn('does not change which harnesses verify. There is no '
                      'analyzer output', text)

    def test_harness_changes(self):
        text = self.comment(verdicts(), verdicts(), coverage=(HEAD, BASE))
        self.assertTrue(text.startswith(
            '## +3 functions can now get a harness\n'))
        self.assertIn('Autoharness can no longer write a harness for '
                      '2 functions that had one on `main`.', text)
        self.assertIn('| 4 | **6** (+2) |', text)
        self.assertIn('**Can now get a harness**\n\n- `core: added`', text)

    def test_no_change(self):
        text = self.comment(verdicts(kept='SUCCESSFUL'),
                            verdicts(kept='SUCCESSFUL'))
        self.assertTrue(text.startswith(
            '## No change to the autoharness results\n'))
        self.assertNotIn('(+', text)

    def test_without_main(self):
        text = comment(read(BASE), verdicts(kept='SUCCESSFUL'))
        self.assertTrue(text.startswith('## Autoharness results\n'))
        self.assertIn('| Step |  | This pull request |', text)
        self.assertNotIn('Compared with', text)


if __name__ == '__main__':
    unittest.main()
