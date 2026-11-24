import unittest

from results_summary import harness_verdicts, summarize


def entry(harness, result, time='1.5s', is_autoharness=True):
    """One log_parser record, with only the fields results_summary reads."""
    return {'result': {'harness': harness, 'is_autoharness': is_autoharness,
                       'result': result, 'time': time}}


class HarnessVerdictsTest(unittest.TestCase):
    def test_verdicts(self):
        entries = [
            entry('ok', 'SUCCESSFUL'),
            entry('bad', 'FAILED'),
            entry('slow', 'FAILED', time='TO'),
            # Selected or skipped by autoharness, but never run.
            entry('skipped', None, time=None),
            # Hand-written harnesses are not counted.
            entry('manual', 'SUCCESSFUL', is_autoharness=False),
            # The same function in two crates runs twice under one name.
            entry('twice', 'SUCCESSFUL'),
            entry('twice', 'FAILED'),
        ]
        self.assertEqual(harness_verdicts(entries), {
            'ok': ['Verified'],
            'bad': ['Failed'],
            'slow': ['Timed out'],
            'twice': ['Failed', 'Verified'],
        })


class SummarizeTest(unittest.TestCase):
    def test_without_base(self):
        head = {'a': ['Verified'], 'b': ['Failed', 'Verified'], 'c': ['Timed out']}
        self.assertEqual(summarize(head), '\n'.join([
            '### Harnesses verified in CI',
            '',
            '| | Harnesses |',
            '| --- | ---: |',
            '| Verified | 2 |',
            '| Failed | 1 |',
            '| Timed out | 1 |',
            '',
        ]))

    def test_with_base(self):
        base = {
            'same': ['Verified'],
            'fixed': ['Failed'],
            'broken': ['Verified'],
            'removed': ['Verified'],
            'slower': ['Failed'],
            'two_crates': ['Verified', 'Verified'],
        }
        head = {
            'same': ['Verified'],
            'fixed': ['Verified'],
            'added': ['Verified'],
            'broken': ['Failed'],
            'slower': ['Timed out'],
            'new`\n\nfailure': ['Failed'],
            'two_crates': ['Verified'],
        }
        self.assertEqual(summarize(head, base), '\n'.join([
            '### Harnesses verified in CI',
            '',
            '| | Base | This run | Change |',
            '| --- | ---: | ---: | ---: |',
            '| Verified | 5 | 4 | -1 |',
            '| Failed | 2 | 2 | 0 |',
            '| Timed out | 0 | 1 | +1 |',
            '',
            '#### Newly verified (2)',
            '',
            '- `added`: not run → Verified',
            '- `fixed`: Failed → Verified',
            '',
            '#### No longer verified (3)',
            '',
            '- `broken`: Verified → Failed',
            '- `removed`: Verified → not run',
            # One of the two crates stopped running it: a loss, not a gain.
            '- `two_crates`: Verified, Verified → Verified',
            '',
            '#### Other changes (2)',
            '',
            # A backquote or a line break in a name cannot end the code span.
            "- `new' failure`: not run → Failed",
            '- `slower`: Failed → Timed out',
            '',
        ]))

    def test_no_change(self):
        runs = {'a': ['Verified']}
        self.assertIn('No automatic harness changed its result.',
                      summarize(runs, dict(runs)))

    def test_long_list_is_cut(self):
        head = {f'f{i:03}': ['Verified'] for i in range(60)}
        summary = summarize(head, {})
        self.assertIn('#### Newly verified (60)', summary)
        self.assertIn('- `f049`: not run → Verified', summary)
        self.assertNotIn('f050', summary)
        self.assertIn('- and 10 more', summary)


if __name__ == '__main__':
    unittest.main()
