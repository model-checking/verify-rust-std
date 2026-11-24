#!/usr/bin/env python3

"""
Write what people read about the autoharness results of a run, as Markdown:
```
python3 autoharness_report.py comment coverage/ results.json \
    [--base-coverage base-coverage/] [--base-results base-results.json]
```
`comment` is the pull request comment: what the pull request changes,
compared with `main`. `coverage/` holds the analyzer output and `results.json`
is the output of `log_parser.py`.
"""

import argparse

import coverage_summary
import results_summary
from coverage_summary import CRATE_LIST, GENERATED
from results_summary import code_span, plural

# Longest list of functions shown outside the collapsed details.
SHOWN = 10
BAR = 20


def bar(n, total, width=BAR):
    filled = min(width, round(width * n / total)) if total else 0
    return '█' * filled + '░' * (width - filled)


def steps(coverage, verdicts):
    """(all functions, with a harness, verified in CI); the first two are None
    without analyzer output."""
    verified = results_summary.count(verdicts, 'Verified')
    if coverage is None:
        return None, None, verified
    counts, _ = coverage
    return sum(counts.values()), counts[GENERATED], verified


def shown(title, names):
    """A short list at the top level; the details below hold all of it."""
    if not names:
        return []
    lines = ['', f'**{title}**', '']
    lines += [f'- {code_span(name)}' for name in names[:SHOWN]]
    if len(names) > SHOWN:
        # The details hold at most LIST_LIMIT names of a list.
        below = (', listed below'
                 if len(names) <= results_summary.LIST_LIMIT else '')
        lines.append(f'- and {len(names) - SHOWN:,} more{below}')
    return lines


def comment(coverage, verdicts, base_coverage=None, base_verdicts=None,
            base_stamp=None):
    """Markdown for the pull request comment.

    `coverage` and `base_coverage` are the output of `coverage_summary.read`,
    the verdicts that of `results_summary.read`; any of them can be None.
    """
    total, written, verified = steps(coverage, verdicts or {})
    compared = base_verdicts is not None
    base_total, base_written, base_verified = steps(
        base_coverage, base_verdicts or {})

    # The same lists as in the details below, so that the two cannot disagree.
    newly, no_longer, failing, changed = [], [], [], []
    if compared:
        gained, lost, other = results_summary.changes(
            verdicts or {}, base_verdicts)
        newly = [harness for harness, _, _ in gained]
        no_longer = [harness for harness, _, _ in lost]
        # Not verified on `main` either, but it did not fail there.
        failing = [harness for harness, old, new in other
                   if len(new) - new.count('Verified')
                   > len(old) - old.count('Verified')]
        # For example from timed out to failed.
        changed = [harness for harness, _, _ in other
                   if harness not in failing]
    can_now, cannot = [], []
    both_coverages = bool(coverage and base_coverage)
    if both_coverages:
        can_now, cannot = coverage_summary.generated_changes(
            coverage, base_coverage)

    # The headline is the most urgent change; the sentences cover all of them.
    means = []
    if no_longer:
        means.append(
            'A proof that passes on `main` does not pass with this change: '
            'it fails or is no longer run. Check it before merging.'
            if len(no_longer) == 1 else
            f'{len(no_longer):,} proofs that pass on `main` do not pass with '
            'this change: they fail or are no longer run. Check them before '
            'merging.')
    more_fail = plural(len(failing), 'more harness fails',
                       'more harnesses fail')
    if failing:
        means.append(f'{more_fail} than on `main`.')
    if newly:
        means.append(
            f'CI now proves {plural(len(newly), "more function")} on every '
            'pull request.')
    if can_now:
        means.append(
            'Autoharness writes a harness for '
            f'{plural(len(can_now), "more function")}. CI does not run '
            + ('it yet. To verify it,' if len(can_now) == 1 else
               'them yet. To verify one,') + ' list it in `kani.yml`.')
    if cannot:
        means.append(
            'Autoharness can no longer write a harness for '
            f'{plural(len(cannot), "function")} that had one on `main`.')
    if changed:
        means.append(
            f'{plural(len(changed), "harness", "harnesses")} that '
            f'{"does" if len(changed) == 1 else "do"} not verify on `main` '
            'changed in another way, for example from timed out to failed.')
    if (newly or no_longer or failing or changed) \
            and not (can_now or cannot) and both_coverages:
        means.append('Which functions have a harness did not change.')

    if not compared:
        headline = 'Autoharness results'
        means = ['There are no results of `main` to compare with.']
    elif no_longer:
        headline = '✗ ' + plural(
            len(no_longer), 'harness no longer verifies',
            'harnesses no longer verify')
    elif failing:
        headline = f'✗ {more_fail}'
    elif newly:
        headline = (f'+{plural(len(newly), "harness", "harnesses")} '
                    'verified in CI')
    elif can_now:
        headline = f'+{plural(len(can_now), "function")} can now get a harness'
    elif cannot:
        headline = (f'−{plural(len(cannot), "function")} can no longer get '
                    'a harness')
    elif changed:
        headline = plural(len(changed), 'harness result changed',
                          'harness results changed')
    else:
        headline = 'No change to the autoharness results'
        means = ['This pull request does not change which functions have a '
                 'harness or which harnesses verify.' if both_coverages else
                 'This pull request does not change which harnesses verify. '
                 'There is no analyzer output to compare which functions '
                 'have a harness.']

    def cell(n, base_n=None):
        if n is None:
            return '—'
        if base_n is None or n == base_n:
            return f'{n:,}'
        return f'**{n:,}** ({n - base_n:+,})'

    def row(title, text, n, base_n):
        graph = bar(n or 0, total) if total else ''
        cells = [f'**{title}**<br>{text}', graph]
        if compared:
            cells.append(cell(base_n))
        cells.append(cell(n, base_n if compared else None))
        return '| ' + ' | '.join(cells) + ' |'

    base_column = 'Main' + (f'<br>{base_stamp}' if base_stamp else '')
    header = (['Step', ''] + ([base_column] if compared else [])
              + ['This pull request'])
    lines = [f'## {headline}', '',
             '**What this means:** ' + ' '.join(means), '',
             '| ' + ' | '.join(header) + ' |',
             '| --- | --- |' + ' ---: |' * (len(header) - 2),
             row('All functions', f'in {CRATE_LIST}', total, base_total),
             row('Harness written', 'Autoharness wrote a harness for the '
                 'function. Most have not been run yet',
                 written, base_written),
             row('Verified in CI', 'CI ran the harness and Kani proved it',
                 verified, base_verified)]
    lines += shown('No longer verified', no_longer)
    lines += shown('Failing', failing)
    lines += shown('Newly verified', newly)
    lines += shown('Can now get a harness', can_now)
    lines += shown('Can no longer get a harness', cannot)
    lines += shown('Other changes', changed)

    if compared:
        at = (f' at {base_stamp.replace(" · ", ", commit ")}'
              if base_stamp else '')
        lines += ['', f'Compared with `main`{at}. If `main` has new merges '
                  'since, run this again to compare with them.']
    lines += ['', '<details><summary>Counts by reason, and every function '
              'that changed</summary>', '']
    if coverage:
        lines.append(coverage_summary.summarize(coverage, base_coverage))
    if verdicts is not None:
        lines.append(results_summary.summarize(verdicts, base_verdicts))
    lines += ['</details>']
    return '\n'.join(lines) + '\n'


def read_coverage(directory):
    """Analyzer output in `directory`, or None if that job produced none."""
    try:
        return coverage_summary.read(directory) if directory else None
    except FileNotFoundError:
        return None


def main():
    parser = argparse.ArgumentParser(
            description=__doc__,
            formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('kind', choices=['comment'])
    parser.add_argument('coverage', help='directory with the analyzer output')
    parser.add_argument('results', help='results.json of the run')
    parser.add_argument('--base-coverage')
    parser.add_argument('--base-results')
    parser.add_argument('--base-stamp', help='date and commit of the base run')
    args = parser.parse_args()

    verdicts = results_summary.read(args.results)
    base_verdicts = (results_summary.read(args.base_results)
                     if args.base_results else None)
    print(comment(read_coverage(args.coverage), verdicts,
                  read_coverage(args.base_coverage), base_verdicts,
                  args.base_stamp), end='')


if __name__ == '__main__':
    main()
