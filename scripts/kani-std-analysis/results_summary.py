"""
The automatic harnesses of a Kani run, read from the JSON that `log_parser.py`
writes: how many verified, failed and timed out, and, compared with another
run, every harness whose result differs. Used by `autoharness_report.py`.
"""

import json

VERDICTS = ['Verified', 'Failed', 'Timed out']
# Longest list of harnesses printed in one section; the rest is counted.
LIST_LIMIT = 50


def verdict(result):
    """Verdict of one log_parser record, or None if the harness did not run."""
    if result['result'] is None:
        return None
    if result['result'].startswith('SUCCESSFUL'):
        return 'Verified'
    # log_parser records a CBMC timeout as time "TO" on a FAILED result.
    if result['time'] == 'TO':
        return 'Timed out'
    return 'Failed'


def harness_verdicts(entries):
    """Map each automatic harness that ran to the sorted verdicts of its runs.

    A function that exists in several crates runs once per crate under the
    same name, hence a list.
    """
    verdicts = {}
    for entry in entries:
        result = entry['result']
        v = verdict(result)
        if result['is_autoharness'] and v is not None:
            verdicts.setdefault(result['harness'], []).append(v)
    return {harness: sorted(v) for harness, v in verdicts.items()}


def count(verdicts, v):
    return sum(runs.count(v) for runs in verdicts.values())


def describe(runs):
    return ', '.join(runs) if runs else 'not run'


def plural(n, one, many=None):
    """`n` with its noun: "1 harness", "2,000 harnesses"."""
    return f'{n:,} {one if n == 1 else many or one + "s"}'


def code_span(name):
    """`name` as a Markdown code span. The name comes from a log: keep it on
    one line and make sure it cannot end the span early."""
    return '`' + ' '.join(name.replace('`', "'").split()) + '`'


def listed(items, render):
    """Markdown list of the first LIST_LIMIT items; the rest is counted."""
    lines = [render(item) for item in items[:LIST_LIMIT]]
    if len(items) > LIST_LIMIT:
        lines.append(f'- and {len(items) - LIST_LIMIT:,} more')
    return lines


def change_row(label, old, new):
    """Table row with a count in two runs and the signed difference."""
    change = f'{new - old:+,}' if new != old else '0'
    return f'| {label} | {old:,} | {new:,} | {change} |'


def section(title, changes):
    """Markdown list of (harness, base runs, head runs); nothing if empty."""
    if not changes:
        return []
    return ['', f'#### {title} ({len(changes):,})', ''] + listed(
        changes, lambda c: f'- {code_span(c[0])}: {describe(c[1])} → '
        f'{describe(c[2])}')


def changes(head, base):
    """(gained, lost, other): the harnesses with more verified runs in `head`
    than in `base`, with fewer, and with another difference, each as
    (harness, base runs, head runs)."""
    gained, lost, other = [], [], []
    for harness in sorted(base.keys() | head.keys()):
        old, new = base.get(harness, []), head.get(harness, [])
        if old == new:
            continue
        # A function that exists in several crates has one run per crate.
        if new.count('Verified') > old.count('Verified'):
            gained.append((harness, old, new))
        elif new.count('Verified') < old.count('Verified'):
            lost.append((harness, old, new))
        else:
            other.append((harness, old, new))
    return gained, lost, other


def summarize(head, base=None):
    """Markdown summary of `head`, compared with `base` if given.

    Both are the output of `harness_verdicts`.
    """
    lines = ['### Harnesses verified in CI', '']
    if base is None:
        lines += ['| | Harnesses |', '| --- | ---: |']
        lines += [f'| {v} | {count(head, v):,} |' for v in VERDICTS]
        return '\n'.join(lines) + '\n'

    lines += ['| | Base | This run | Change |', '| --- | ---: | ---: | ---: |']
    lines += [change_row(v, count(base, v), count(head, v)) for v in VERDICTS]

    gained, lost, other = changes(head, base)
    if not (gained or lost or other):
        lines += ['', 'No automatic harness changed its result.']
    lines += section('Newly verified', gained)
    lines += section('No longer verified', lost)
    lines += section('Other changes', other)
    return '\n'.join(lines) + '\n'


def read(path):
    with open(path) as f:
        return harness_verdicts(json.load(f))
