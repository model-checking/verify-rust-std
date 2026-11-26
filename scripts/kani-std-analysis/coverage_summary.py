"""
Which library functions autoharness can generate a harness for, read from the
`<crate>_autoharness_data.json` files that scripts/autoharness_analyzer writes:
how many functions get a harness and how many do not, by reason, and, compared
with another run, the functions that gained or lost their harness. Used by
`autoharness_report.py`.

The analyzer only generates harnesses; it does not run them. Whether a harness
verifies is what `results_summary.py` reports.
"""

import collections
import json
import os

from results_summary import change_row, code_span, listed

CRATES = ['core', 'alloc', 'std']
CRATE_LIST = f'{", ".join(CRATES[:-1])} and {CRATES[-1]}'
GENERATED = 'harness generated'
# Skip reasons with a row of their own, as the analyzer spells them.
REASONS = {
    'Generic Function': 'generic function',
    'Missing Arbitrary implementation for argument(s)':
        'an argument type has no `kani::Arbitrary`',
    'Requires --bounded-arguments for argument(s)':
        'needs `--bounded-arguments`',
}
OTHER = 'other reason'
# Not library functions somebody could unblock: Kani's own harnesses and
# contract instrumentation, and functions a run with filters did not look at.
NOT_COUNTED = ['Kani implementation', 'Did not match provided filters']
ROWS = [GENERATED] + list(REASONS.values()) + [OTHER]


def load(directory):
    """Yield (crate, analyzer data) for the analyzer output in `directory`."""
    for crate in CRATES:
        path = os.path.join(directory, f'{crate}_autoharness_data.json')
        with open(path) as f:
            yield crate, json.load(f)


def row_of(reason):
    """Row a skip reason is counted in, or None if it is not counted."""
    return None if reason in NOT_COUNTED else REASONS.get(reason, OTHER)


def read(directory):
    """Return (count per row, {'crate: function': row}) for the analyzer
    output in `directory`."""
    counts = collections.Counter()
    status = {}
    for crate, data in load(directory):
        # A list, not a map: two functions can share a printed name.
        # shortcut: such functions are counted one by one but share one entry
        # in the map, so the lists of changes name them once. Key the map by
        # more than the name if the library ever has enough of them to matter.
        for function, _safety in data['chosen']:
            counts[GENERATED] += 1
            status[f'{crate}: {function}'] = GENERATED
        for function, skipped in data['skipped'].items():
            row = row_of(skipped['reason'])
            if row is not None:
                counts[row] += 1
                status[f'{crate}: {function}'] = row
    return counts, status


def generated_changes(head, base):
    """(can now, can no longer): the functions with a harness in `head` and
    not in `base`, and the other way round. Both are the output of `read`."""
    generated, base_generated = (
        {f for f, row in status.items() if row == GENERATED}
        for _, status in (head, base))
    return (sorted(generated - base_generated),
            sorted(base_generated - generated))


def label(row):
    return 'Harness generated' if row == GENERATED else f'No harness: {row}'


def section(title, functions, base, head):
    if not functions:
        return []
    absent = 'not in the library'
    return ['', f'#### {title} ({len(functions):,})', ''] + listed(
        functions, lambda f: f'- {code_span(f)}: '
        f'{base.get(f, absent)} → {head.get(f, absent)}')


def summarize(head, base=None):
    """Markdown summary of `head`, compared with `base` if given.

    Both are the output of `read`.
    """
    counts, status = head
    lines = ['### Functions autoharness can handle', '']
    if base is None:
        lines += ['| | Functions |', '| --- | ---: |']
        lines += [f'| {label(row)} | {counts[row]:,} |' for row in ROWS]
    else:
        base_counts, base_status = base
        lines += ['| | Base | This run | Change |',
                  '| --- | ---: | ---: | ---: |']
        lines += [change_row(label(row), base_counts[row], counts[row])
                  for row in ROWS]
        can_now, cannot = generated_changes(head, base)
        lines += section('Can now get a harness', can_now, base_status, status)
        lines += section('Can no longer get a harness', cannot,
                         base_status, status)
    lines += ['', f'Counts cover {CRATE_LIST}. '
              'A generated harness is not a proof yet: CI runs only the '
              'harnesses counted below.']
    return '\n'.join(lines) + '\n'
