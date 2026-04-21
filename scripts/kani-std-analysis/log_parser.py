#!/usr/bin/env python3

"""
Parse log file of multi-threaded Kani run (terse output) into JSON.
Given a run of Kani on the standard library with `--jobs=<N>
--output-format=terse` (and, typically, `autoharness`) enabled this produces
a machine-processable JSON result via
```
python3 log_parser.py \
  --kani-list-file kani-list.json \
  --analysis-results-dir std_lib_analysis/results/ \
  verification.log -o results.json
```
where each entry in the resulting JSON array is of the form
```
{
  "thread_id": int,
  "result": {
    "harness": string,
    "is_autoharness": bool,
    "autoharness_result": string,
    "with_contract": bool,
    "crate": string,
    "function": string,
    "function_safeness": string,
    "file_name": string,
    "n_failed_properties": int,
    "n_total_properties": int,
    "result": string,
    "time": string,
    "output": array
  }
}
```
With the help of `jq` one can then conveniently compute various metrics:
```
jq 'map(select(.result.result == "SUCCESSFUL" and
               .result.is_autoharness == true and
               .result.crate == "core" and
               .result.function_safeness == "unsafe" and
               .result.with_contract == true)) | length' results.json
```
to find the number of successfully-verified contracts of unsafe functions in
crate `core` that were verified using automatically generated harnesses.
"""

import argparse
import csv
import glob
import json
import re
import sys


def read_scanner_results(scanner_results_dir):
    """Parse information produced by Kani's scanner tool."""
    crate_pattern = re.compile(r'^.*/(.+)_scan_functions.csv$')
    fn_to_info = {}
    for csv_file in glob.glob(f'{scanner_results_dir}/*_scan_functions.csv'):
        crate_match = re.match(crate_pattern, csv_file)
        crate = crate_match.group(1)
        with open(csv_file) as f:
            csv_reader = csv.DictReader(f, delimiter=';')
            for row in csv_reader:
                fn = row['name']
                if row['is_unsafe'] == 'true':
                    target_safeness = 'unsafe'
                elif row['has_unsafe_ops'] == 'true':
                    target_safeness = 'safe abstraction'
                else:
                    target_safeness = 'safe'
                if fn_to_info.get(fn) is None:
                    fn_to_info[fn] = {}
                else:
                    # assert fn_to_info[fn].get(crate) is None
                    if ex_entry := fn_to_info[fn].get(crate):
                        # print(f'Scanner entry for {fn} in {crate} already exists',
                        #       file=sys.stderr)
                        # the below doesn't even hold!
                        # assert ex_entry['target_safeness'] == target_safeness
                        continue
                fn_to_info[fn][crate] = {
                        'target_safeness': target_safeness,
                        'public_target': row['is_public'] == 'true'
                    }

    return fn_to_info


def read_kani_list(kani_list_file, scanner_data):
    """Read from kani_list_file (a JSON file produced using kani list) and
    combine the information with the scanner's data."""
    with open(kani_list_file, 'r') as f:
        harnesses = json.load(f)

    # There is no reasonable way to reliably deduce which function a
    # non-contract harness is targeting for verification, so we apply a bunch
    # of patterns that we know are being used. We expect that, over time,
    # manual harnesses will largely disappear.
    harness_pattern1 = re.compile(r'^(.+::)verify::(check|verify)_(.+)$')
    harness_pattern2 = re.compile(
            r'^(.+::)verify::(non_null|nonzero)_check_(.+)$')
    harness_pattern3 = re.compile(
            r'^time::duration_verify::duration_as_nanos(_panics)?$')
    harness_pattern4 = re.compile(
            r'^intrinsics::verify::transmute_unchecked_(.+)$')
    harness_pattern5 = re.compile(
            r'^num::verify::(carrying|widening)_mul_(.+)$')
    harness_pattern6 = re.compile(
            r'^option::verify::verify_as_slice$')
    standard_harnesses = {}
    for file_name, l in harnesses['standard-harnesses'].items():
        for h in l:
            assert standard_harnesses.get(h) is None
            if harness_match := re.match(harness_pattern1, h):
                fn = harness_match.group(1) + harness_match.group(3)
            elif harness_match := re.match(harness_pattern2, h):
                fn = harness_match.group(1) + harness_match.group(3)
            elif harness_match := re.match(harness_pattern3, h):
                fn = 'time::duration::as_nanos'
            elif harness_match := re.match(harness_pattern4, h):
                fn = 'intrinsics::transmute_unchecked'
            elif harness_match := re.match(harness_pattern5, h):
                fn = 'num::' + harness_match.group(1)
            elif h == 'option::verify::verify_as_slice':
                fn = 'option::Option::<T>::as_slice'
            else:
                fn = h
            fn_info = scanner_data.get(fn)
            if fn_info is None:
                standard_harnesses[h] = {
                        'file_name': file_name,
                        'crate': None,
                        'function': fn,
                        'target_safeness': None,
                        'public_target': None
                    }
            elif len(fn_info.keys()) > 1:
                crates = list(fn_info.keys())
                target_safenesses = [e['target_safeness']
                                     for _, e in fn_info.items()]
                public_targets = [e['public_target']
                                     for _, e in fn_info.items()]
                standard_harnesses[h] = {
                        'file_name': file_name,
                        'crate': crates,
                        'function': fn,
                        'target_safeness': target_safenesses,
                        'public_target': public_targets
                    }
            else:
                crate = list(fn_info.keys())[0]
                standard_harnesses[h] = {
                        'file_name': file_name,
                        'crate': crate,
                        'function': fn,
                        'target_safeness': fn_info[crate]['target_safeness'],
                        'public_target': fn_info[crate]['public_target']
                    }

    contract_harnesses = {}
    for file_name, l in harnesses['contract-harnesses'].items():
        for h in l:
            assert contract_harnesses.get(h) is None
            contract_harnesses[h] = {
                    'file_name': file_name,
                    'crate': None,
                    'target_safeness': None,
                    'public_target': None
                }
    for o in harnesses['contracts']:
        for h in o['harnesses']:
            fn = o['function']
            if h == 'core::kani::internal::automatic_harness':
                entry = contract_harnesses[fn]
            elif h == 'kani::internal::automatic_harness':
                entry = contract_harnesses[fn]
            else:
                entry = contract_harnesses[h]
                if o['file'] != entry['file_name']:
                    # replace harness file name by target function file name
                    entry['file_name'] = o['file']
            entry['function'] = fn
            fn_info = scanner_data.get(fn)
            if fn_info is not None:
                if len(fn_info.keys()) > 1:
                    crates = list(fn_info.keys())
                    target_safenesses = [e['target_safeness']
                                         for _, e in fn_info.items()]
                    public_targets = [e['public_target']
                                         for _, e in fn_info.items()]
                    entry['crate'] = crates
                    entry['target_safeness'] = target_safenesses
                    entry['public_target'] = public_targets
                else:
                    crate = list(fn_info.keys())[0]
                    entry['crate'] = crate
                    entry['target_safeness'] = fn_info[crate][
                            'target_safeness']
                    entry['public_target'] = fn_info[crate]['public_target']

    return contract_harnesses, standard_harnesses


def find_harness_map_entry(
        harness, autoharness_for_contract, contract_harnesses,
        standard_harnesses):
    """Find harness in either contract- or standard harness dict."""
    if entry := contract_harnesses.get(harness):
        return (entry, True)
    elif entry := standard_harnesses.get(harness):
        with_contract = autoharness_for_contract is True
        return (entry, with_contract)
    else:
        return {
                'crate': None,
                'function': None,
                'target_safeness': None,
                'public_target': None,
                'file_name': None
               }, None


def init_entry(
        match_group, is_autoharness, autoharness_for_contract,
        contract_harnesses, standard_harnesses, active_threads,
        autoharness_info):
    """Initialize verification result entry."""
    thread_id = int(match_group(1))
    harness = match_group(2)
    (harness_map_entry, with_contract) = find_harness_map_entry(
            harness, autoharness_for_contract, contract_harnesses,
            standard_harnesses)
    crate = harness_map_entry['crate']
    if is_autoharness:
        if crate is None:
            print(f'No autoharness info for {harness}', file=sys.stderr)
        else:
            if isinstance(crate, list):
                crate_list = crate
            else:
                crate_list = [crate]
            for c in crate_list:
                if autoharness_info.get(c) is None:
                    print(f'No autoharness info for {c}',
                            file=sys.stderr)
                else:
                    if autoharness_info[c][harness] != 'ok':
                        print(f'Unexpected autoharness info for {harness} in {c}',
                                file=sys.stderr)
                    del autoharness_info[c][harness]
        autoharness_result = 'ok'
    else:
        fn = harness_map_entry['function']
        if autoharness_info.get(crate) is None:
            autoharness_result = None
        elif autoharness_info_entry := autoharness_info[crate].get(fn):
            autoharness_result = autoharness_info_entry
            del autoharness_info_entry
        else:
            autoharness_result = None
    # Assert that the slot is empty when work starts
    if thread_id in active_threads:
        print(f'Error: Thread {thread_id} is already active ' +
              'when starting new work', file=sys.stderr)
        assert False
    active_threads[thread_id] = {
            'harness': harness,
            'is_autoharness': is_autoharness,
            'autoharness_result': autoharness_result,
            'with_contract': with_contract,
            'crate': crate,
            'function': harness_map_entry['function'],
            'function_safeness': harness_map_entry['target_safeness'],
            'public_target': harness_map_entry['public_target'],
            'file_name': harness_map_entry['file_name'],
            'n_failed_properties': None,
            'n_total_properties': None,
            'result': None,
            'time': None,
            'output': []
        }


def create_autoharness_result(
        crate, fn, autoharness_result, contract_harnesses, standard_harnesses,
        scanner_data):
    """Initialize entries from autoharness summary tables."""
    (harness_map_entry, with_contract) = find_harness_map_entry(
            fn, None, contract_harnesses, standard_harnesses)
    if harness_map_entry is None:
        fn_info = scanner_data.get(fn)
        if fn_info is None:
            return {
                    'harness': fn,
                    'is_autoharness': True,
                    'autoharness_result': autoharness_result,
                    'with_contract': None,
                    'crate': None,
                    'function': fn,
                    'function_safeness': None,
                    'public_target': None,
                    'file_name': None,
                    'n_failed_properties': None,
                    'n_total_properties': None,
                    'result': None,
                    'time': None,
                    'output': []
                }
        elif len(fn_info.keys()) > 1:
            crates = list(fn_info.keys())
            target_safenesses = [e['target_safeness']
                                 for _, e in fn_info.items()]
            public_targets = [e['public_target']
                                 for _, e in fn_info.items()]
            return {
                    'harness': fn,
                    'is_autoharness': True,
                    'autoharness_result': autoharness_result,
                    'with_contract': None,
                    'crate': crates,
                    'function': fn,
                    'function_safeness': target_safenesses,
                    'public_target': public_targets,
                    'file_name': None,
                    'n_failed_properties': None,
                    'n_total_properties': None,
                    'result': None,
                    'time': None,
                    'output': []
                }
        else:
            crate = list(fn_info.keys())[0]
            return {
                    'harness': fn,
                    'is_autoharness': True,
                    'autoharness_result': autoharness_result,
                    'with_contract': None,
                    'crate': crate,
                    'function': fn,
                    'function_safeness': fn_info[crate]['target_safeness'],
                    'public_target': fn_info[crate]['public_target'],
                    'file_name': None,
                    'n_failed_properties': None,
                    'n_total_properties': None,
                    'result': None,
                    'time': None,
                    'output': []
                }
    else:
        return {
                'harness': fn,
                'is_autoharness': True,
                'autoharness_result': autoharness_result,
                'with_contract': with_contract,
                'crate': harness_map_entry['crate'],
                'function': harness_map_entry['function'],
                'function_safeness': harness_map_entry['target_safeness'],
                'public_target': harness_map_entry['public_target'],
                'file_name': harness_map_entry['file_name'],
                'n_failed_properties': None,
                'n_total_properties': None,
                'result': None,
                'time': None,
                'output': []
            }


def parse_autoharness_info(lines, i):
    """Parse summary tables provided by autoharness."""
    ok_header_pattern = re.compile(r'^\| Crate\s+\| Selected Function')
    fail_header_pattern = re.compile(r'\| Crate\s+\| Skipped Function')
    fn_ok_pattern = re.compile(r'^\| (.+?)\s+\| (.+?)\s+\|$')
    fn_fail_pattern = re.compile(r'^\| (.+?)\s+\| (.+?)\s+\| (.+?)\s+\|$')
    parser_state = 0
    in_fails = False
    autoharness_info = {}
    while i < len(lines):
        line = lines[i].rstrip()
        if parser_state == 0 and (
                line.startswith('Kani generated automatic harnesses for') or
                line.startswith('Kani did not generate automatic harnesses')):
            parser_state = 1
            i += 1
        elif parser_state == 0 and not line:
            i += 1
        elif parser_state == 1 and (
                line.startswith('+--') or
                line.startswith('If you believe that the provided reason') or
                re.match(ok_header_pattern, line) is not None or
                re.match(fail_header_pattern, line) is not None):
            i += 1
        elif parser_state == 1 and line.startswith('+=='):
            parser_state = 2
            i += 1
        elif parser_state == 2 and line.startswith('|--'):
            i += 1
        elif parser_state == 2 and line.startswith('+--'):
            i += 1
            if in_fails:
                break
            else:
                parser_state = 0
                in_fails = True
        else:
            assert parser_state == 2
            if in_fails:
                fn_match = re.match(fn_fail_pattern, line)
                crate = fn_match.group(1)
                if autoharness_info.get(crate) is None:
                    autoharness_info[crate] = {}
                fn = fn_match.group(2)
                assert autoharness_info[crate].get(fn) is None
                autoharness_info[crate][fn] = fn_match.group(3)
            else:
                fn_match = re.match(fn_ok_pattern, line)
                crate = fn_match.group(1)
                if autoharness_info.get(crate) is None:
                    autoharness_info[crate] = {}
                fn = fn_match.group(2)
                assert autoharness_info[crate].get(fn) is None
                autoharness_info[crate][fn] = 'ok'
            i += 1

    return i, autoharness_info


def parse_log_lines(
        lines, contract_harnesses, standard_harnesses, scanner_data):
    """Parse (terse) output from multi-threaded Kani run while considering list
    and scanner data."""
    # Regular expressions for matching patterns
    start_work_autoharness_contract_pattern = re.compile(
            r'Thread (\d+): Autoharness: Checking function (.*)\'s contract ' +
            r'against all possible inputs\.\.\.$')
    start_work_autoharness_pattern = re.compile(
            r'Thread (\d+): Autoharness: Checking function (.*) against all ' +
            r'possible inputs\.\.\.$')
    start_work_manual_pattern = re.compile(
        r'Thread (\d+): Checking harness (.*)\.\.\.$')
    end_work_pattern = re.compile(r'Thread (\d+):$')
    property_pattern = re.compile(r'^ \*\* (\d+) of (\d+) failed')
    end_result_pattern = re.compile(r'^VERIFICATION:- (.*)')
    end_result_with_time_pattern = re.compile(r'^Verification Time: (.*)')

    # Track active threads and results
    active_threads = {}  # thread_id -> list of result lines
    all_results = []
    thread_id = None

    i = 0
    while i < len(lines):
        if lines[i].startswith('Kani generated automatic harnesses for'):
            (i, autoharness_info) = parse_autoharness_info(lines, i)

        line = lines[i].rstrip()
        i += 1

        # Check if a thread is starting work
        if start_match := start_work_autoharness_contract_pattern.search(line):
            init_entry(
                    start_match.group, True, True, contract_harnesses,
                    standard_harnesses, active_threads, autoharness_info)
            continue
        elif start_match := start_work_autoharness_pattern.search(line):
            init_entry(
                    start_match.group, True, False, contract_harnesses,
                    standard_harnesses, active_threads, autoharness_info)
            continue
        elif start_match := start_work_manual_pattern.search(line):
            init_entry(
                    start_match.group, False, None, contract_harnesses,
                    standard_harnesses, active_threads, autoharness_info)
            continue

        # Check if a thread is ending work
        if end_match := end_work_pattern.search(line):
            thread_id = int(end_match.group(1))
            assert thread_id in active_threads
            continue

        # Check if we're at the end of a result section
        if end_result_match := end_result_pattern.match(line):
            assert thread_id is not None
            active_threads[thread_id]['result'] = end_result_match.group(1)
            next_i = i
            if next_i < len(lines):
                next_line = lines[next_i].rstrip()
                if next_line.startswith('CBMC timed out.'):
                    active_threads[thread_id]['time'] = 'TO'
                    active_threads[thread_id]['output'].append(next_line)
                elif next_line.startswith('** WARNING:'):
                    active_threads[thread_id]['output'].append(next_line)
                elif next_line.startswith('[Kani]'):
                    active_threads[thread_id]['output'].append(next_line)
                    active_threads[thread_id]['output'].append(
                            lines[next_i + 2].rstrip())
                    next_i += 1
                elif t_match := end_result_with_time_pattern.match(next_line):
                    active_threads[thread_id]['time'] = t_match.group(1)
                if next_i + 1 < len(lines):
                    next_line = lines[next_i + 1].rstrip()
                    if t_match := end_result_with_time_pattern.match(
                            next_line):
                        active_threads[thread_id]['time'] = t_match.group(1)
            all_results.append({
                'thread_id': thread_id,
                'result': active_threads[thread_id]
            })
            del active_threads[thread_id]
            thread_id = None
        elif property_match := property_pattern.match(line):
            assert thread_id is not None, f'No known thread id at line {i}'
            active_threads[thread_id]['n_failed_properties'] = int(
                    property_match.group(1))
            active_threads[thread_id]['n_total_properties'] = int(
                    property_match.group(2))
        elif thread_id is not None:
            if line not in ['VERIFICATION RESULT:', '']:
                active_threads[thread_id]['output'].append(line)

    assert len(active_threads) == 0

    for crate, crate_value in autoharness_info.items():
        for fn, value in crate_value.items():
            all_results.append({
                'result': create_autoharness_result(
                    crate, fn, value, contract_harnesses, standard_harnesses,
                    scanner_data)
            })

    return all_results


def main():
    parser = argparse.ArgumentParser(
            description=__doc__,
            formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('log_file', help='Path to the log file to parse')
    parser.add_argument(
            '-o', '--output', help='Output file path (default: stdout)')
    parser.add_argument(
            '--kani-list-file',
            type=str,
            default='kani-list.json',
            help='Path to the JSON file containing the Kani list data ' +
                 '(default: kani-list.json)')
    parser.add_argument(
            '--analysis-results-dir',
            type=str,
            default='/tmp/std_lib_analysis/results',
            help='Path to the folder file containing the std-analysis.sh ' +
            'results (default: /tmp/std_lib_analysis/results)')
    args = parser.parse_args()

    scanner_data = read_scanner_results(args.analysis_results_dir)

    (contract_harnesses, standard_harnesses) = read_kani_list(
            args.kani_list_file, scanner_data)

    with open(args.log_file, 'r') as f:
        log_lines = f.readlines()

    results = parse_log_lines(
            log_lines, contract_harnesses, standard_harnesses, scanner_data)

    if args.output:
        with open(args.output, 'w') as f:
            json.dump(results, f, indent=2)
    else:
        print(json.dumps(results, indent=2))


if __name__ == '__main__':
    main()
