#!/usr/bin/env python3

import argparse
import csv
import glob
import json
import re
import sys


def read_kani_list(kani_list_file, scanner_data):
    with open(kani_list_file, 'r') as f:
        harnesses = json.load(f)

    harness_pattern1 = re.compile(r'^(.+)::verify::(check|verify)_(.+)$')
    harness_pattern2 = re.compile(
            r'^(.+)::verify::(non_null|nonzero)_check_(.+)$')
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
                lt_replaced = h.replace('<\'_>', '<\'a>')
                if scanner_data.get(h) is None and (
                        scanner_data.get(lt_replaced) is not None):
                    fn = lt_replaced
                else:
                    fn = h
            fn_info = scanner_data.get(
                    fn, {'crate': None, 'target_safeness': None})
            standard_harnesses[h] = {
                    'file_name': file_name,
                    'crate': fn_info['crate'],
                    'function': fn,
                    'target_safeness': fn_info['target_safeness']
                }

    contract_harnesses = {}
    for file_name, l in harnesses['contract-harnesses'].items():
        for h in l:
            assert contract_harnesses.get(h) is None
            contract_harnesses[h] = {
                    'file_name': file_name,
                    'crate': None,
                    'target_safeness': None
                }
    for o in harnesses['contracts']:
        for h in o['harnesses']:
            fn = o['function']
            fn_info = scanner_data.get(
                    fn, {'crate': None, 'target_safeness': None})
            if h == 'kani::internal::automatic_harness':
                entry = contract_harnesses[fn]
            else:
                entry = contract_harnesses[h]
                if o['file'] != entry['file_name']:
                    # replace harness file name by target function file name
                    entry['file_name'] = o['file']
            entry['function'] = fn
            entry['crate'] = fn_info['crate']
            entry['target_safeness'] = fn_info['target_safeness']

    return contract_harnesses, standard_harnesses


def read_scanner_results(scanner_results_dir):
    crate_pattern = re.compile(r'^.*/(.+)_scan_functions.csv$')
    fn_to_info = {}
    for csv_file in glob.glob(f'{scanner_results_dir}/*_scan_functions.csv'):
        crate_match = re.match(crate_pattern, csv_file)
        crate = crate_match.group(1)
        with open(csv_file) as f:
            csv_reader = csv.DictReader(f, delimiter=';')
            for row in csv_reader:
                fn = row['name']
                if row['is_unsafe'] == 'false':
                    target_safeness = 'unsafe'
                elif row['has_unsafe_ops'] == 'true':
                    target_safeness = 'safe abstraction'
                else:
                    target_safeness = 'safe'
                if ex_entry := fn_to_info.get(fn):
                    # print(f'Scanner entry for {fn} already exists',
                    #       file=sys.stderr)
                    # the below don't even hold!
                    # assert ex_entry['crate'] == crate
                    # assert ex_entry['target_safeness'] == target_safeness
                    continue
                fn_to_info[fn] = {
                        'crate': crate,
                        'target_safeness': target_safeness
                    }

    return fn_to_info


def find_harness_map_entry(
        harness, autoharness_for_contract, contract_harnesses,
        standard_harnesses):
    if entry := contract_harnesses.get(harness):
        return (entry, True)
    elif entry := standard_harnesses.get(harness):
        with_contract = autoharness_for_contract is True
        return (entry, with_contract)
    else:
        return None, None


def init_entry(
        match_group, is_autoharness, autoharness_for_contract,
        contract_harnesses, standard_harnesses, active_threads,
        autoharness_info):
    thread_id = int(match_group(1))
    harness = match_group(2)
    (harness_map_entry, with_contract) = find_harness_map_entry(
            harness, autoharness_for_contract, contract_harnesses,
            standard_harnesses)
    if is_autoharness:
        assert autoharness_info[harness] == 'ok'
        del autoharness_info[harness]
        autoharness_result = 'ok'
    else:
        fn = harness_map_entry['function']
        if autoharness_info_entry := autoharness_info.get(fn):
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
            'crate': harness_map_entry['crate'],
            'function': harness_map_entry['function'],
            'function_safeness': harness_map_entry['target_safeness'],
            'file_name': harness_map_entry['file_name'],
            'n_failed_properties': None,
            'n_total_properties': None,
            'result': None,
            'time': None,
            'output': []
        }


def create_autoharness_result(
        fn, autoharness_result, contract_harnesses, standard_harnesses,
        scanner_data):
    (harness_map_entry, with_contract) = find_harness_map_entry(
            fn, None, contract_harnesses, standard_harnesses)
    if harness_map_entry is None:
        fn_info = scanner_data.get(
                fn, {'crate': None, 'target_safeness': None})
        return {
                'harness': fn,
                'is_autoharness': True,
                'autoharness_result': autoharness_result,
                'with_contract': None,
                'crate': fn_info['crate'],
                'function': fn,
                'function_safeness': fn_info['target_safeness'],
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
                'file_name': harness_map_entry['file_name'],
                'n_failed_properties': None,
                'n_total_properties': None,
                'result': None,
                'time': None,
                'output': []
            }


def parse_autoharness_info(lines, i):
    fn_ok_pattern = re.compile(r'^\| (.+?)\s+\|$')
    fn_fail_pattern = re.compile(r'^\| (.+?)\s+\| (.+?)\s+\|$')
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
                line.startswith('| Chosen Function') or
                line.startswith('If you believe that the provided reason') or
                line.startswith('| Skipped Function')):
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
                fn = fn_match.group(1)
                # there may be multiple entries here
                # assert autoharness_info.get(fn) is None
                autoharness_info[fn] = fn_match.group(2)
            else:
                fn_match = re.match(fn_ok_pattern, line)
                fn = fn_match.group(1)
                assert autoharness_info.get(fn) is None
                autoharness_info[fn] = 'ok'
            i += 1

    return i, autoharness_info


def parse_log_lines(
        lines, contract_harnesses, standard_harnesses, scanner_data):
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
            next_i = i + 1
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
            assert thread_id is not None
            active_threads[thread_id]['n_failed_properties'] = int(
                    property_match.group(1))
            active_threads[thread_id]['n_total_properties'] = int(
                    property_match.group(2))
        elif thread_id is not None:
            if line not in ['VERIFICATION RESULT:', '']:
                active_threads[thread_id]['output'].append(line)

    assert len(active_threads) == 0

    for fn, value in autoharness_info.items():
        all_results.append({'result': create_autoharness_result(
            fn, value, contract_harnesses, standard_harnesses, scanner_data)})

    return all_results


def main():
    parser = argparse.ArgumentParser(
            description='Parse log file of multi-threaded autoharness results')
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
