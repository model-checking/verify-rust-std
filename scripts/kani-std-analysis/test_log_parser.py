import json
import tempfile
import unittest

from log_parser import parse_log_lines, read_kani_list


class ReadKaniListTests(unittest.TestCase):
    def read_standard_harnesses(self, harnesses, scanner_data):
        with tempfile.NamedTemporaryFile(mode='w+') as source:
            json.dump({'standard-harnesses': harnesses,
                       'contract-harnesses': {}, 'contracts': []}, source)
            source.flush()
            return read_kani_list(source.name, scanner_data)[1]

    def test_exported_name_in_two_crates_preserves_both_locations(self):
        files = ['/repo/library/panic_abort/src/lib.rs',
                 '/repo/library/panic_unwind/src/lib.rs']
        scanner_data = {'other_function': {
            crate: {'target_safeness': 'unsafe', 'public_target': False}
            for crate in ('panic_abort', 'panic_unwind')}}
        result = self.read_standard_harnesses(
            {file: ['__rust_panic_cleanup'] for file in files}, scanner_data)
        entry = result['__rust_panic_cleanup']
        self.assertEqual(entry['file_name'], files)
        self.assertEqual(entry['crate'], ['panic_abort', 'panic_unwind'])
        self.assertEqual(entry['function'], '__rust_panic_cleanup')

    def test_repeated_identical_entry_preserves_scalar_metadata(self):
        result = self.read_standard_harnesses(
            {'library/core/src/example.rs': ['check_example', 'check_example']}, {})
        self.assertEqual(result['check_example']['file_name'],
                         'library/core/src/example.rs')
        self.assertIsNone(result['check_example']['crate'])

    def test_generic_contract_keeps_concrete_automatic_harness(self):
        concrete = '<array::IntoIter<i32, 2> as Iterator>::get_unchecked'
        generic = '<array::IntoIter<T, N> as Iterator>::get_unchecked'
        file = '/repo/library/core/src/array/iter.rs'
        with tempfile.NamedTemporaryFile(mode='w+') as source:
            json.dump({'standard-harnesses': {},
                       'contract-harnesses': {file: [concrete]},
                       'contracts': [{'function': generic, 'file': file,
                                      'harnesses': ['kani::internal::automatic_harness']}]},
                      source)
            source.flush()
            contracts, standard = read_kani_list(source.name, {})
        self.assertEqual(standard, {})
        self.assertEqual(set(contracts), {concrete})
        self.assertEqual(contracts[concrete]['function'], concrete)
        self.assertEqual(contracts[concrete]['file_name'], file)
        self.assertIsNone(contracts[concrete]['target_safeness'])


class ParseLogLinesTests(unittest.TestCase):
    def test_serial_manual_success_failure_and_timeout(self):
        lines = """Checking harness successful...
VERIFICATION RESULT:
 ** 0 of 2 failed
VERIFICATION:- SUCCESSFUL
Verification Time: 1s
Checking harness failed...
VERIFICATION RESULT:
 ** 1 of 5 failed
Failed Checks: pointer dereference
VERIFICATION:- FAILED
Verification Time: 2s
Checking harness timed_out...
VERIFICATION:- TIMEOUT
CBMC timed out.
""".splitlines()
        results = parse_log_lines(lines, {}, {}, {})
        self.assertEqual([entry['thread_id'] for entry in results], [0, 0, 0])
        self.assertEqual(
            [entry['result']['harness'] for entry in results],
            ['successful', 'failed', 'timed_out'])
        self.assertEqual(
            [entry['result']['result'] for entry in results],
            ['SUCCESSFUL', 'FAILED', 'TIMEOUT'])
        self.assertEqual(
            [entry['result']['time'] for entry in results], ['1s', '2s', 'TO'])
        self.assertEqual(results[0]['result']['n_failed_properties'], 0)
        self.assertEqual(results[1]['result']['n_failed_properties'], 1)
        self.assertEqual(results[1]['result']['n_total_properties'], 5)
        self.assertIn('Failed Checks: pointer dereference',
                      results[1]['result']['output'])
        self.assertIsNone(results[2]['result']['n_failed_properties'])

    def test_parallel_results_can_finish_out_of_order(self):
        lines = """Thread 0: Checking harness first...
Thread 1: Checking harness second...
Thread 1:
VERIFICATION RESULT:
 ** 1 of 5 failed
VERIFICATION:- FAILED
Verification Time: 2s
Thread 0:
VERIFICATION RESULT:
 ** 0 of 2 failed
VERIFICATION:- SUCCESSFUL
Verification Time: 3s
""".splitlines()
        results = parse_log_lines(lines, {}, {}, {})
        self.assertEqual([entry['thread_id'] for entry in results], [1, 0])
        self.assertEqual(results[0]['result']['harness'], 'second')
        self.assertEqual(results[0]['result']['result'], 'FAILED')
        self.assertEqual(results[0]['result']['n_failed_properties'], 1)
        self.assertEqual(results[1]['result']['harness'], 'first')
        self.assertEqual(results[1]['result']['result'], 'SUCCESSFUL')
        self.assertEqual(results[1]['result']['time'], '3s')

    def test_serial_autoharness_results_match_threaded_results(self):
        header = """Kani generated automatic harnesses for 1 functions
+--+
| Crate | Selected Function |
+==+
| core | example |
+--+
Kani did not generate automatic harnesses for 0 functions
+--+
| Crate | Skipped Function | Reason |
+==+
+--+
"""
        metadata = {'example': {
            'crate': 'core', 'function': 'example', 'target_safeness': 'safe',
            'public_target': True, 'file_name': 'example.rs'}}
        for contract in ['', "'s contract"]:
            with self.subTest(contract=contract):
                start = (f'Autoharness: Checking function example{contract} '
                         'against all possible inputs...\n')
                result = ('VERIFICATION RESULT:\n ** 0 of 2 failed\n'
                          'VERIFICATION:- SUCCESSFUL\nVerification Time: 1s\n')
                serial = parse_log_lines(
                    (header + start + result).splitlines(), {}, metadata, {})
                threaded = parse_log_lines(
                    (header + 'Thread 0: ' + start + 'Thread 0:\n' + result)
                    .splitlines(), {}, metadata, {})
                self.assertEqual(serial, threaded)
                self.assertEqual(len(serial), 1)
                self.assertTrue(serial[0]['result']['is_autoharness'])
                self.assertEqual(serial[0]['result']['with_contract'],
                                 bool(contract))

    def test_incomplete_serial_harness_is_rejected(self):
        with self.assertRaises(AssertionError):
            parse_log_lines(['Checking harness incomplete...'], {}, {}, {})


if __name__ == '__main__':
    unittest.main()
