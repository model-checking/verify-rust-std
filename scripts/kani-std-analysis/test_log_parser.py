import unittest

from log_parser import parse_log_lines


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
