import sys
import unittest
from io import StringIO
from a5_ex3 import safe_list_access 

class TestSafeListAccess(unittest.TestCase):

    def setUp(self):
        self.test_cases = [
            # (lst, index, expected_console_output, expected_return_value)
            ([10, 20, 30, 40], 1, "Operation completed\n", 20),
            ([10, 20, 30, 40], '1', "Converting Index to integer\nOperation completed\n", 20),
            ([10, 20, 30, 40], 'abc', "Converting Index to integer\nOperation completed\n", "Index cannot be converted to an integer"),
            ([10, 20, 30, 40], 5, "Operation completed\n", "Index out of range"),
            ([10, 20, 30, 40], '5', "Converting Index to integer\nOperation completed\n", "Index out of range"),
            (3, 1, "Operation completed\n", "First argument is not a list")
        ]

    def test_safe_list_access(self):
        for lst, index, expected_console_output, expected_return_value in self.test_cases:
            with self.subTest(lst=lst, index=index):
                # Capture the console output
                captured_output = StringIO()
                original_stdout = sys.stdout  # Save original stdout
                sys.stdout = captured_output

                try:
                    # Call the function and get result
                    result = safe_list_access(lst, index)
                finally:
                    # Restore original stdout
                    sys.stdout = original_stdout

                # Assert the function return value
                self.assertEqual(result, expected_return_value)

                # Assert the console output
                self.assertEqual(captured_output.getvalue(), expected_console_output)

if __name__ == '__main__':
    unittest.main()
