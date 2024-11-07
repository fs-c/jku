import sys
import unittest
from io import StringIO
from a5_ex1 import analyze_and_update_collection  

class TestAnalyzeAndUpdateCollection(unittest.TestCase):

    def setUp(self):
        self.items1 = [1, 2, 4, 5]
        self.items2 = [2, 4, 6]
        self.items_with_string = [str(i) for i in self.items1]
        self.empty_list = []

        self.test_cases = [
            # (my_list, my_set, expected_console_output, expected_return_value)
            (self.items1, None, "The last element of my_list is 5\n", {3}),
            (self.items2, None, "The last element of my_list is 6\n", {4}),
            (self.items1, set(self.items1), "The last element of my_list is 5\nmy_set and my_list contain the same elements\n", {1, 2, 4, 5, 3}),
            (self.items1, set(self.items2), "The last element of my_list is 5\n", {2, 4, 6, 3}),
        ]

    def test_analyze_and_update_collection(self):
        for my_list, my_set, expected_console_output, expected_return_value in self.test_cases:
            with self.subTest(my_list=my_list, my_set=my_set):
                # Capture the console output
                captured_output = StringIO()
                original_stdout = sys.stdout  # Save original stdout
                sys.stdout = captured_output

                try:
                    # Call the function and get result
                    result = analyze_and_update_collection(my_list, my_set=my_set)
                finally:
                    # Restore original stdout
                    sys.stdout = original_stdout

                # Check the function return value
                self.assertEqual(result, expected_return_value)

                # Check the console output
                self.assertEqual(captured_output.getvalue(), expected_console_output)

    def test_empty_list(self):
        # Test for empty list, which should raise an AssertionError
        with self.assertRaises(AssertionError) as cm:
            analyze_and_update_collection(self.empty_list)
        self.assertEqual(str(cm.exception), "Aborted as my_list must not be empty")

    def test_non_integer_list(self):
        # Test for list with non-integer values, which should raise an AssertionError
        with self.assertRaises(AssertionError) as cm:
            analyze_and_update_collection(self.items_with_string)
        self.assertEqual(str(cm.exception), "Aborted as my_list contains non integer values")

if __name__ == '__main__':
    unittest.main()
