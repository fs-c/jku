import unittest
import os
import pickle
import platform
import shutil

from a7_ex4 import analyze_and_append_logs

class TestAnalyzeAndAppendLogs(unittest.TestCase):

    def setUp(self):
        """ Set up the test environment. """
        self.input_directory = "a7_ex4_logs"
        self.output_file = "test_error_data.pkl"
        self.expected_output_file = "a7_ex4_expected_error_data.pkl"
        self.is_windows = platform.system().lower() == "windows"

        # Ensure the test environment is clean before running
        if os.path.exists(self.output_file):
            os.remove(self.output_file)

    def tearDown(self):
        """ Clean up the test environment. """
        if os.path.exists(self.output_file):
            os.remove(self.output_file)

    def convert_expected_paths(self, expected_data):
        """ Convert paths in expected data to match the current operating system. """
        if self.is_windows:
            return {
                key.replace("/", "\\"): value
                for key, value in expected_data.items()
            }
        return expected_data

    def test_analyze_and_append_logs(self):
        """ Test the analyze_and_append_logs function with the provided example folder. """
        # Run the function
        analyze_and_append_logs(self.input_directory, self.output_file)

        # Load the generated output data
        with open(self.output_file, "rb") as f:
            generated_data = pickle.load(f)

        # Load the expected output data
        with open(self.expected_output_file, "rb") as f:
            expected_data = pickle.load(f)

        # Convert expected paths if on Windows
        expected_data = self.convert_expected_paths(expected_data)

        # Assert the generated data matches the expected data
        self.assertEqual(generated_data, expected_data, "Generated data does not match expected data.")

if __name__ == "__main__":
    unittest.main()
