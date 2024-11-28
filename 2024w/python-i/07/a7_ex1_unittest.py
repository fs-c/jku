import unittest
import tempfile
import os
from a7_ex1 import analyze_log_file

class TestAnalyzeLogFile(unittest.TestCase):

    def setUp(self):
        self.maxDiff = None
        # Define test cases as (filename, keyword, expected_file, output_file)
        self.test_cases = [
            ("a7_ex1.log", "ERROR", "a7_ex1_ERROR_expected.log", "a7_ex1_ERROR.log"),
            ("a7_ex1.log", "WARNING", "a7_ex1_WARNING_expected.log", "a7_ex1_WARNING.log")
        ]

    def test_analyze_log_file(self):
        """Test analyze_log_file with different keywords and compare output files using subTest."""
        for filename, keyword, expected_file, output_filename in self.test_cases:
            with self.subTest(filename=filename, keyword=keyword):
                # Run the analyze_log_file function and get the count
                count = analyze_log_file(filename, keyword)

                # Verify the count matches the expected number of lines in the expected file
                with open(expected_file, "r") as f:
                    expected_lines = [line.strip() for line in f.readlines()]
                self.assertEqual(count, len(expected_lines))

                # Check if the generated output file matches the expected file content
                with open(output_filename, "r") as f:
                    output_content = [line.strip() for line in f.readlines()]
                self.assertEqual(output_content, expected_lines)

                os.remove(output_filename)
    
    def test_missing_file(self):
        """Test handling of a missing file."""
        count = analyze_log_file("missing_file.txt", "ERROR")
        self.assertIsNone(count)  # Should return None for missing file

    def test_output_filename_format(self):
        """Test that output filename matches the expected format when input file does not end in `.log`."""
        # Create a temporary file with a non-.log extension
        with tempfile.NamedTemporaryFile(suffix=".txt", mode="w", delete=False) as temp_file:
            temp_file.write("Sample line with ERROR\nAnother line without\nYet another ERROR line")
            temp_filename = temp_file.name

        keyword = "ERROR"
        expected_output_filename = f"{os.path.splitext(temp_filename)[0]}_{keyword}.txt"
        
        try:
            # Run analyze_log_file and verify the output filename
            analyze_log_file(temp_filename, keyword)
            self.assertTrue(os.path.exists(expected_output_filename), "Output file not created as expected")
        except:
            os.chdir(tempfile.tempdir)
            analyze_log_file(temp_filename, keyword)
            self.assertTrue(os.path.exists(expected_output_filename), "Output file not created as expected")
        finally:
            # Clean up the temporary files
            os.remove(temp_filename)
            if os.path.exists(expected_output_filename):
                os.remove(expected_output_filename)

if __name__ == "__main__":
    unittest.main()
