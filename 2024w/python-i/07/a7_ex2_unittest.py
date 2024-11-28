import unittest
import os
import shutil
import platform
from filecmp import dircmp

from a7_ex2 import organize_directory

class TestDirectoryOrganizer(unittest.TestCase):

    def setUp(self):
        self.maxDiff = None
        self.is_windows = platform.system().lower() == "windows"

    def test_organize_directory(self):
        """ 
        Test if the directory is correctly organized and matches the expected structure. 
        Test if the log file contains the correct move entries.
        """
        src_path = "a7_ex2_dir"
        dest_path = "a7_ex2_dir_organized"
        expected_path = "a7_ex2_expected"

        # Create expected log content based on the operating system
        if self.is_windows:
            expected_log_content = [
                "Copied 'a7_ex2_dir\\document1.txt' to 'a7_ex2_dir_organized\\txt\\document1.txt'",
                "Copied 'a7_ex2_dir\\document2.txt' to 'a7_ex2_dir_organized\\txt\\document2.txt'",
                "Copied 'a7_ex2_dir\\image1.jpg' to 'a7_ex2_dir_organized\\jpg\\image1.jpg'",
                "Copied 'a7_ex2_dir\\image2.jpg' to 'a7_ex2_dir_organized\\jpg\\image2.jpg'",
                "Copied 'a7_ex2_dir\\script1.py' to 'a7_ex2_dir_organized\\py\\script1.py'",
                "Copied 'a7_ex2_dir\\subdir1\\image3.jpg' to 'a7_ex2_dir_organized\\jpg\\image3.jpg'",
                "Copied 'a7_ex2_dir\\subdir2\\document3.txt' to 'a7_ex2_dir_organized\\txt\\document3.txt'",
                "Copied 'a7_ex2_dir\\subdir2\\script2.py' to 'a7_ex2_dir_organized\\py\\script2.py'"
            ]
        else:
            expected_log_content = [
                "Copied 'a7_ex2_dir/document1.txt' to 'a7_ex2_dir_organized/txt/document1.txt'",
                "Copied 'a7_ex2_dir/document2.txt' to 'a7_ex2_dir_organized/txt/document2.txt'",
                "Copied 'a7_ex2_dir/image1.jpg' to 'a7_ex2_dir_organized/jpg/image1.jpg'",
                "Copied 'a7_ex2_dir/image2.jpg' to 'a7_ex2_dir_organized/jpg/image2.jpg'",
                "Copied 'a7_ex2_dir/script1.py' to 'a7_ex2_dir_organized/py/script1.py'",
                "Copied 'a7_ex2_dir/subdir1/image3.jpg' to 'a7_ex2_dir_organized/jpg/image3.jpg'",
                "Copied 'a7_ex2_dir/subdir2/document3.txt' to 'a7_ex2_dir_organized/txt/document3.txt'",
                "Copied 'a7_ex2_dir/subdir2/script2.py' to 'a7_ex2_dir_organized/py/script2.py'"
            ]

        # Clean up previous test artifacts
        if os.path.exists(dest_path):
            shutil.rmtree(dest_path)
        if os.path.exists("move.log"):
            os.remove("move.log")

        # Run the function
        organize_directory(src_path)

        # Check if destination folder matches expected output
        self.assertTrue(os.path.exists(dest_path), "Organized directory not created.")
        self.assertTrue(self.compare_directories(dest_path, expected_path), 
                        "Organized directory structure/content does not match expected.")

        # Check log file content
        with open("move.log", "r", encoding="utf-8") as log_file:
            log_content = [line.strip() for line in log_file.readlines()]
        self.assertEqual(log_content, expected_log_content, "Log file content does not match expected moves.")

        # Clean up after tests
        if os.path.exists(dest_path):
            shutil.rmtree(dest_path)
        if os.path.exists("move.log"):
            os.remove("move.log")

    def test_missing_directory(self):
        """ Test if an error is logged when the source directory does not exist. """
        missing_path = "missing_dir"
        organize_directory(missing_path)
        
        # Check if the log file contains the correct error entry
        with open("move.log", "r", encoding="utf-8") as log_file:
            log_content = log_file.read().strip()
        self.assertEqual(log_content, f"Error: '{missing_path}' is not a valid directory.")

    def compare_directories(self, dir1, dir2):
        """ Helper method to compare two directories recursively. """
        dcmp = dircmp(dir1, dir2)
        if dcmp.left_only or dcmp.right_only or dcmp.diff_files:
            return False
        for sub_dcmp in dcmp.subdirs.values():
            if not self.compare_directories(sub_dcmp.left, sub_dcmp.right):
                return False
        return True


if __name__ == "__main__":
    unittest.main()
