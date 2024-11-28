import unittest
from a7_ex3 import file_statistics

class TestFileStatistics(unittest.TestCase):

    def setUp(self):
        """Set up test files and expected results."""
        self.test_cases = [
            # Format: (file_path, encoding, expected_output)
            ('a7_ex3_cp1252.txt', 'CP1252', (74, 8, 22, ['.', ':', 'é', ',', 'ç', ',', 'ñ', ',', 'ü', ',', 'ß', '.', '.'])),
            ('a7_ex3_utf8.txt', 'utf-8', (102, 5, 25, ['-', '.', '😊', '-', '你', '好', 'Д', 'о', 'б', 'р', 'ы', 'й', 'д', 'е', 'н', 'ь', '.', '.'])),
            ('a7_ex3_utf8.txt', 'CP1252', (102, 6, 26, ['-', '.', 'ð', 'Ÿ', '˜', 'Š', '-', 'ä', '½', 'å', '¥', '½', 'Ð', '”', 'Ð', '¾', 'Ð', '±', 'Ñ', '€', 'Ñ', '‹', 'Ð', 'Ð', '´', 'Ð', 'µ', 'Ð', '½', 'Ñ', 'Œ', '.', '.'])),
        ]

    def test_file_statistics(self):
        """Test file_statistics with various encodings and inputs."""
        for file_path, encoding, expected_output in self.test_cases:
            with self.subTest(file=file_path, encoding=encoding):
                result = file_statistics(file_path, encoding=encoding)
                self.assertEqual(result, expected_output, f"Failed for {file_path} with encoding {encoding}.")

if __name__ == '__main__':
    unittest.main()
