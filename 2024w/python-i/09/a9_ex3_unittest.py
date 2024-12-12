import unittest
import os
import tempfile

from a9_ex3 import Reader

class TestReader(unittest.TestCase):
    def setUp(self):
        # Create a temporary file with known content
        self.temp_file = tempfile.NamedTemporaryFile(delete=False)
        self.data = b'abcdefghijklmnopqrstuvwxyz'  # 26 bytes
        self.temp_file.write(self.data)
        self.temp_file.close()  # Close so it can be read
        self.reader = Reader(self.temp_file.name)
    
    def tearDown(self):
        # Clean up the temporary file
        self.reader.close()
        os.unlink(self.temp_file.name)

    def test_invalid_path(self):
        """Test that ValueError is raised when path is not a file."""
        with self.assertRaises(ValueError):
            Reader("non_existent_file.txt")

    def test_valid_initialization(self):
        """Test that Reader initializes correctly with a valid file."""
        self.assertEqual(len(self.reader), len(self.data))

    def test_len(self):
        """Test that __len__ returns the correct file size."""
        self.assertEqual(len(self.reader), 26)

    def test_getitem_positive_index(self):
        """Test that __getitem__ returns the correct byte at a given positive index."""
        for i in range(26):
            expected_byte = self.data[i:i+1]
            self.assertEqual(self.reader[i], expected_byte)

    def test_getitem_negative_index(self):
        """Test that __getitem__ returns the correct byte at a given negative index."""
        for i in range(1, len(self.data)+1):
            expected_byte = bytes([self.data[-i]])
            self.assertEqual(self.reader[-i], expected_byte)

    def test_getitem_index_out_of_range_positive(self):
        """Test that __getitem__ raises IndexError when index is out of range (positive index)."""
        with self.assertRaises(IndexError):
            self.reader[26]  # Index equal to size
        with self.assertRaises(IndexError):
            self.reader[100]  # Index beyond size

    def test_getitem_index_out_of_range_negative(self):
        """Test that __getitem__ raises IndexError when index is out of range (negative index)."""
        with self.assertRaises(IndexError):
            self.reader[-27]  # Index beyond negative size
        with self.assertRaises(IndexError):
            self.reader[-100]  # Index beyond negative size

    def test_getitem_invalid_index_type(self):
        """Test that __getitem__ raises TypeError when index is not an integer."""
        with self.assertRaises(TypeError):
            self.reader["0"]
        with self.assertRaises(TypeError):
            self.reader[2.5]
        with self.assertRaises(TypeError):
            self.reader[None]
        with self.assertRaises(TypeError):
            self.reader[[1]]

    def test_close_method(self):
        """Test that close() closes the file and subsequent operations fail."""
        self.reader.close()
        with self.assertRaises(ValueError):
            self.reader[0]  # Should raise ValueError: I/O operation on closed file

    def test_multiple_instances(self):
        """Test that multiple Reader instances can be used independently."""
        reader2 = Reader(self.temp_file.name)
        self.assertEqual(self.reader[0], reader2[0])
        self.reader.close()
        # reader2 should still work
        self.assertEqual(reader2[1], self.data[1:2])
        reader2.close()

    def test_seek_and_read(self):
        """Test that the file position is set correctly and bytes are read correctly."""
        indices = [0, 5, 10, -1, -5]
        for idx in indices:
            expected_byte = self.data[idx:idx+1] if idx >= 0 else bytes([self.data[idx]])
            self.assertEqual(self.reader[idx], expected_byte)

if __name__ == '__main__':
    unittest.main()
