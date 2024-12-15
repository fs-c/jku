import unittest
import numpy as np
from a10_ex4 import one_hot_encoding

class TestOneHotEncoding(unittest.TestCase):
    
    def test_valid_strings(self):
        """Test one-hot encoding for a 1D array of strings."""
        arr = np.array(["a", "a", "b", "c"])
        result = one_hot_encoding(arr)
        expected = np.array([
            [1., 0., 0.],
            [1., 0., 0.],
            [0., 1., 0.],
            [0., 0., 1.]
        ])
        np.testing.assert_array_equal(result, expected, "The one-hot encoding for strings is incorrect.")
    
    def test_valid_numbers(self):
        """Test one-hot encoding for a 1D array of numbers."""
        arr = np.array([10, 5, 15, 20])
        result = one_hot_encoding(arr)
        expected = np.array([
            [0., 1., 0., 0.],
            [1., 0., 0., 0.],
            [0., 0., 1., 0.],
            [0., 0., 0., 1.]
        ])
        np.testing.assert_array_equal(result, expected, "The one-hot encoding for numbers is incorrect.")

    def test_single_value(self):
        """Test one-hot encoding for a 1D array with a single unique value."""
        arr = np.array([3, 3, 3, 3])
        result = one_hot_encoding(arr)
        expected = np.array([
            [1.],
            [1.],
            [1.],
            [1.]
        ])
        np.testing.assert_array_equal(result, expected, "The one-hot encoding for a single value is incorrect.")
    
    def test_empty_array(self):
        """Test one-hot encoding for an empty array."""
        arr = np.array([])
        result = one_hot_encoding(arr)
        expected = np.zeros((0, 0))
        np.testing.assert_array_equal(result, expected, "The one-hot encoding for an empty array is incorrect.")

    def test_invalid_2d_array(self):
        """Test for a non-1D input, should raise ValueError."""
        arr = np.array([[1, 2], [3, 4]])
        with self.assertRaises(ValueError) as context:
            one_hot_encoding(arr)
        self.assertEqual(str(context.exception), "The function can work for 1D matrices, not 2D", "Error message is incorrect.")

    def test_non_numeric_strings(self):
        """Test for non-numeric string array."""
        arr = np.array(["apple", "banana", "orange", "apple"])
        result = one_hot_encoding(arr)
        expected = np.array([
            [1., 0., 0.],
            [0., 1., 0.],
            [0., 0., 1.],
            [1., 0., 0.]
        ])
        np.testing.assert_array_equal(result, expected, "The one-hot encoding for non-numeric strings is incorrect.")

    def test_sorted_unique_values(self):
        """Test to ensure unique values are sorted."""
        arr = np.array([3, 2, 1, 2, 1])
        result = one_hot_encoding(arr)
        expected = np.array([
            [0., 0., 1.],  # 3 -> 2nd index
            [0., 1., 0.],  # 2 -> 1st index
            [1., 0., 0.],  # 1 -> 0th index
            [0., 1., 0.],  # 2 -> 1st index
            [1., 0., 0.]   # 1 -> 0th index
        ])
        np.testing.assert_array_equal(result, expected, "The one-hot encoding did not consider sorted unique values.")
    
    def test_large_array(self):
        """Test one-hot encoding for a large array with many unique values."""
        arr = np.array([i for i in range(100)])
        result = one_hot_encoding(arr)
        expected = np.eye(100)  # Identity matrix, as each element is unique
        np.testing.assert_array_equal(result, expected, "The one-hot encoding for a large array is incorrect.")

if __name__ == '__main__':
    unittest.main()
