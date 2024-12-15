import unittest
import numpy as np
from a10_ex1 import matrix_operations  # Replace with the actual filename of your script

class TestMatrixOperations(unittest.TestCase):

    def test_positive_size(self):
        """Test that size must be greater than 0"""
        with self.assertRaises(AssertionError):
            matrix_operations(0)

    def test_output_shapes(self):
        """Test the shapes of the output arrays"""
        for size in [2, 4, 5, 7]:
            with self.subTest(size=size):
                outputs = matrix_operations(size)
                axis_0_sum, axis_01_sum, axis_all_sum, max_index, min_index, border_sum, normed_array = outputs

                # Shape of axis_0_sum should be (size, size)
                self.assertEqual(axis_0_sum.shape, (size, size))

                # Shape of axis_01_sum should be (size,)
                self.assertEqual(axis_01_sum.shape, (size,))

                # axis_all_sum should be a scalar
                self.assertIsInstance(axis_all_sum, np.integer)

                # max_index and min_index should be tuples of length 3
                self.assertIsInstance(max_index, tuple)
                self.assertEqual(len(max_index), 3)
                self.assertIsInstance(min_index, tuple)
                self.assertEqual(len(min_index), 3)

                # normed_array should have size **size * size * size**
                self.assertEqual(normed_array.shape, (size**3,))

    def test_correct_normalization(self):
        """Test that the normalization of the array is correct"""
        for size in [3, 6, 8, 10]:
            with self.subTest(size=size):
                _, _, _, _, _, _, normed_array = matrix_operations(size)

                # Check if normalized values are in [0, 1]
                self.assertTrue(np.all(normed_array >= 0))
                self.assertTrue(np.all(normed_array <= 1))

    def test_border_sum(self):
        """Test the correctness of border sum computation"""
        for size in [3, 6, 10,11]:
            with self.subTest(size=size):
                np.random.seed(0)
                _, _, _, _, _, border_sum, _ = matrix_operations(size)

                # Manually calculate the border sum for a simple case
                np.random.seed(0)
                array = np.random.randint(0, 100, (size, size, size))
                manual_border_sum = (
                    np.sum(array[0, :, :]) + np.sum(array[-1, :, :]) +
                    np.sum(array[1:-1, 0, :]) + np.sum(array[1:-1, -1, :]) +
                    np.sum(array[1:-1, 1:-1, 0]) + np.sum(array[1:-1, 1:-1, -1])
                )

                self.assertEqual(border_sum, manual_border_sum)

    def test_max_min_indices(self):
        """Test the correctness of max and min indices"""
        for size in [4, 5, 7]:
            with self.subTest(size=size):
                np.random.seed(0)
                _, _, _, max_index, min_index, _, _ = matrix_operations(size)

                np.random.seed(0)
                array = np.random.randint(0, 100, (size, size, size))

                # Check if max_index corresponds to the maximum value
                self.assertEqual(array[max_index], np.max(array))

                # Check if min_index corresponds to the minimum value
                self.assertEqual(array[min_index], np.min(array))

    def test_sum_calculations(self):
        """Test the correctness of sum calculations"""
        for size in [3, 6, 9]:
            with self.subTest(size=size):
                np.random.seed(0)
                axis_0_sum, axis_01_sum, axis_all_sum, _, _, _, _ = matrix_operations(size)

                np.random.seed(0)
                array = np.random.randint(0, 100, (size, size, size))

                # Check axis 0 sum
                np.testing.assert_array_equal(axis_0_sum, np.sum(array, axis=0))

                # Check axis 0 and 1 sum
                np.testing.assert_array_equal(axis_01_sum, np.sum(array, axis=(0, 1)))

                # Check total sum
                self.assertEqual(axis_all_sum, np.sum(array))

    def test_large_size(self):
        """Test the function with larger sizes"""
        for size in [15, 20]:
            with self.subTest(size=size):
                outputs = matrix_operations(size)
                self.assertEqual(len(outputs), 7)  # Ensure all outputs are returned correctly

    def test_deterministic_behavior(self):
        """Test that the function produces deterministic results with the same seed"""
        for size in [5, 8]:
            with self.subTest(size=size):
                np.random.seed(0)
                result1 = matrix_operations(size)

                np.random.seed(0)
                result2 = matrix_operations(size)

                # Assert that results with the same seed are identical
                for r1, r2 in zip(result1, result2):
                    if isinstance(r1, np.ndarray):
                        np.testing.assert_array_equal(r1, r2)
                    else:
                        self.assertEqual(r1, r2)

if __name__ == '__main__':
    unittest.main()
