import unittest
import numpy as np
from a10_ex3 import convolution
class TestConvolution(unittest.TestCase):

    def test_basic_convolution(self):
        matrix = np.array([[1, 2, 3], [4, 5, 6], [7, 8, 9]], dtype=float)
        kernel = np.array([[0, 1, 0], [1, 1, 1], [0, 1, 0]], dtype=float)

        expected_output = np.array([[ 7, 11, 11],
                                    [17, 25, 23],
                                    [19, 29, 23]], dtype=float)

        output = convolution(matrix, kernel)
        np.testing.assert_array_equal(output, expected_output)

    def test_convolution_with_padding(self):
        # Using a 3x3 matrix
        matrix = np.array([[1, 2, 3],
                           [4, 5, 6],
                           [7, 8, 9]], dtype=float)

        # 3x3 kernel
        kernel = np.array([[1, 0, -1],
                           [1, 0, -1],
                           [1, 0, -1]], dtype=float)

        # Apply padding of 1
        expected_output = np.array([[ -5,   -4,  5],
                                    [ -12,   -6, 12],
                                    [ -11,   -4, 11]], dtype=float)

        # Perform convolution
        output = convolution(matrix, kernel, padding=1)
        np.testing.assert_array_equal(output, expected_output)

    def test_convolution_with_different_kernel_size(self):
        matrix = np.array([[1, 2, 3], [4, 5, 6], [7, 8, 9]], dtype=float)
        kernel = np.array([[1, 2, 1], [0, 0, 0], [-1, -2, -1]], dtype=float)

        # Manually computed expected output
        expected_output = np.array([[-13, -20,  -17],
                                    [-18, -24,  -18],
                                    [ 13,  20, 17]], dtype=float)

        output = convolution(matrix, kernel)
        np.testing.assert_array_equal(output, expected_output)

    def test_convolution_with_large_kernel(self):
        matrix = np.array([[1, 2, 3, 4, 5],
                            [6, 7, 8, 9, 10],
                            [11, 12, 13, 14, 15],
                            [16, 17, 18, 19, 20],
                            [21, 22, 23, 24, 25]], dtype=float)
                            
        kernel = np.zeros((5, 5), dtype=float)
        kernel[2, 2] = -1

        # Manually computed expected output
        expected_output = matrix * -1

        output = convolution(matrix, kernel)
        np.testing.assert_array_equal(output, expected_output)

    def test_convolution_with_invalid_kernel(self):
        matrix = np.array([[1, 2], [3, 4]], dtype=float)
        kernel = np.array([[1, 0], [0, 0], [0, 1]], dtype=float)  # Non-square kernel

        with self.assertRaises(AssertionError):
            convolution(matrix, kernel)

    def test_convolution_with_invalid_matrix(self):
        matrix = np.array([[1, 2]], dtype=float)  # Matrix is smaller than the kernel
        kernel = np.array([[1, 0], [0, 1]], dtype=float)

        with self.assertRaises(AssertionError):
            convolution(matrix, kernel)


if __name__ == "__main__":
    unittest.main()