import unittest
import numpy as np
from a10_ex2 import elements_wise

class TestElementsWise(unittest.TestCase):

    def test_basic_function(self):
        def func(x):
            return x * x + 3 * x + 2
        
        a = np.array([1, 2, 3], dtype=float)
        expected = np.array([6, 12, 20], dtype=float)
        
        elements_wise(a, func)
        np.testing.assert_array_equal(a, expected)
    
    def test_reshape_function(self):
        def func(x):
            return x * x + 3 * x + 2
        
        a = np.array(range(9), dtype=float).reshape(3, 3)
        expected = np.array([2, 6, 12, 20, 30, 42, 56, 72, 90], dtype=float).reshape(3, 3)
        
        elements_wise(a, func)
        np.testing.assert_array_equal(a, expected)

    def test_empty_array(self):
        def func(x):
            return x * x + 3 * x + 2
        
        a = np.array([], dtype=float)
        expected = np.array([], dtype=float)
        
        elements_wise(a, func)
        np.testing.assert_array_equal(a, expected)

    def test_single_element(self):
        def func(x):
            return x * x + 3 * x + 2
        
        a = np.array([4], dtype=float)
        expected = np.array([30], dtype=float)  # 4^2 + 3(4) + 2 = 30
        
        elements_wise(a, func)
        np.testing.assert_array_equal(a, expected)

    def test_3d_array(self):
        def func(x):
            return x * x + 3 * x + 2
        
        a = np.array(range(12), dtype=float).reshape(2, 2, 3)
        expected = np.array([2, 6, 12, 20, 30, 42, 56, 72, 90, 110, 132, 156], dtype=float).reshape(2, 2, 3)
        
        elements_wise(a, func)
        np.testing.assert_array_equal(a, expected)

    def test_large_array(self):
        def func(x):
            return x * x + 3 * x + 2
        
        a = np.array(range(1000), dtype=float)
        elements_wise(a, func)  # Test if it runs without errors

    def test_in_place_modification(self):
        def func(x):
            return x * x + 3 * x + 2
        
        a = np.array([1, 2, 3], dtype=float)
        original_a = a.copy()  # Save a copy to check if in-place modification happens
        elements_wise(a, func)
        
        # Check that the array has been modified in-place
        self.assertTrue(np.all(a != original_a))

if __name__ == "__main__":
    unittest.main()
