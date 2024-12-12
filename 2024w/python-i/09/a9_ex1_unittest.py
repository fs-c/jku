import unittest
from a9_ex1 import Vector



class TestVector(unittest.TestCase):
    def test_vector_initialization(self):
        """Test that the vector initializes correctly."""
        # Valid initialization
        v = Vector([1, 2, 3])
        self.assertEqual(v.components, (1, 2, 3))
        # Invalid initialization
        with self.assertRaises(TypeError):
            Vector([1, 'a', 3])

    def test_vector_equality(self):
        """Test that equality works as expected."""
        v1 = Vector([1, 2, 3])
        v2 = Vector([1, 2, 3])
        v3 = Vector([4, 5, 6])
        self.assertEqual(v1, v2)
        self.assertNotEqual(v1, v3)

    def test_vector_addition(self):
        """Test vector addition."""
        v1 = Vector([1, 2, 3])
        v2 = Vector([4, 5, 6])
        v3 = v1 + v2
        self.assertEqual(v3, Vector([5, 7, 9]))
        # Test addition with vectors of different lengths
        v_short = Vector([1, 2])
        with self.assertRaises(TypeError):
            v1 + v_short

    def test_vector_subtraction(self):
        """Test vector subtraction."""
        v1 = Vector([5, 7, 9])
        v2 = Vector([1, 2, 3])
        v3 = v1 - v2
        self.assertEqual(v3, Vector([4, 5, 6]))
        # Test subtraction with vectors of different lengths
        v_short = Vector([1, 2])
        with self.assertRaises(TypeError):
            v1 - v_short

    def test_vector_scalar_multiplication(self):
        """Test scalar multiplication."""
        v1 = Vector([1, 2, 3])
        v2 = v1 * 3
        self.assertEqual(v2, Vector([3, 6, 9]))
        v3 = 2 * v1
        self.assertEqual(v3, Vector([2, 4, 6]))
        # Test multiplication with a non-scalar
        with self.assertRaises(TypeError):
            v1 * 'a'

    def test_vector_negation(self):
        """Test unary negation."""
        v1 = Vector([1, -2, 3])
        v2 = -v1
        self.assertEqual(v2, Vector([-1, 2, -3]))

    def test_vector_length(self):
        """Test the length (dimension) of the vector."""
        v1 = Vector([1, 2, 3])
        self.assertEqual(len(v1), 3)
        v2 = Vector([])
        self.assertEqual(len(v2), 0)

    def test_vector_indexing(self):
        """Test accessing components via indexing."""
        v1 = Vector([10, 20, 30])
        self.assertEqual(v1[0], 10)
        self.assertEqual(v1[1], 20)
        self.assertEqual(v1[2], 30)
        # Test negative indexing
        self.assertEqual(v1[-1], 30)
        self.assertEqual(v1[-2], 20)
        self.assertEqual(v1[-3], 10)
        # Test out-of-range indexing
        with self.assertRaises(IndexError):
            _ = v1[3]
        # Test invalid index type
        with self.assertRaises(TypeError):
            _ = v1['a']

    def test_vector_iteration(self):
        """Test that we can iterate over the components."""
        v1 = Vector([1, 2, 3])
        components = []
        for component in v1:
            components.append(component)
        self.assertEqual(components, [1, 2, 3])

    def test_vector_error_handling(self):
        """Test that errors are raised appropriately."""
        v1 = Vector([1, 2, 3])
        # Test addition with invalid type
        with self.assertRaises(TypeError):
            v1 + 5
        # Test subtraction with invalid type
        with self.assertRaises(TypeError):
            v1 - [1, 2, 3]
        # Test multiplication with invalid type
        with self.assertRaises(TypeError):
            v1 * Vector([1, 2, 3])

    def test_vector_str_repr(self):
        """Test string representations."""
        v1 = Vector([1, 2, 3])
        self.assertEqual(str(v1), "<1, 2, 3>")
        self.assertEqual(repr(v1), "Vector((1, 2, 3))")


if __name__ == '__main__':
    unittest.main()
