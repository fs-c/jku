import unittest
from a9_ex2 import Time


class TestTime(unittest.TestCase):
    def test_time_initialization(self):
        """Test that time initializes correctly."""
        # Valid initialization
        t = Time(12, 30, 45)
        self.assertEqual(t.hours, 12)
        self.assertEqual(t.minutes, 30)
        self.assertEqual(t.seconds, 45)
        # Invalid initialization: hours out of range
        with self.assertRaises(ValueError):
            Time(24, 0, 0)
        # Invalid initialization: minutes out of range
        with self.assertRaises(ValueError):
            Time(12, 60, 0)
        # Invalid initialization: seconds out of range
        with self.assertRaises(ValueError):
            Time(12, 0, 60)
        # Invalid initialization: negative values
        with self.assertRaises(ValueError):
            Time(-1, 0, 0)

    def test_time_string_representation(self):
        """Test __str__ and __repr__ methods."""
        t = Time(5, 7, 9)
        self.assertEqual(str(t), "05:07:09")
        self.assertEqual(repr(t), "Time(hours=5, minutes=7, seconds=9)")

    def test_time_equality(self):
        """Test __eq__ method."""
        t1 = Time(12, 0, 0)
        t2 = Time(12, 0, 0)
        t3 = Time(13, 0, 0)
        self.assertEqual(t1, t2)
        self.assertNotEqual(t1, t3)

    def test_time_comparison(self):
        """Test __lt__ method."""
        t1 = Time(10, 0, 0)
        t2 = Time(11, 0, 0)
        self.assertTrue(t1 < t2)
        self.assertFalse(t2 < t1)
        self.assertFalse(t1 < t1)

    def test_time_addition(self):
        """Test addition with another Time object."""
        t1 = Time(1, 30, 15)
        t2 = Time(2, 45, 50)
        t3 = t1 + t2
        self.assertEqual(t3, Time(4, 16, 5))
        # Test addition resulting in overflow
        with self.assertRaises(ValueError):
            Time(23, 59, 59) + Time(0, 0, 1)

    def test_time_addition_seconds(self):
        """Test addition with seconds (integer)."""
        t1 = Time(1, 30, 15)
        t2 = t1 + 5000
        self.assertEqual(t2, Time(2, 53, 35))
        # Test addition resulting in overflow
        with self.assertRaises(ValueError):
            Time(23, 59, 59) + 1

    def test_time_reverse_addition(self):
        """Test reverse addition with seconds."""
        t1 = Time(1, 30, 15)
        t2 = 3600 + t1
        self.assertEqual(t2, Time(2, 30, 15))
        # Test reverse addition resulting in overflow
        with self.assertRaises(ValueError):
            86400 + t1  # 86400 seconds is 24 hours

    def test_time_subtraction(self):
        """Test subtraction with another Time object."""
        t1 = Time(2, 45, 50)
        t2 = Time(1, 30, 15)
        diff = t1 - t2
        self.assertEqual(diff, 4535)  # Difference in seconds
        # Subtracting larger time from smaller time
        diff = t2 - t1
        self.assertEqual(diff, -4535)

    def test_time_subtraction_seconds(self):
        """Test subtraction with seconds (integer)."""
        t1 = Time(2, 45, 50)
        t2 = t1 - 5000
        self.assertEqual(t2, Time(1, 22, 30))
        # Test subtraction resulting in negative time
        with self.assertRaises(ValueError):
            Time(0, 0, 10) - 20

    def test_time_error_handling(self):
        """Test error handling for invalid operations."""
        # Comparing with invalid type
        t1 = Time(1, 34, 40)
        self.assertEqual(t1.__lt__('1:00:00'), NotImplemented)

    def test_time_int_conversion(self):
        """Test conversion to total seconds."""
        t = Time(1, 30, 15)
        total_seconds = int(t)
        self.assertEqual(total_seconds, 5415)


if __name__ == '__main__':
    unittest.main()
