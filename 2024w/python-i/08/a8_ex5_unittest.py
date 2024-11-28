import unittest

from a8_ex2 import Electric_Circuits
from a8_ex3 import Energy
from a8_ex5 import Power

class TestPower(unittest.TestCase):

    def test_init_valid(self):
        p = Power(1.0, 2.0, 3, 0.5, 20.0)
        self.assertEqual(p.x, 1.0)
        self.assertEqual(p.y, 2.0)
        self.assertEqual(p.z, 3)
        self.assertEqual(p.current, 0.5)
        self.assertEqual(p.resistance, 20.0)
        self.assertEqual(p.time, 1)

    def test_to_string(self):
        p = Power(1.0, 2.0, 3, 0.5, 20.0)
        expected = "Power: x=1.0, y=2.0, z=3, current=0.5, resistance=20.0, time=1"
        self.assertEqual(p.to_string(), expected)

    def test_measure(self):
        p = Power(0.0, 0.0, 0, 0.5, 20.0)
        expected_power = (0.5 ** 2) * 20.0 * 1  # 0.25 * 20 * 1 = 5.0
        self.assertEqual(p.measure(), expected_power)

    def test_inheritance(self):
        p = Power(1.0, 2.0, 3, 0.5, 20.0)
        self.assertIsInstance(p, Power)
        self.assertIsInstance(p, Energy)
        self.assertIsInstance(p, Electric_Circuits)

    def test_attribute_modification(self):
        p = Power(1.0, 2.0, 3, 0.5, 20.0)
        p.current = 1.0
        p.resistance = 10.0
        p.time = 2  # Should affect measure calculation
        expected_power = (1.0 ** 2) * 10.0 * 2  # 1 * 10 * 2 = 20.0
        self.assertEqual(p.measure(), expected_power)
        expected_string = "Power: x=1.0, y=2.0, z=3, current=1.0, resistance=10.0, time=2"
        self.assertEqual(p.to_string(), expected_string)

    def test_negative_values(self):
        p = Power(-1.0, -2.0, -3, -0.5, -20.0)
        expected_power = ((-0.5) ** 2) * (-20.0) * 1  # 0.25 * -20 * 1 = -5.0
        self.assertEqual(p.measure(), -5.0)
        expected_string = "Power: x=-1.0, y=-2.0, z=-3, current=-0.5, resistance=-20.0, time=1"
        self.assertEqual(p.to_string(), expected_string)

    def test_zero_values(self):
        p = Power(0.0, 0.0, 0, 0.0, 0.0)
        expected_power = 0.0
        self.assertEqual(p.measure(), expected_power)
        expected_string = "Power: x=0.0, y=0.0, z=0, current=0.0, resistance=0.0, time=1"
        self.assertEqual(p.to_string(), expected_string)

    def test_large_values(self):
        p = Power(1e10, 2e10, 3e10, 1e5, 2e5)
        expected_power = (1e5) ** 2 * 2e5 * 1  # 1e10 * 2e5 = 2e15
        self.assertEqual(p.measure(), 2e15)

    def test_measure_with_time_attribute(self):
        p = Power(1.0, 2.0, 3, 0.5, 20.0)
        self.assertEqual(p.time, 1)
        expected_power = (0.5 ** 2) * 20.0 * p.time  # Should be 5.0
        self.assertEqual(p.measure(), expected_power)
        # Modify time and see if measure changes
        p.time = 2
        expected_power = (0.5 ** 2) * 20.0 * p.time  # Should be 10.0
        self.assertEqual(p.measure(), expected_power)

    def test_invalid_measure_calculation(self):
        p = Power(1.0, 2.0, 3, "invalid", 20.0)
        with self.assertRaises(TypeError):
            p.measure()
        p = Power(1.0, 2.0, 3, 0.5, "invalid")
        with self.assertRaises(TypeError):
            p.measure()

    def test_to_string_with_invalid_types(self):
        p = Power("x_value", "y_value", "z_value", "current_value", "resistance_value")
        expected = "Power: x=x_value, y=y_value, z=z_value, current=current_value, resistance=resistance_value, time=1"
        self.assertEqual(p.to_string(), expected)

    def test_time_argument_override(self):
        p = Power(1.0, 2.0, 3, 0.5, 20.0)
        p.time = 5  # Attempt to change time
        self.assertEqual(p.time, 5)
        expected_power = (0.5 ** 2) * 20.0 * 5  # Should be 12.5
        self.assertEqual(p.measure(), expected_power)

    def test_measure_with_negative_resistance(self):
        p = Power(1.0, 2.0, 3, 0.5, -20.0)
        expected_power = (0.5 ** 2) * (-20.0) * 1  # 0.25 * -20 * 1 = -5.0
        self.assertEqual(p.measure(), -5.0)

if __name__ == "__main__":
    unittest.main()

