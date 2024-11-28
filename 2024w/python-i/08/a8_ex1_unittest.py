import unittest
from io import StringIO
import sys
from a8_ex1 import Voltage


class TestVoltage(unittest.TestCase):

    def test_init(self):
        v = Voltage(5.0, 10.0)
        self.assertEqual(v.current, 5.0)
        self.assertEqual(v.resistance, 10.0)

    def test_volt(self):
        v = Voltage(5.0, 10.0)
        self.assertEqual(v.volt(), 50.0)

    def test_print(self):
        v = Voltage(-5.0, 10.0)
        captured_output = StringIO()
        sys.stdout = captured_output
        v.print()
        sys.stdout = sys.__stdout__
        self.assertEqual(captured_output.getvalue().strip(), "-5.0 amps + 10.0 ohms")

    def test_increase_resistance_valid(self):
        v = Voltage(5.0, 10.0)
        v.increase_resistance(5.0)
        self.assertEqual(v.resistance, 15.0)

    def test_increase_resistance_invalid_type(self):
        v = Voltage(5.0, 10.0)
        with self.assertRaises(TypeError) as context:
            v.increase_resistance("invalid")
        self.assertIn('Please provide float value instead of str', str(context.exception))

    def test_add_all_valid(self):
        v1 = Voltage(5.0, 10.0)
        v2 = Voltage(5.0, 20.0)
        v3 = Voltage(5.0, 30.0)
        result = Voltage.add_all(v1, v2, v3)
        self.assertEqual(result.current, 5.0)
        self.assertEqual(result.resistance, 60.0)

    def test_add_all_different_currents(self):
        v1 = Voltage(5.0, 10.0)
        v2 = Voltage(10.0, 20.0)
        with self.assertRaises(ValueError) as context:
            Voltage.add_all(v1, v2)
        self.assertEqual(str(context.exception), 'The current must be equal')

    def test_add_all_invalid_object(self):
        v1 = Voltage(5.0, 10.0)
        with self.assertRaises(TypeError) as context:
            Voltage.add_all(v1, "invalid")
        self.assertEqual(str(context.exception), "Can only add objects of type 'Voltage'")

    def test_negative_values(self):
        v = Voltage(-5.0, -10.0)
        self.assertEqual(v.volt(), 50.0)
        self.assertEqual(v.current, -5.0)
        self.assertEqual(v.resistance, -10.0)


    def test_attribute_modification(self):
        v = Voltage(5.0, 10.0)
        v.current = 10.0
        v.resistance = 20.0
        self.assertEqual(v.current, 10.0)
        self.assertEqual(v.resistance, 20.0)
        self.assertEqual(v.volt(), 200.0)

if __name__ == '__main__':
    unittest.main()
