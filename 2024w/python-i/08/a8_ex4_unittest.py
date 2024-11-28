import unittest

from a8_ex2 import Electric_Circuits
from a8_ex4 import Charge_Flow

class TestChargeFlow(unittest.TestCase):

    def test_init_valid(self):
        cf = Charge_Flow(1.0, 2.0, 3, 0.5, 10)
        self.assertEqual(cf.x, 1.0)
        self.assertEqual(cf.y, 2.0)
        self.assertEqual(cf.z, 3)
        self.assertEqual(cf.current, 0.5)
        self.assertEqual(cf.time, 10)
    
    def test_to_string(self):
        cf = Charge_Flow(1.0, 2.0, 3, 0.5, 10)
        expected = "Charge_Flow: x=1.0, y=2.0, z=3, current=0.5, time=10"
        self.assertEqual(cf.to_string(), expected)
    
    def test_measure(self):
        cf = Charge_Flow(0.0, 0.0, 0, 0.5, 10)
        expected_charge = 0.5 * 10  # 5.0
        self.assertEqual(cf.measure(), expected_charge)
    
    def test_inheritance(self):
        cf = Charge_Flow(1.0, 2.0, 3, 0.5, 10)
        self.assertIsInstance(cf, Electric_Circuits)
    
    def test_attribute_modification(self):
        cf = Charge_Flow(1.0, 2.0, 3, 0.5, 10)
        cf.current = 1.0
        cf.time = 20
        expected_charge = 1.0 * 20  # 20.0
        self.assertEqual(cf.measure(), expected_charge)
        expected_string = "Charge_Flow: x=1.0, y=2.0, z=3, current=1.0, time=20"
        self.assertEqual(cf.to_string(), expected_string)
    
    def test_negative_values(self):
        cf = Charge_Flow(-1.0, -2.0, -3, -0.5, -10)
        expected_charge = (-0.5) * (-10)  # 5.0
        self.assertEqual(cf.measure(), expected_charge)
        expected_string = "Charge_Flow: x=-1.0, y=-2.0, z=-3, current=-0.5, time=-10"
        self.assertEqual(cf.to_string(), expected_string)
    
    def test_zero_values(self):
        cf = Charge_Flow(0.0, 0.0, 0, 0.0, 0)
        expected_charge = 0.0
        self.assertEqual(cf.measure(), expected_charge)
        expected_string = "Charge_Flow: x=0.0, y=0.0, z=0, current=0.0, time=0"
        self.assertEqual(cf.to_string(), expected_string)
    
    def test_large_values(self):
        cf = Charge_Flow(1e10, 2e10, 3e10, 1e5, 2e5)
        expected_charge = 1e5 * 2e5  # 2e10
        self.assertEqual(cf.measure(), expected_charge)
    
    def test_float_time(self):
        cf = Charge_Flow(1.0, 2.0, 3, 0.5, 10.5)
        expected_charge = 0.5 * 10.5  # 5.25
        self.assertEqual(cf.measure(), expected_charge)
        expected_string = "Charge_Flow: x=1.0, y=2.0, z=3, current=0.5, time=10.5"
        self.assertEqual(cf.to_string(), expected_string)
    
    def test_measure_with_zero_time(self):
        cf = Charge_Flow(1.0, 2.0, 3, 0.5, 0)
        expected_charge = 0.0
        self.assertEqual(cf.measure(), expected_charge)
    
    def test_measure_with_negative_time(self):
        cf = Charge_Flow(1.0, 2.0, 3, 0.5, -10)
        expected_charge = 0.5 * (-10)  # -5.0
        self.assertEqual(cf.measure(), expected_charge)
    
    def test_to_string_with_invalid_types(self):
        cf = Charge_Flow("x_value", "y_value", "z_value", "current_value", "time_value")
        expected = "Charge_Flow: x=x_value, y=y_value, z=z_value, current=current_value, time=time_value"
        self.assertEqual(cf.to_string(), expected)

if __name__ == "__main__":
    unittest.main()
