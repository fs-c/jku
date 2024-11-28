import unittest

from a8_ex2 import Electric_Circuits
from a8_ex3 import Energy

class TestEnergy(unittest.TestCase):

    def test_init_valid(self):
        e = Energy(1.0, 2.0, 3, 0.5, 20.0, 10)
        self.assertEqual(e.x, 1.0)
        self.assertEqual(e.y, 2.0)
        self.assertEqual(e.z, 3)
        self.assertEqual(e.current, 0.5)
        self.assertEqual(e.resistance, 20.0)
        self.assertEqual(e.time, 10)
    
    def test_to_string(self):
        e = Energy(1.0, 2.0, 3, 0.5, 20.0, 10)
        expected = "Energy: x=1.0, y=2.0, z=3, current=0.5, resistance=20.0, time=10"
        self.assertEqual(e.to_string(), expected)
    
    def test_measure(self):
        e = Energy(0, 0, 0, 0.5, 20.0, 10)
        expected_energy = (0.5 ** 2) * 20.0 * 10  # 0.25 * 20 * 10 = 50.0
        self.assertEqual(e.measure(), expected_energy)
    
    def test_inheritance(self):
        e = Energy(1.0, 2.0, 3, 0.5, 20.0, 10)
        self.assertIsInstance(e, Electric_Circuits)
    
    def test_attribute_modification(self):
        e = Energy(1.0, 2.0, 3, 0.5, 20.0, 10)
        e.current = 1.0
        e.resistance = 10.0
        e.time = 5
        expected_energy = (1.0 ** 2) * 10.0 * 5  # 1 * 10 * 5 = 50.0
        self.assertEqual(e.measure(), expected_energy)
        expected_string = "Energy: x=1.0, y=2.0, z=3, current=1.0, resistance=10.0, time=5"
        self.assertEqual(e.to_string(), expected_string)
    
    def test_negative_values(self):
        e = Energy(-1.0, -2.0, -3, -0.5, -20.0, -10)
        expected_energy = ((-0.5) ** 2) * (-20.0) * (-10)  # 0.25 * -20 * -10 = 50.0
        self.assertEqual(e.measure(), 50.0)
        expected_string = "Energy: x=-1.0, y=-2.0, z=-3, current=-0.5, resistance=-20.0, time=-10"
        self.assertEqual(e.to_string(), expected_string)
    
    def test_zero_values(self):
        e = Energy(0.0, 0.0, 0, 0.0, 0.0, 0)
        expected_energy = 0.0
        self.assertEqual(e.measure(), expected_energy)
        expected_string = "Energy: x=0.0, y=0.0, z=0, current=0.0, resistance=0.0, time=0"
        self.assertEqual(e.to_string(), expected_string)
    
    def test_large_values(self):
        e = Energy(1e10, 2e10, 3e10, 1e5, 2e5, 3e5)
        expected_energy = (1e5) ** 2 * 2e5 * 3e5
        self.assertEqual(e.measure(), expected_energy)
    
    def test_float_time(self):
        e = Energy(1.0, 2.0, 3, 0.5, 20.0, 10.5)
        expected_energy = (0.5 ** 2) * 20.0 * 10.5
        self.assertEqual(e.measure(), expected_energy)
        expected_string = "Energy: x=1.0, y=2.0, z=3, current=0.5, resistance=20.0, time=10.5"
        self.assertEqual(e.to_string(), expected_string)
    
    def test_measure_with_zero_time(self):
        e = Energy(1.0, 2.0, 3, 0.5, 20.0, 0)
        expected_energy = 0.0
        self.assertEqual(e.measure(), expected_energy)
    
    def test_measure_with_negative_time(self):
        e = Energy(1.0, 2.0, 3, 0.5, 20.0, -10)
        expected_energy = (0.5 ** 2) * 20.0 * -10
        self.assertEqual(e.measure(), expected_energy)
    
    def test_invalid_measure_calculation(self):
        e = Energy(1.0, 2.0, 3, "invalid", 20.0, 10)
        with self.assertRaises(TypeError):
            e.measure()
        e = Energy(1.0, 2.0, 3, 0.5, "invalid", 10)
        with self.assertRaises(TypeError):
            e.measure()
        e = Energy(1.0, 2.0, 3, 0.5, 20.0, "invalid")
        with self.assertRaises(TypeError):
            e.measure()
    
    def test_to_string_with_invalid_types(self):
        e = Energy("x_value", "y_value", "z_value", "current_value", "resistance_value", "time_value")
        expected = "Energy: x=x_value, y=y_value, z=z_value, current=current_value, resistance=resistance_value, time=time_value"
        self.assertEqual(e.to_string(), expected)

if __name__ == '__main__':
    unittest.main()
