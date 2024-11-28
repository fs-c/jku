import unittest
from a8_ex2 import Electric_Circuits


class TestElectricCircuits(unittest.TestCase):

    def test_init_valid(self):
        ec = Electric_Circuits(1.0, 2.0, 3)
        self.assertEqual(ec.x, 1.0)
        self.assertEqual(ec.y, 2.0)
        self.assertEqual(ec.z, 3)

    def test_init_invalid_x(self):
        ec = Electric_Circuits("invalid", 2.0, 3)
        self.assertEqual(ec.x, "invalid")
        self.assertEqual(ec.y, 2.0)
        self.assertEqual(ec.z, 3)

    def test_init_invalid_y(self):
        ec = Electric_Circuits(1.0, "invalid", 3)
        self.assertEqual(ec.x, 1.0)
        self.assertEqual(ec.y, "invalid")
        self.assertEqual(ec.z, 3)

    def test_init_invalid_z(self):
        ec = Electric_Circuits(1.0, 2.0, "invalid")
        self.assertEqual(ec.x, 1.0)
        self.assertEqual(ec.y, 2.0)
        self.assertEqual(ec.z, "invalid")

    def test_to_string(self):
        ec = Electric_Circuits(1.0, 2.0, 3)
        expected = "Electric_Circuits: x=1.0, y=2.0, z=3"
        self.assertEqual(ec.to_string(), expected)

    def test_to_string_with_invalid_types(self):
        ec = Electric_Circuits("x_value", "y_value", "z_value")
        expected = "Electric_Circuits: x=x_value, y=y_value, z=z_value"
        self.assertEqual(ec.to_string(), expected)

    def test_measure_not_implemented(self):
        ec = Electric_Circuits(1.0, 2.0, 3)
        with self.assertRaises(NotImplementedError):
            ec.measure()

    def test_attribute_modification(self):
        ec = Electric_Circuits(1.0, 2.0, 3)
        ec.x = 10.0
        ec.y = 20.0
        ec.z = 30
        self.assertEqual(ec.x, 10.0)
        self.assertEqual(ec.y, 20.0)
        self.assertEqual(ec.z, 30)
        expected = "Electric_Circuits: x=10.0, y=20.0, z=30"
        self.assertEqual(ec.to_string(), expected)

    def test_negative_values(self):
        ec = Electric_Circuits(-1.0, -2.0, -3)
        self.assertEqual(ec.x, -1.0)
        self.assertEqual(ec.y, -2.0)
        self.assertEqual(ec.z, -3)
        expected = "Electric_Circuits: x=-1.0, y=-2.0, z=-3"
        self.assertEqual(ec.to_string(), expected)

    def test_zero_values(self):
        ec = Electric_Circuits(0.0, 0.0, 0)
        self.assertEqual(ec.x, 0.0)
        self.assertEqual(ec.y, 0.0)
        self.assertEqual(ec.z, 0)
        expected = "Electric_Circuits: x=0.0, y=0.0, z=0"
        self.assertEqual(ec.to_string(), expected)

    def test_large_values(self):
        ec = Electric_Circuits(1e10, 2e10, 3e10)
        self.assertEqual(ec.x, 1e10)
        self.assertEqual(ec.y, 2e10)
        self.assertEqual(ec.z, 3e10)
        expected = "Electric_Circuits: x=10000000000.0, y=20000000000.0, z=30000000000.0"
        self.assertEqual(ec.to_string(), expected)

    def test_float_z(self):
        ec = Electric_Circuits(1.0, 2.0, 3.0)
        self.assertEqual(ec.x, 1.0)
        self.assertEqual(ec.y, 2.0)
        self.assertEqual(ec.z, 3.0)
        expected = "Electric_Circuits: x=1.0, y=2.0, z=3.0"
        self.assertEqual(ec.to_string(), expected)

if __name__ == '__main__':
    unittest.main()
