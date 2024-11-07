import unittest
from a5_ex2 import safe_lookup 

class TestSafeLookup(unittest.TestCase):

    def setUp(self):
        self.nested_dict = {
            "level1": {
                "level2": {
                    "key": "value",
                    "int_value": 123
                }
            }
        }
        self.test_cases = [
            # (d, keys, expected_type, expected_return_value, should_raise_type_error)
            (self.nested_dict, ["level1", "level2", "key"], str, "value", False),           # Valid case with correct type
            (self.nested_dict, ["level1", "level2", "int_value"], int, 123, False),         # Valid case with integer
            (self.nested_dict, ["level1", "level2", "missing_key"], str, "Key not found", False),  # Missing key
            (self.nested_dict, ["level1", "missing_level"], str, "Key not found", False),   # Missing level
            (self.nested_dict, ["level1", "level2"], list, None, True)                      # Type mismatch
        ]

    def test_safe_lookup(self):
        for d, keys, expected_type, expected_return_value, should_raise_type_error in self.test_cases:
            with self.subTest(d=d, keys=keys, expected_type=expected_type):
                if should_raise_type_error:
                    with self.assertRaises(TypeError):
                        safe_lookup(d, keys, expected_type)
                else:
                    result = safe_lookup(d, keys, expected_type)
                    self.assertEqual(result, expected_return_value)

if __name__ == '__main__':
    unittest.main()
