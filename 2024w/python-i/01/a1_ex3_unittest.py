import unittest
import subprocess

class TestStudentScriptEx3(unittest.TestCase):
    def test_output(self):
        student_script = 'a1_ex3.py'
        inputs = '3\n5\n'
        expected_output = '''\
Radius (in metres): Height (in metres): Surface area of the tank: 150.80
Volume of the tank: 141.37
Amount of water needed: 127.23
Litres of paint needed: 98.02
Number of plates needed: 76
'''

        result = subprocess.run(['python', student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

if __name__ == '__main__':
    unittest.main()
