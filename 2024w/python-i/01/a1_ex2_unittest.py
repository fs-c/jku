import unittest
import subprocess

class TestStudentScriptEx2(unittest.TestCase):
    def test_output(self):
        student_script = 'a1_ex2.py'
        inputs = '1\n2\n3\n4\n'
        expected_output = '''\
a: b: c: d: Sum of a, b and d: 7
Product of all numbers: 24
The sum of a and c times the sum of b and d: 24
a divided by c (int): 0
a divided by b (float): 0.5
Remainder of a divided by d: 1
a to the power of -c: 1.0
d to the power of 1/2 (square root): 2.0
Complex equation: 4.0
'''

        result = subprocess.run(['python', student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

if __name__ == '__main__':
    unittest.main()
