import unittest
import subprocess

PYTHON_CMD = 'python'

class TestStudentScriptEx3(unittest.TestCase):
    
    def test_output_1(self):
        student_script = 'a2_ex3.py'
        inputs = '1\n10\n3\n'
        expected_output = '''\
Start: Stop: Step: Index: 0, Value: 1
Index: 1, Value: 4
Index: 2, Value: 7
Index: 3, Value: 10
Sum of even values: 14
Sum of odd multiplied values: 14
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

    def test_output_2(self):
        student_script = 'a2_ex3.py'
        inputs = '0\n100\n1\n'
        expected_output = '''\
Start: Stop: Step: Index: 0, Value: 0
Index: 1, Value: 1
Index: 2, Value: 2
Index: 3, Value: 3
Index: 4, Value: 4
Index: 96, Value: 96
Index: 97, Value: 97
Index: 98, Value: 98
Index: 99, Value: 99
Index: 100, Value: 100
Sum of even values: 2550
Sum of odd multiplied values: 166650
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

    def test_output_3(self):
        student_script = 'a2_ex3.py'
        inputs = '59\n20\n1\n'
        expected_output = '''\
Start: Stop: Step: Sum of even values: 0
Sum of odd multiplied values: 0
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

    def test_output_4(self):
        student_script = 'a2_ex3.py'
        inputs = '9\n40\n5\n'
        expected_output = '''\
Start: Stop: Step: Index: 0, Value: 9
Index: 1, Value: 14
Index: 2, Value: 19
Index: 3, Value: 24
Index: 4, Value: 29
Index: 5, Value: 34
Index: 6, Value: 39
Sum of even values: 72
Sum of odd multiplied values: 388
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)


if __name__ == '__main__':
    unittest.main()
