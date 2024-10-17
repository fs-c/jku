import unittest
import subprocess

PYTHON_CMD='python'

class TestStudentScriptEx2(unittest.TestCase):

    def test_output_1(self):
        student_script = 'a2_ex2.py'
        inputs = 'x\n'
        expected_output = '''\
Enter a value (or 'x' to stop): Empty sequence
'''
        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

    def test_output_2(self):
        student_script = 'a2_ex2.py'
        inputs = '4\nx\n'
        expected_output = '''\
Enter a value (or 'x' to stop): Enter a value (or 'x' to stop): Result: 4
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

    def test_output_3(self):
        student_script = 'a2_ex2.py'
        inputs = '4\n5\n3\n2\nx\n'
        expected_output = '''\
Enter a value (or 'x' to stop): Enter a value (or 'x' to stop): Enter a value (or 'x' to stop): Enter a value (or 'x' to stop): Enter a value (or 'x' to stop): Result: 120
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

    def test_output_4(self):
        student_script = 'a2_ex2.py'
        inputs = '9\n7\n7\n4\n'
        expected_output = '''\
Enter a value (or 'x' to stop): Enter a value (or 'x' to stop): Enter a value (or 'x' to stop): Enter a value (or 'x' to stop): Result has exceeded the value 1000: 1764
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

if __name__ == '__main__':
    unittest.main()
