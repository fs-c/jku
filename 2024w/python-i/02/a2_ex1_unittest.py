import unittest
import subprocess

PYTHON_CMD='python'

class TestStudentScriptEx1(unittest.TestCase):
    
    def test_output_1(self):
        student_script = 'a2_ex1.py'
        inputs = '2\n8\n'
        expected_output = '''\
Enter employment years (> 0): Enter department (10-99): Invalid input
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

    def test_output_2(self):
        student_script = 'a2_ex1.py'
        inputs = '0\n10\n'
        expected_output = '''\
Enter employment years (> 0): Enter department (10-99): Invalid input
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

    def test_output_3(self):
        student_script = 'a2_ex1.py'
        inputs = '3\n77\n'
        expected_output = '''\
Enter employment years (> 0): Enter department (10-99): Bonus for 3 years of employment in department 77: 300.00
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

    def test_output_4(self):
        student_script = 'a2_ex1.py'
        inputs = '7\n53\n'
        expected_output = '''\
Enter employment years (> 0): Enter department (10-99): Bonus for 7 years of employment in department 53: 440.00
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

    def test_output_5(self):
        student_script = 'a2_ex1.py'
        inputs = '8\n88\n'
        expected_output = '''\
Enter employment years (> 0): Enter department (10-99): Bonus for 8 years of employment in department 88: 480.00
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

if __name__ == '__main__':
    unittest.main()
