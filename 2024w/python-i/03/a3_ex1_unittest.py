import unittest
import subprocess


PYTHON_CMD = "python"

class TestStudentScriptEx1(unittest.TestCase):
    def test_output1(self):
        student_script = 'a3_ex1.py'
        inputs = '3\n3\n'
        expected_output = '''Number of rows: \
Number of cols:     0 1 2
   -------
0 | X O X |
1 | O X O |
2 | X O X |
   -------
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())

    def test_output2(self):
        student_script = 'a3_ex1.py'
        inputs = '3\n4\n'
        expected_output = '''Number of rows: \
Number of cols:     0 1 2 3
   ---------
0 | X O X O |
1 | O X O X |
2 | X O X O |
   ---------
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())
        
    def test_output3(self):
        student_script = 'a3_ex1.py'
        inputs = '1\n1\n'
        expected_output = '''Number of rows: \
Number of cols:     0
   ---
0 | X |
   ---
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())
        
    def test_output4(self):
        student_script = 'a3_ex1.py'
        inputs = '10\n10\n'
        expected_output = '''Number of rows: \
Number of cols:     0 1 2 3 4 5 6 7 8 9
   ---------------------
0 | X O X O X O X O X O |
1 | O X O X O X O X O X |
2 | X O X O X O X O X O |
3 | O X O X O X O X O X |
4 | X O X O X O X O X O |
5 | O X O X O X O X O X |
6 | X O X O X O X O X O |
7 | O X O X O X O X O X |
8 | X O X O X O X O X O |
9 | O X O X O X O X O X |
   ---------------------
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())

if __name__ == '__main__':
    unittest.main()

