import unittest
import subprocess

PYTHON_CMD = 'python'

def normalize_output(output):
    return '\n'.join([line.rstrip() for line in output.splitlines()])

class TestStudentScriptEx4(unittest.TestCase):

    def test_output_1(self):
        student_script = 'a2_ex4.py'
        inputs = '1\n'
        expected_output = '''\
Diamond size: Invalid size
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        actual_output = normalize_output(result.stdout)
        expected_output_processed = normalize_output(expected_output)
        self.assertEqual(result.stdout, expected_output)
    
    def test_output_2(self):
        student_script = 'a2_ex4.py'
        inputs = '5\n'
        expected_output = '''\
Diamond size:   *  
 * * 
*   *
 * * 
  *  
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        actual_output = normalize_output(result.stdout)
        expected_output_processed = normalize_output(expected_output)
        self.assertEqual(result.stdout, expected_output)

if __name__ == '__main__':
    unittest.main()
