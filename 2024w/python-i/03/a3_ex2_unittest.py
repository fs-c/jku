import unittest
import subprocess

PYTHON_CMD = "python"

class TestStudentScriptEx2(unittest.TestCase):
    def test_output1(self):
        student_script = 'a3_ex2.py'
        inputs = 'a\nb\na\nx\n'
        expected_output = '''\
Enter element or 'x' when done: Enter element or 'x' when done: Enter element or 'x' when done: Enter element or 'x' when done: All:  ['a', 'b', 'a']
First half:  ['a']
Second half:  ['b', 'a']
Sorted common words:  ['a']
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())
        
    def test_output2(self):
        student_script = 'a3_ex2.py'
        inputs = 'x\n'
        expected_output = '''\
Enter element or 'x' when done: All:  []
First half:  []
Second half:  []
Sorted common words:  []
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())
        
    def test_output3(self):
        student_script = 'a3_ex2.py'
        inputs = 'hello\nthis\nis\na\ntest\nx\n'
        expected_output = '''\
Enter element or 'x' when done: Enter element or 'x' when done: Enter element or 'x' when done: Enter element or 'x' when done: Enter element or 'x' when done: Enter element or 'x' when done: All:  ['hello', 'this', 'is', 'a', 'test']
First half:  ['hello', 'this']
Second half:  ['is', 'a', 'test']
Sorted common words:  []
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())
        
    def test_output4(self):
        student_script = 'a3_ex2.py'
        inputs = 'to\nbe\nor\nnot\nto\nbe\nx\n'
        expected_output = '''\
Enter element or 'x' when done: Enter element or 'x' when done: Enter element or 'x' when done: Enter element or 'x' when done: Enter element or 'x' when done: Enter element or 'x' when done: Enter element or 'x' when done: All:  ['to', 'be', 'or', 'not', 'to', 'be']
First half:  ['to', 'be', 'or']
Second half:  ['not', 'to', 'be']
Sorted common words:  ['be', 'to']
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())

if __name__ == '__main__':
    unittest.main()

