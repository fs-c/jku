import unittest
import subprocess

PYTHON_CMD = "python"

class TestStudentScriptEx4(unittest.TestCase):
    def test_output1(self):
        student_script = 'a3_ex4.py'
        inputs = 'hello world this is a test\n'
        expected_output = '''\
Enter text (space separated): length 1: 1 word (a)
length 2: 1 word (is)
length 4: 2 words (this, test)
length 5: 2 words (hello, world)
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())

    def test_output2(self):
        student_script = 'a3_ex4.py'
        inputs = 'a horse a horse my kingdom for a horse\n'
        expected_output = '''\
Enter text (space separated): length 1: 3 words (a, a, a)
length 2: 1 word (my)
length 3: 1 word (for)
length 5: 3 words (horse, horse, horse)
length 7: 1 word (kingdom)
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())

    def test_output3(self):
        student_script = 'a3_ex4.py'
        inputs = '\n'
        expected_output = '''\
Enter text (space separated): length 0: 1 word ()
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())

if __name__ == '__main__':
    unittest.main()

