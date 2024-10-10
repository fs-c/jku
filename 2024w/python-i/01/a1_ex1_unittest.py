import unittest
import subprocess


class TestStudentScriptEx1(unittest.TestCase):
    def test_output(self):
        student_script = 'a1_ex1.py'
        expected_output = '''\
False
-000048
      1.5000
pythonisgreatpythonisgreat
'''

        result = subprocess.run(['python', student_script],
                                capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)


if __name__ == '__main__':
    unittest.main()
