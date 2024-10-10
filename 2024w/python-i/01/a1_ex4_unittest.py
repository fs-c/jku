import unittest
import subprocess

class TestStudentScriptEx4(unittest.TestCase):
    def test_output(self):
        student_script = 'a1_ex4.py'
        inputs = '4\n2\n3\n'
        expected_output = '''\
Input the number of ordered chairs: Input the number of ordered tables: Input the number of ordered lamps: 
Order Form:
---------------------------------
Chairs:   4 x  49.99 =     199.96
Tables:   2 x 199.99 =     399.98
Lamps:    3 x  29.99 =      89.97
---------------------------------
Total:                     689.91
=================================
'''

        result = subprocess.run(['python', student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout, expected_output)

if __name__ == '__main__':
    unittest.main()
