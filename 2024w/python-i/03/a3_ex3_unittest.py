import unittest
import subprocess

PYTHON_CMD = "python"

class TestStudentScriptEx3(unittest.TestCase):

    def setUp(self):
        """Set up before each test case. Disables maxDiff truncation."""
        self.maxDiff = None
    
    def test_output1(self):
        student_script = 'a3_ex3.py'
        inputs = 'cipolla\neggplant;ham;cheese;fish\n'
        expected_output = '''\
Hello at the JKU Pizza Service!
Please select your pizza:
Pizza margarita: 10 Euros
Pizza provenzale: 12 Euros
Pizza rusticana: 17 Euros
Pizza funghi: 16 Euros
Pizza cipolla: 13 Euros
Enter name of pizza: You have selected pizza cipolla for 13 Euros.
Which extras would you like? Please enter them separated by a ';'.
egg
cheese
salami
pepperoni
garlic
ham
Extras not available: eggplant, fish
Extras available and added: ham, cheese
Your total price is now 16.0 Euros.
Thank you for your order!
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())

    def test_output2(self):
        student_script = 'a3_ex3.py'
        inputs = 'della casa\nfrutti di mare\nmargarita\nham;cheese\n'
        expected_output = '''\
Hello at the JKU Pizza Service!
Please select your pizza:
Pizza margarita: 10 Euros
Pizza provenzale: 12 Euros
Pizza rusticana: 17 Euros
Pizza funghi: 16 Euros
Pizza cipolla: 13 Euros
Enter name of pizza: Pizza not available, please try again.
Enter name of pizza: Pizza not available, please try again.
Enter name of pizza: You have selected pizza margarita for 10 Euros.
Which extras would you like? Please enter them separated by a ';'.
egg
cheese
salami
pepperoni
garlic
ham
All extras available and added.
Your total price is now 13.0 Euros.
Thank you for your order!
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())

    def test_output3(self):
        student_script = 'a3_ex3.py'
        inputs = 'rusticana\negg;ham;cheese\n'
        expected_output = '''\
Hello at the JKU Pizza Service!
Please select your pizza:
Pizza margarita: 10 Euros
Pizza provenzale: 12 Euros
Pizza rusticana: 17 Euros
Pizza funghi: 16 Euros
Pizza cipolla: 13 Euros
Enter name of pizza: You have selected pizza rusticana for 17 Euros.
Which extras would you like? Please enter them separated by a ';'.
egg
cheese
salami
pepperoni
garlic
ham
All extras available and added.
Your total price is now 21.5 Euros.
Thank you for your order!
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())
        
    def test_output4(self):
        student_script = 'a3_ex3.py'
        inputs = 'funghi\n\n'
        expected_output = '''\
Hello at the JKU Pizza Service!
Please select your pizza:
Pizza margarita: 10 Euros
Pizza provenzale: 12 Euros
Pizza rusticana: 17 Euros
Pizza funghi: 16 Euros
Pizza cipolla: 13 Euros
Enter name of pizza: You have selected pizza funghi for 16 Euros.
Which extras would you like? Please enter them separated by a ';'.
egg
cheese
salami
pepperoni
garlic
ham
No extras selected.
Your total price is now 16.0 Euros.
Thank you for your order!
'''

        result = subprocess.run([PYTHON_CMD, student_script], input=inputs, capture_output=True, text=True)
        self.assertEqual(result.stdout.strip(), expected_output.strip())

if __name__ == '__main__':
    unittest.main()

