from a4_ex4 import check_parentheses

test_inputs = [
    "", 
    "(", 
    ")", 
    ")(",
    "()", 
    "( (()) ()()) )", 
    "( (()) (()()) )", 
    "( (()) (()()) ) (", 
    "( (()) (()()) ) ()"
]
expected_outputs = [True, False, False, False, True, False, True, False, True]

for index, (test_input, expected_output) in enumerate(zip(test_inputs, expected_outputs), 1):
    output = check_parentheses(test_input)
    assert output == expected_output, f"Test {index} failed. input={test_input}, output={output}, expected_output={expected_output}"

print("OK")

