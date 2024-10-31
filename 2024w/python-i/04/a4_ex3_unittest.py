
from a4_ex3 import multiply_matrix

test_inputs = [
    ([[1, 2, 3], [4, 5, 6]], [[7, 8], [9, 10]]),
    ([[1, 2, 3], [4, 5, 6]], [[7, 8], [9, 10], [11, 12]])
]
expected_outputs = [
    None, 
    [[58, 64], [139, 154]]
]

for index, (test_input, expected_output) in enumerate(zip(test_inputs, expected_outputs), 1):
    output = multiply_matrix(*test_input)
    assert output == expected_output, f"Test {index} failed. input={test_input}, output={output}, expected_output={expected_output}"

print("OK")