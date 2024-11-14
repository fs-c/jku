from a6_ex1 import numerical_sequence

test_inputs = [11]
expected_outputs = [[1, 3, 6, 10, 15, 21, 28, 36, 45, 55]]

for index, (test_input, expected_output) in enumerate(zip(test_inputs, expected_outputs), 1):
    sequence = numerical_sequence()
    output = [next(sequence) for _ in range(1, test_input)]
    assert output == expected_output, f"Test {index} failed. input={test_input}, output={output}, expected_output={expected_output}"

print("OK")