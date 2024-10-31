
from a4_ex1 import aggregate

test_input1 = ()
expected_output1 = {}

test_input2 = ({'a':5, 'b':10, 'd':4},)
expected_output2 = {'a': 5, 'b': 10, 'd': 4}

test_input3 = (['a', 'b', 'c', 'b', 'c'],)
expected_output3 = {'a': 1, 'b': 2, 'c': 2}

test_input4 = (['a', 'b', 'c', 'b', 'c'], {'a':5, 'b':10, 'd':4})
expected_output4 = {'a': 6, 'b': 12, 'd': 4, 'c': 2}

test_inputs = [test_input1, test_input2, test_input3, test_input4]
expected_outputs = [expected_output1, expected_output2, expected_output3, expected_output4]

for index, (test_input, expected_output) in enumerate(zip(test_inputs, expected_outputs), 1):
    length = len(test_input)
    if length == 0:
        output = aggregate()
    elif length == 1:
        if isinstance(test_input[0], list):
            output = aggregate(*test_input[0])
        else:
            output = aggregate(**test_input[0])
    else:
        output = aggregate(*test_input[0], **test_input[1])

    assert output == expected_output, f"Test {index} failed. output={output}, expected_output={expected_output}"

print("OK")

