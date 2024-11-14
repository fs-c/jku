from a6_ex2 import power_set

test_inputs = [[], [3, 1, 2], ['c', 'a', 'b']]
expected_outputs = [{()}, 
                    {(1, 3), (2,), (1, 2), (1, 2, 3), (2, 3), (1,), (), (3,)},
                    {('a',), ('a', 'b', 'c'), ('b',), ('b', 'c'), ('a', 'b'), ('a', 'c'), (), ('c',)}]

for index, (test_input, expected_output) in enumerate(zip(test_inputs, expected_outputs), 1):
    output = power_set(test_input)
    assert output == expected_output, f"Test {index} failed. input={test_input}, output={output}, expected_output={expected_output}"

print("OK")

