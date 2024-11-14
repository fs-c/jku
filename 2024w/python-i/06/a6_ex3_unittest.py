from a6_ex3 import flatten_dict

d1 = {}
d2 = {'a':1, 'b':2}
d3 = {
    'a':1, 'b':2,
    'c':{
        'a': 3,
        'b': {
            'a': 4,
            'b': 5
        }
    },
    'd': 6
}

test_inputs = [d1, d2, d3]
expected_outputs = [{},
                    {'a': 1, 'b': 2},
                    {'a': 1, 'b': 2, 'c.a': 3, 'c.b.a': 4, 'c.b.b': 5, 'd': 6}]

for index, (test_input, expected_output) in enumerate(zip(test_inputs, expected_outputs), 1):
    output = flatten_dict(test_input)
    assert output == expected_output, f"Test {index} failed. input={test_input}, output={output}, expected_output={expected_output}"

print("OK")