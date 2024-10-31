
from a4_ex2 import compose

# Example functions
def add_one(x):
    return x + 1

def square(x):
    return x * x

def half(x):
    return x / 2

value = 3
test_inputs = [
    (), 
    (square,), 
    (half, square, add_one),
]
expected_outputs = [
    3, 
    9, 
    8
]

for index, (test_input, expected_output) in enumerate(zip(test_inputs, expected_outputs), 1):
    compose_fn = compose(*test_input)
    output = compose_fn(value)
    assert output == expected_output, f"Test {index} failed. input={test_input}, output={output}, expected_output={expected_output}"

print("OK")