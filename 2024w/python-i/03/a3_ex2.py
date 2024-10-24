inputs: list[str] = []

while True:
    element = input('Enter element or \'x\' when done: ')
    if element == 'x':
        break
    inputs.append(element)

first_half = inputs[:len(inputs) // 2]
second_half = inputs[len(inputs) // 2:]

print('All: ', inputs)
print('First half: ', first_half)
print('Second half: ', second_half)

common_words = sorted(list(set(first_half) & set(second_half)))

print('Sorted common words: ', common_words)
