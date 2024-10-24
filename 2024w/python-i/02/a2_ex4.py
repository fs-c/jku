size = int(input('Diamond size: '))

if size < 2:
    print('Invalid size')
    exit(0)

if (size % 2) == 0:
    size += 1

max_spaces = size - 2

for i in range(1, size + 1):
    outer_spaces = abs((size // 2) + 1 - i)
    inner_spaces = max_spaces - (outer_spaces * 2)

    print(' ' * outer_spaces + '*' + ' ' * inner_spaces, end='')

    if i != 1 and i != size:
        print('*', end='')
    
    print(' ' * outer_spaces)
