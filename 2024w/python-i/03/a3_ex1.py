num_rows = int(input('Number of rows: '))
num_cols = int(input('Number of cols: '))

#
# build the matrix
#
matrix: list[list[str]] = []
for row in range(0, num_rows):
    matrix.append([])

    for col in range(0, num_cols):
        # (col + row) % 2 creates an alternating pattern between rows
        matrix[row].append('X' if (col + row) % 2 == 0 else 'O')

#
# print header row
#
print('   ', end='')

for col in range(0, num_cols):
    print(' ' + str(col), end='')

print()
print('   ' + '-' * (num_cols * 2 + 1))

#
# print matrix rows
#
for row in range(0, num_rows):
    print(str(row) + ' | ', end='')

    for col in range(0, num_cols):
        print(matrix[row][col] + ' ', end='')

    print('|')

#
# print footer row
#
print('   ' + '-' * (num_cols * 2 + 1))
