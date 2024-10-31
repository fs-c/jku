# https://upload.wikimedia.org/wikipedia/commons/e/eb/Matrix_multiplication_diagram_2.svg

def multiply_matrix(matrix1: list, matrix2: list):
    if len(matrix1[0]) != len(matrix2):
        return None

    result: list[list[int]] = []

    for i in range(len(matrix1)):
        row: list[int] = []
        for j in range(len(matrix2[0])):
            value: int = 0
            for k in range(len(matrix1[0])):
                value += matrix1[i][k] * matrix2[k][j]
            row.append(value)
        result.append(row)

    return result
