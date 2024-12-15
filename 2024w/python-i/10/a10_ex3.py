import numpy as np

def convolution(matrix: np.ndarray, kernel: np.ndarray, padding: int = 0) -> np.ndarray:
    assert matrix.ndim == 2, "Matrix must be 2D"
    assert kernel.ndim == 2, "Kernel must be 2D"

    assert kernel.shape[0] == kernel.shape[1], "Kernel must be square"
    assert kernel.shape[0] % 2 == 1, "Kernel must have an odd number of dimensions"

    assert matrix.shape[0] >= kernel.shape[0], "Matrix must be larger than the kernel"
    assert matrix.shape[1] >= kernel.shape[1], "Matrix must be larger than the kernel"

    padding_n = kernel.shape[0] // 2
    padded_matrix = np.pad(matrix, padding_n, mode = 'constant', constant_values = padding)

    output = np.zeros_like(matrix)
    for i in range(0, matrix.shape[0]):
        for j in range(0, matrix.shape[1]):
            output[i, j] = np.sum(
                padded_matrix[i:i + kernel.shape[0], j:j + kernel.shape[1]] * kernel
            )

    return output

if __name__ == '__main__':
    print(
        convolution(
            np.array([[1, 2, 3], [4, 5, 6], [7, 8, 9]]),
            np.array([[0, 0, 0], [0, 1, 0], [0, 0, 0]]),
            padding=0
        )
    )

    print(
        convolution(
            np.array([[1, 2, 3], [4, 5, 6], [7, 8, 9]]),
            np.array([[1, 0, -1], [1, 0, -1], [1, 0, -1]]),
            padding=1
        )
    )
