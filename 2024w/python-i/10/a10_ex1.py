import numpy as np

def matrix_operations(size: int):
    assert size > 0, "Size should be a positive integer"

    matrix = np.random.randint(0, 100, (size, size, size))

    return (
        # sums across axes
        matrix.sum(axis=0),
        matrix.sum(axis=(0, 1)),
        matrix.sum(),
        # indices of max and min values, argmax/min returns the flattened index 
        # so we transform it back to our shape
        np.unravel_index(matrix.argmax(), matrix.shape),
        np.unravel_index(matrix.argmin(), matrix.shape),
        # sum of border elements
        sum([
            matrix[0].sum(),                # first layer
            matrix[-1].sum(),               # last layer
            matrix[1:-1, 0].sum(),          # first row of all other layers
            matrix[1:-1, -1].sum(),         # last row of all other layers
            matrix[1:-1, 1:-1, 0].sum(),    # first column of all other layers
            matrix[1:-1, 1:-1, -1].sum()    # last column of all other layers
        ]),
        # -min() so the values are in [0, max()-min()] then divide by new max
        ((matrix - matrix.min()) / (matrix.max() - matrix.min())).flatten()
    )

if __name__ == '__main__':
    np.random.seed(0)

    print(matrix_operations(4))
