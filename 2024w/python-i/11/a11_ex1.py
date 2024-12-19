import numpy as np

def create_grid(rows: int, cols: int) -> np.ndarray:
    np.random.seed(0)
    return np.random.randint(0, 2, (rows, cols), dtype=int)

def count_neighbours(grid: np.ndarray, row: int, col: int) -> int:
    rows, cols = grid.shape
    count = 0
    for i in range(row - 1, row + 2):
        for j in range(col - 1, col + 2):
            if i == row and j == col:
                continue
            if 0 <= i < rows and 0 <= j < cols:
                count += grid[i, j]
    return count

def print_grid(grid: np.ndarray) -> None:
    rows, cols = grid.shape
    for i in range(rows):
        for j in range(cols):
            print("*" if grid[i, j] else ".", end="")
            if j != cols - 1:
                print(" ", end="")
        print()
    print()

def number_of_live_cells(grid: np.ndarray) -> int:
    return np.sum(grid)

if __name__ == "__main__":
    grid = np.array([
        [0, 1, 0, 1, 0],
        [0, 0, 1, 0, 0],
        [1, 1, 1, 1, 1],
        [0, 0, 1, 0, 0],
        [0, 1, 0, 1, 0]
    ])

    print(count_neighbours(grid, 1, 0))
