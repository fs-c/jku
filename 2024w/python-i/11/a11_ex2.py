import numpy as np

from a11_ex1 import count_neighbours

def apply_rules(grid: np.ndarray) -> np.ndarray:
    rows, cols = grid.shape
    new_grid = np.zeros((rows, cols), dtype=int)
    for i in range(rows):
        for j in range(cols):
            count = count_neighbours(grid, i, j)
            if grid[i, j]:
                if count < 2:
                    new_grid[i, j] = 0
                elif count < 4:
                    new_grid[i, j] = 1
                else:
                    new_grid[i, j] = 0
            else:
                if count == 3:
                    new_grid[i, j] = 1
    return new_grid
