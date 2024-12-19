import numpy as np

def load_grid_from_file(filename: str) -> np.ndarray:
    with open(filename, "r") as f:
        lines = f.readlines()
        return np.array([[int(c) for c in line.strip()] for line in lines])

def save_grid_to_file(grid: np.ndarray, filename: str) -> None:
    with open(filename, "w") as f:
        for row in grid:
            f.write("".join(str(cell) for cell in row) + "\n")
