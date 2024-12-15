import numpy as np

def one_hot_encoding(arr: np.ndarray) -> np.ndarray:
    if len(arr.shape) != 1:
        raise ValueError(f"The function can work for 1D matrices, not {len(arr.shape)}D")
    
    unique_values = np.unique(arr)
    output = np.empty((arr.size, unique_values.size))
    for i, value in enumerate(arr):
        output[i] = unique_values == value

    return output

if __name__ == "__main__":
    print(one_hot_encoding(np.array([1, 1, 2, 3, 1])))
