import numpy as np

def elements_wise(arr: np.ndarray, f):
    for i in np.ndindex(arr.shape):
        arr[i] = f(arr[i])

if __name__ == '__main__':
    a1 = np.array([1, 2, 3])
    elements_wise(a1, lambda x: x * x)
    print(a1)

    a2 = np.array(range(9)).reshape(3, 3)
    elements_wise(a2, lambda x: x * x)
    print(a2)
