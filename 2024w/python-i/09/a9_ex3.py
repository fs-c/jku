import os
from typing import IO

class Reader:
    handle: IO

    def __init__(self, path: str):
        try:
            self.handle = open(path, mode = "rb")
        except OSError:
            raise ValueError

    def close(self):
        self.handle.close()

    def __len__(self):
        return self.handle.seek(0, os.SEEK_END)

    def __getitem__(self, key):
        if not isinstance(key, int):
            raise TypeError
        if key > len(self) - 1 or key < -len(self):
            raise IndexError

        self.handle.seek(key if key >= 0 else len(self) + key)
        return self.handle.read(1)
