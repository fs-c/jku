class Electric_Circuits:
    x: float
    y: float
    z: float

    def __init__(self, x: float, y: float, z: float):
        self.x = x
        self.y = y
        self.z = z

    def to_string(self) -> str:
        return f"{type(self).__name__}: x={self.x}, y={self.y}, z={self.z}"
    
    def measure(self) -> float:
        raise NotImplementedError("Not implemented in base class")
