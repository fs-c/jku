from a8_ex2 import Electric_Circuits

class Energy(Electric_Circuits):
    current: float
    resistance: float
    time: float

    def __init__(self, x, y, z, current, resistance, time):
        super().__init__(x, y, z)
        self.current = current
        self.resistance = resistance
        self.time = time

    def measure(self):
        return (self.current ** 2) * self.resistance * self.time

    def to_string(self):
        return f"{super().to_string()}, current={self.current}, resistance={self.resistance}, time={self.time}"
