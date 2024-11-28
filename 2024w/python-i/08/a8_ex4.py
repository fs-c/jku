from a8_ex2 import Electric_Circuits

class Charge_Flow(Electric_Circuits):
    current: float
    time: float

    def __init__(self, x, y, z, current, time):
        super().__init__(x, y, z)
        self.current = current
        self.time = time

    def measure(self):
        return self.current * self.time

    def to_string(self):
        return f"{super().to_string()}, current={self.current}, time={self.time}"
