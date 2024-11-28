from a8_ex3 import Energy

class Power(Energy):
    def __init__(self, x, y, z, current, resistance):
        super().__init__(x, y, z, current, resistance, 1)
