class Voltage:
    current: float
    resistance: float

    def __init__(self, current: float, resistance: float):
        self.current = current
        self.resistance = resistance

    def print(self):
        print(f"{self.current} amps + {self.resistance} ohms")

    def volt(self) -> float:
        return self.current * self.resistance
    
    def increase_resistance(self, delta: float):
        if not isinstance(delta, float):
            raise TypeError(f"Please provide float value instead of {type(delta).__name__}")
        self.resistance += delta

    @staticmethod
    def add_all(volt_obj: "Voltage", *volt_objs: "Voltage") -> "Voltage":
        new_volt_obj = Voltage(volt_obj.current, volt_obj.resistance)

        for v in volt_objs:
            if not isinstance(v, Voltage):
                raise TypeError(f"Can only add objects of type 'Voltage'")
            if v.current != volt_obj.current:
                raise ValueError('The current must be equal')

            new_volt_obj.increase_resistance(v.resistance)

        return new_volt_obj
