class Time:
    hours: int
    minutes: int
    seconds: int

    def __init__(self, hours: int, minutes: int, seconds: int):
        if not (0 <= hours < 24 and 0 <= minutes < 60 and 0 <= seconds < 60):
            raise ValueError("Time component out of bounds")
        self.hours = hours
        self.minutes = minutes
        self.seconds = seconds

    def to_seconds(self) -> int:
        return self.hours * 3600 + self.minutes * 60 + self.seconds
    
    @staticmethod
    def from_seconds(total_seconds) -> 'Time':
        hours, remainder = divmod(total_seconds, 3600)
        minutes, seconds = divmod(remainder, 60)
        return Time(hours, minutes, seconds)

    def __repr__(self) -> str:
        return f"Time(hours={self.hours}, minutes={self.minutes}, seconds={self.seconds})"
    
    def __str__(self) -> str:
        return f"{self.hours:02}:{self.minutes:02}:{self.seconds:02}"
    
    def __eq__(self, other) -> bool:
        if not isinstance(other, Time):
            return NotImplemented
        return self.to_seconds() == other.to_seconds()
    
    def __lt__(self, other) -> bool:
        if not isinstance(other, Time):
            return NotImplemented
        return self.to_seconds() < other.to_seconds()
    
    def __add__(self, other) -> 'Time':
        if isinstance(other, Time):
            total_seconds = self.to_seconds() + other.to_seconds()
            return Time.from_seconds(total_seconds)
        elif isinstance(other, int):
            total_seconds = self.to_seconds() + other
            return Time.from_seconds(total_seconds)
        return NotImplemented
    
    def __radd__(self, other) -> 'Time':
        return self + other

    # add always returns Time but sub returns Time | int (╯°□°）╯︵ ┻━┻
    def __sub__(self, other):
        if isinstance(other, Time):
            return self.to_seconds() - other.to_seconds()
        elif isinstance(other, int):
            total_seconds = self.to_seconds() - other
            return Time.from_seconds(total_seconds)
        return NotImplemented

    def __int__(self) -> int:
        return self.to_seconds()
