class Vector:
    components: tuple

    def __init__(self, components: list[int | float]):
        for component in components:
            if not isinstance(component, (int, float)):
                raise TypeError(f"Components must be int or float, got '{type(component)}'")
        self.components = tuple(components)

    def __repr__(self):
        # apparently we want Vector((x, y, ...)) for some reason
        return f"Vector({self.components})"
    
    def __str__(self):
        return f"<{', '.join(str(component) for component in self.components)}>"
    
    def __eq__(self, other):
        if not isinstance(other, Vector):
            return NotImplemented
        return self.components == other.components
    
    def __add__(self, other):
        if not isinstance(other, Vector) or len(self.components) != len(other.components):
            return NotImplemented
        return Vector([a + b for a, b in zip(self.components, other.components)])
    
    def __radd__(self, other):
        return self + other

    def __sub__(self, other):
        if not isinstance(other, Vector) or len(self.components) != len(other.components):
            return NotImplemented
        return Vector([a - b for a, b in zip(self.components, other.components)])

    def __neg__(self):
        return Vector([-component for component in self.components])

    def __mul__(self, scalar):
        if not isinstance(scalar, (int, float)):
            return NotImplemented
        return Vector([component * scalar for component in self.components])

    def __rmul__(self, scalar):
        return self * scalar

    def __len__(self):
        return len(self.components)

    def __getitem__(self, index):
        if index > len(self.components) - 1 or index < -len(self.components):
            raise IndexError
        return self.components[index if index >= 0 else len(self.components) + index]
    
    def __iter__(self):
        return iter(self.components)
