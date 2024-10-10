radius = float(input('Radius (in metres): '))
height = float(input('Height (in metres): '))

pi = 3.14159

surface_area = 2 * pi * radius * height + 2 * pi * radius ** 2
volume = pi * (radius ** 2) * height

print(f'Surface area of the tank: {surface_area:.2f}')
print(f'Volume of the tank: {volume:.2f}')

print(f'Amount of water needed: {volume * 0.9:.2f}')

print(f'Litres of paint needed: {surface_area * 0.65:.2f}')

# todo: i don't think we learned about if/else yet but doing ceil without this 
#  seems complicated
print(f'Number of plates needed: {int(surface_area / 2) + (1 if surface_area % 2 != 0 else 0):d}') 
