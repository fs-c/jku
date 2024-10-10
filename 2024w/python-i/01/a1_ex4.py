chairs = int(input('Input the number of ordered chairs: '))
tables = int(input('Input the number of ordered tables: '))
lamps = int(input('Input the number of ordered lamps: '))

chair_price = 49.99
table_price = 199.99
lamp_price = 29.99

print()
print('Order Form:')
print('---------------------------------')
print(f'Chairs: {chairs:3d} x {chair_price:6.2f} = {chairs * chair_price:10.2f}')
print(f'Tables: {tables:3d} x {table_price:6.2f} = {tables * table_price:10.2f}')
print(f'Lamps: {lamps:4d} x {lamp_price:6.2f} = {lamps * lamp_price:10.2f}')
print('---------------------------------')
print(f'Total: {chairs * chair_price + tables * table_price + lamps * lamp_price:26.2f}')
print('=================================')
