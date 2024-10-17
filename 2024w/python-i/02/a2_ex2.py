product = 0

while True:
    value = input('Enter a value (or \'x\' to stop): ')
    if value == 'x':
        break
    
    if product == 0:
        product = 1

    product *= int(value)

    if product > 1000:
        break

if product == 0:
    print('Empty sequence')
elif product > 1000:
    print(f'Result has exceeded the value 1000: {product}')
else:
    print(f'Result: {product}')
