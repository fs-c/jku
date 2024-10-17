start = int(input('Start: '))
stop = int(input('Stop: '))
step = int(input('Step: '))

sum_even = 0
sum_uneven_multiplied = 0

for index, value in enumerate(range(start, stop + 1, step)):
    if value % 2 == 0:
        sum_even += value
    else:
        sum_uneven_multiplied += value * index  
    
    if index < 5 * step or index > stop - 5 * step:
        print(f'Index: {index}, Value: {value}')

print(f'Sum of even values: {sum_even}')
print(f'Sum of odd multiplied values: {sum_uneven_multiplied}')
