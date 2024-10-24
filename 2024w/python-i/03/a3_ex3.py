pizza_prices = dict(margarita = 10, provenzale = 12, rusticana = 17, funghi = 16, cipolla = 13)

extra_price = 1.5
available_extras = ['egg', 'cheese', 'salami', 'pepperoni', 'garlic', 'ham']

print('Hello at the JKU Pizza Service!')
print('Please select your pizza:')

for pizza, price in pizza_prices.items():
    print(f'Pizza {pizza}: {price} Euros')

selected_pizza: str | None = None
while True:
    selected_pizza = input('Enter name of pizza: ')
    if selected_pizza in pizza_prices:
        break
    print('Pizza not available, please try again.')

print(f'You have selected pizza {selected_pizza} for {pizza_prices[selected_pizza]} Euros.')

print('Which extras would you like? Please enter them separated by a \';\'.')

for extra in available_extras:
    print(extra)

selected_extras_string = input()
selected_extras = selected_extras_string.split(';')

selected_available_extras = [extra for extra in selected_extras if extra in available_extras]
selected_unavailable_extras = [extra for extra in selected_extras if extra not in available_extras]

if not len(selected_extras_string):
    print('No extras selected.')
else:
    if len(selected_unavailable_extras):
        print('Extras not available:', ', '.join(selected_unavailable_extras))
        if len(selected_available_extras):
            print('Extras available and added:', ', '.join(selected_available_extras))
    else:
        print('All extras available and added.')

total_price = pizza_prices[selected_pizza] + len(selected_available_extras) * extra_price
print(f'Your total price is now {total_price} Euros.')

print('Thank you for your order!')
