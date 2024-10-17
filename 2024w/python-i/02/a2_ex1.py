employment_years = int(input('Enter employment years (> 0): '))
department = int(input('Enter department (10-99): '))

if employment_years <= 0 or department < 10 or department > 99:
    print('Invalid input')
    exit(0)

bonus = 200.0

if employment_years in range(2, 4):
    bonus = 300.0

if employment_years > 3:
    bonus = 400.0

    department_last_digit = department % 10

    bonus_multiplier = 1.0
    if department_last_digit in range(1, 6):
        bonus_multiplier = 1.1
    elif department_last_digit in range(5, 10):
        bonus_multiplier = 1.2

    bonus *= bonus_multiplier

print(f'Bonus for {employment_years} years of employment in department {department}: {bonus:.2f}')
