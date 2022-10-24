-- Exercise 2b)

CREATE OR REPLACE PROCEDURE adjust_all_salaries
AS
    CURSOR c_emp_ids IS SELECT * FROM employees;
BEGIN
    FOR emp IN c_emp_ids LOOP
        adjust_salary(emp.employee_id);
    END LOOP;
END adjust_all_salaries;
/

-- create employees with 1. correct, 2. low and 3. high salary for their job
-- IT_PROG is [4000, 10000]
EXEC add_employee('Max', 'Mustermann', 'max@muster.at', '06999339838', 'IT_PROG', 8000, 230);
EXEC add_employee('Simone', 'Musterfrau', 'simone@muster.at', '06999339839', 'IT_PROG', 3000, 240);
EXEC add_employee('Julia', 'Musterfrau', 'julia@muster.at', '06999339839', 'IT_PROG', 11000, 240);

-- test
EXEC adjust_all_salaries();

-- verify
SELECT first_name, last_name, salary FROM employees WHERE email LIKE '%@muster.at';

-- cleanup
DELETE FROM employees WHERE email LIKE '%@muster.at';
