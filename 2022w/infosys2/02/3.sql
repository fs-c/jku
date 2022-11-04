-- Exercise 3)

SET ECHO ON

-- add column
-- ALTER TABLE departments ADD employees_count number(6);

-- intial setup
UPDATE departments SET employees_count = (
    SELECT COUNT(*) FROM employees
    WHERE employees.department_id = departments.department_id
);

CREATE OR REPLACE TRIGGER update_employees_count
AFTER INSERT OR UPDATE OR DELETE ON employees
BEGIN
    UPDATE departments SET employees_count = (
        SELECT COUNT(*) FROM employees
        WHERE employees.department_id = departments.department_id
    );
END update_employees_count;
/

-- initial count
SELECT department_name, employees_count FROM departments WHERE department_id = 50 OR department_id = 60;

-- add an employee and verify
EXEC add_employee('Max', 'Mustermann', 'max@muster.at', '06999339838', 'IT_PROG', 8000, 50);
SELECT department_name, employees_count FROM departments WHERE department_id = 50 OR department_id = 60;

-- move the employee to another department and verify
UPDATE employees SET department_id = 60 WHERE email = 'max@muster.at';
SELECT department_name, employees_count FROM departments WHERE department_id = 50 OR department_id = 60;

-- remove the employee and verify
DELETE FROM employees WHERE email = 'max@muster.at';
SELECT department_name, employees_count FROM departments WHERE department_id = 50 OR department_id = 60;

-- cleanup
-- ALTER TABLE departments DROP COLUMN employees_count;
