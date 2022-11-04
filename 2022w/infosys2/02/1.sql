-- Exercise 1)

SET ECHO ON

CREATE OR REPLACE TRIGGER adjust_salary_trigger
BEFORE INSERT OR UPDATE OF salary ON employees
FOR EACH ROW
DECLARE
    min_salary jobs.min_salary%TYPE;
    max_salary jobs.max_salary%TYPE;
BEGIN
    dbms_output.put_line('adjust salary trigger called');

    SELECT min_salary, max_salary INTO min_salary, max_salary FROM jobs
    WHERE job_id = :NEW.job_id;

    dbms_output.put('current salary is ');
    dbms_output.put_line(:NEW.salary);
    
    IF :NEW.salary < min_salary THEN
        dbms_output.put_line('adjusted upwards');
        :NEW.salary := min_salary;
    ELSIF :NEW.salary > max_salary THEN
        dbms_output.put_line('adjusted downwards');
        :NEW.salary := max_salary;
    END IF;
END adjust_salary_trigger;
/

-- create employees with 1. correct, 2. low and 3. high salary for their job
-- IT_PROG is [4000, 10000]
EXEC add_employee('Max', 'Mustermann', 'max@muster.at', '06999339838', 'IT_PROG', 8000, 230);
EXEC add_employee('Simone', 'Musterfrau', 'simone@muster.at', '06999339839', 'IT_PROG', 3000, 240);
EXEC add_employee('Julia', 'Musterfrau', 'julia@muster.at', '06999339839', 'IT_PROG', 11000, 240);

-- verify that updating also gets adjusted
UPDATE employees SET salary = 10000 WHERE email = 'max@muster.at';

--- verify
SELECT first_name, last_name, salary FROM employees WHERE email LIKE '%@muster.at';

-- cleanup
DELETE FROM employees WHERE email LIKE '%@muster.at';