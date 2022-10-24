-- Exercise 2a)

CREATE OR REPLACE PROCEDURE adjust_salary(emp_id employees.employee_id%TYPE)
AS
    current_job employees.job_id%TYPE;
    current_salary employees.salary%TYPE;
    min_salary jobs.min_salary%TYPE;
    max_salary jobs.max_salary%TYPE;
BEGIN
    SELECT job_id, salary INTO current_job, current_salary FROM employees
    WHERE employee_id = emp_id;

    SELECT min_salary, max_salary INTO min_salary, max_salary FROM jobs
    WHERE job_id = current_job;
    
    dbms_output.put('current salary is ');
    dbms_output.put_line(current_salary);

    IF current_salary < min_salary THEN
        dbms_output.put_line('adjusted upwards');
        UPDATE employees SET salary = min_salary WHERE employee_id = emp_id;
    ELSIF current_salary > max_salary THEN
        dbms_output.put_line('adjusted downwards');
        UPDATE employees SET salary = max_salary WHERE employee_id = emp_id;
    END IF;
EXCEPTION
    WHEN NO_DATA_FOUND THEN
        DBMS_OUTPUT.PUT_LINE('Given employee does not exist.');
END adjust_salary;
/

-- create employees with 1. correct, 2. low and 3. high salary for their job
-- IT_PROG is [4000, 10000]
EXEC add_employee('Max', 'Mustermann', 'max@muster.at', '06999339838', 'IT_PROG', 8000, 230);
EXEC add_employee('Simone', 'Musterfrau', 'simone@muster.at', '06999339839', 'IT_PROG', 3000, 240);
EXEC add_employee('Julia', 'Musterfrau', 'julia@muster.at', '06999339839', 'IT_PROG', 11000, 240);

BEGIN
    -- adjust salaries of newly created employees
    FOR emp IN (SELECT * FROM employees WHERE email LIKE '%@muster.at') LOOP
        adjust_salary(emp.employee_id);
    END LOOP;
END;
/

--- attempt to adjust salary for nonexistent employee
EXEC adjust_salary(1);

--- verify
SELECT first_name, last_name, salary FROM employees WHERE email LIKE '%@muster.at';

-- cleanup
DELETE FROM employees WHERE email LIKE '%@muster.at';
