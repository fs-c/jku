-- Exercise 1b)

SET ECHO ON

CREATE OR REPLACE PROCEDURE add_employee(
    fname employees.first_name%TYPE, lname employees.last_name%TYPE,
    email employees.email%TYPE, phone employees.phone_number%TYPE,
    emp_job_id employees.job_id%TYPE, salary employees.salary%TYPE,
    dept_id employees.department_id%TYPE
) AS
    dummy_job_id jobs.job_id%TYPE;
    dummy_dept_id departments.department_id%TYPE;
BEGIN
    -- attempt to fetch job and dept with the given ids, will throw NO_DATA_FOUND 
    -- if either doesn't exist
    SELECT job_id INTO dummy_job_id FROM jobs WHERE emp_job_id = job_id;
    SELECT department_id INTO dummy_dept_id FROM departments
        WHERE department_id = dept_id;
    
    INSERT INTO employees VALUES (
        employees_seq.NEXTVAL, fname, lname, email, phone, SYSDATE, 
        emp_job_id, salary, NULL, NULL, dept_id
    );
EXCEPTION
    WHEN NO_DATA_FOUND THEN
        DBMS_OUTPUT.PUT_LINE('Given job or department does not exist.');
END add_employee;
/

-- run tests, first two run fine the others have wrong inputs
EXEC add_employee('Max', 'Mustermann', 'max@muster.at', '06999339838', 'IT_PROG', 8000, 230);
EXEC add_employee('Simone', 'Musterfrau', 'simone@muster.at', '06999339839', 'IT_PROG', 7000, 240);
EXEC add_employee('Max', '1Wrong', 'max1@muster.at', '06999339838', 'DOESNT_EXIST', 8000, 230);
EXEC add_employee('Max', 'Wrong1', 'max2@muster.at', '06999339838', 'IT_PROG', 8000, 0);
EXEC add_employee('Max', '2Wrong', 'max3@muster.at', '06999339838', 'DOESNT_EXIST', 8000, 0);

-- verify
SELECT * FROM employees WHERE first_name = 'Max' OR first_name = 'Simone';

-- cleanup
DELETE FROM employees WHERE email LIKE '%@muster.at';
