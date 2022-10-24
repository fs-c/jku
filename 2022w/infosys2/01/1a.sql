-- Exercise 1a)

SET ECHO ON

CREATE OR REPLACE PROCEDURE create_dept (
    dept_name departments.department_name%TYPE, loc_id locations.location_id%TYPE
) AS
    dummy_loc_id locations.location_id%TYPE;
BEGIN
    -- attempt to fetch location with the given id, will throw NO_DATA_FOUND 
    -- if it doesn't exist
    SELECT location_id INTO dummy_loc_id FROM locations WHERE location_id = loc_id;

    -- insert the new department, leave manager empty
    INSERT INTO departments VALUES (
        departments_seq.NEXTVAL, dept_name, NULL, loc_id
    );
EXCEPTION
    WHEN NO_DATA_FOUND THEN
        DBMS_OUTPUT.PUT_LINE('Could not find location with the given ID.');
END create_dept;
/

-- run tests (first two run fine, third one will fail because the location doesn't exist)
EXEC create_dept('Test Department 1', 1000);
EXEC create_dept('Test Department 2', 3200);
EXEC create_dept('Test Department 3', 1);

-- verify
SELECT * FROM departments WHERE department_name LIKE 'Test Department _';

-- cleanup
DELETE FROM departments WHERE department_name LIKE 'Test Department _';
