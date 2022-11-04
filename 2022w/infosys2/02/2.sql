-- Exercise 2)

SET ECHO ON

CREATE OR REPLACE TRIGGER verify_manager_trigger
BEFORE INSERT OR UPDATE OF manager_id ON departments
FOR EACH ROW
DECLARE
    manger_department employees.department_id%type;
BEGIN
    IF :NEW.manager_id IS NOT NULL THEN
        SELECT department_id INTO manger_department FROM employees
        WHERE employee_id = :NEW.manager_id;

        IF manger_department != :NEW.department_id THEN
            raise_application_error(-20001,
                'Mitarbeiter kann nicht als Abteilungsleiter eingesetzt werden.');
        END IF;
    END IF;
END verify_manager_trigger;
/

-- verify that invalid update errors
UPDATE departments SET manager_id = 201 WHERE department_id = 10;

-- verify that invalid insert errors
INSERT INTO departments (department_id, department_name, manager_id, location_id)
VALUES (departments_seq.NEXTVAL, 'Test Department', 100, 1000);
