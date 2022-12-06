SELECT e.employee_id, XMLElement("emp",
    XMLAttributes(employee_id, last_name, job_title),
    XMLElement("cursalary", salary)
) FROM employees e, jobs j WHERE department_id = 90 AND e.job_id = j.job_id;