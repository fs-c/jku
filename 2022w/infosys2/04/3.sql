SET ECHO ON

-- a)
SELECT e.employee_id, XMLElement("emp",
    XMLAttributes(employee_id, last_name, job_title),
    XMLForest(salary, min_salary, max_salary)
) FROM employees e, jobs j WHERE department_id = 90 AND e.job_id = j.job_id;

-- b)
SELECT XMLElement("dep", 
    XMLElement("meta", XMLAttributes(d.department_id), XMLElement("name", d.department_name)),
    XMLElement("stats",
        XMLElement("empcount", COUNT(employee_id)),
        XMLElement("avgsal", AVG(salary))
    )
) FROM departments d, employees e
WHERE d.department_id = e.department_id AND department_name = 'Sales' OR department_name = 'Marketing' OR department_name = 'IT' GROUP BY d.department_id, d.department_name;

-- c)
SELECT XMLElement("region",
    XMLAttributes(r.region_id, r.region_name),
    (SELECT XMLAgg(XMLElement("country",
        XMLAttributes(c.country_id, c.country_name),
        (SELECT XMLAgg(XMLElement("location",
            XMLAttributes(l.location_id, l.postal_code, l.city)))
        FROM locations l
        WHERE l.country_id = c.country_id)))
    FROM countries c
    WHERE c.region_id = r.region_id))
FROM regions r WHERE r.region_name = 'Asia';
