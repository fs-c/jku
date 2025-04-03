import sys

def parse_cnf_formula(file_path):
    with open(file_path, "r") as file:
        content = file.read().strip()

    clauses = content.split("&")
    variable_map = {}
    next_var_id = 1
    parsed_clauses = []

    for clause in clauses:
        clause = clause.strip().strip("() ")
        literals = clause.split(" | ")
        parsed_clause = []
        
        for literal in literals:
            is_negated = literal.startswith("!")
            variable = literal[1:] if is_negated else literal
            
            if variable not in variable_map:
                variable_map[variable] = next_var_id
                next_var_id += 1
            
            parsed_clause.append(-variable_map[variable] if is_negated else variable_map[variable])
        
        parsed_clauses.append(parsed_clause)
    
    return variable_map, parsed_clauses

def print_dimacs(variable_map, parsed_clauses):
    num_variables = len(variable_map)
    num_clauses = len(parsed_clauses)
    
    print(f"p cnf {num_variables} {num_clauses}")
    for clause in parsed_clauses:
        print(" ".join(map(str, clause)) + " 0")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python cnf_to_dimacs.py <path_to_cnf_file>")
        sys.exit(1)
    
    file_path = sys.argv[1]
    variable_map, parsed_clauses = parse_cnf_formula(file_path)
    print_dimacs(variable_map, parsed_clauses)
    print(variable_map)