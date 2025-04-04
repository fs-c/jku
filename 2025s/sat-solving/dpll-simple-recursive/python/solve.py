import copy

def parse_dimacs(path: str) -> list[list[(int, bool)]]:
    clauses = []
    with open(path, 'r') as f:
        for line in f:
            if line.startswith('c'):
                continue
            if line.startswith('p'):
                continue
            new_clause = [(abs(int(x)), True if int(x) > 0 else False) for x in line.split() if x != '0']
            # some weird input files have empty clauses, here we assume that this is a mistake and ignore them
            # but in principle it really means that the input formula is trivially unsatisfiable
            if len(new_clause) != 0:
                clauses.append(new_clause)
    return clauses

def solve(formula: list[list[(int, bool)]]) -> bool:
    formula = unit_propagation(formula)

    if any(len(clause) == 0 for clause in formula):
        return False

    if len(formula) == 0:
        return True

    first_variable = formula[0][0][0]

    # this is awful but it is what it is
    # (we need to deep copy because we modify the clauses in place in unit_propagation)
    formula_copy = copy.deepcopy(formula)

    return (solve(formula_copy + [[(first_variable, True)]]) or 
            solve(formula_copy + [[(first_variable, False)]]))

def unit_propagation(formula: list[list[(int, bool)]]) -> list[list[(int, bool)]]:
    while True:
        unit_clauses = [clause for clause in formula if len(clause) == 1]

        if len(unit_clauses) == 0:
            break

        for unit_clause in unit_clauses:
            if len(unit_clause) == 0:
                continue

            unit_var = unit_clause[0]
            neg_unit_var = (unit_var[0], not unit_var[1])

            formula = [[var for var in clause if not var == neg_unit_var] 
                       for clause in formula if not unit_var in clause]
    
    return formula

if __name__ == "__main__":
    path = "2025s/sat-solving/test-formulas/sat0.in"

    formula = parse_dimacs(path)

    solution = solve(formula)

    print(solution)
