import sys

def parse_dimacs(path: str) -> list[list[(int, bool)]]:
    clauses = []
    with open(path, 'r') as f:
        for line in f:
            if line.startswith('c'):
                continue
            if line.startswith('p'):
                continue
            clauses.append([(abs(int(x)), True if int(x) > 0 else False) for x in line.split() if x != '0'])
    return clauses

def solve(formula: list[list[(int, bool)]]) -> list[(int, bool)]:
    lits = set()
    for clause in formula:
        for lit in clause:
            lits.add(lit[0])

    assignment = []

    return solve_recursive(lits, formula, assignment)

def solve_recursive(lits: set[int], formula: list[list[(int, bool)]], assignment: list[(int, bool)]) -> bool:
    pure_elimination(lits, formula)
    propagate_units(formula)

    if any(len(clause) == 0 for clause in formula):
        return False

    if len(formula) == 0:
        return True

    first_variable = formula[0][0][0]

    return solve_recursive(lits, copy.deepcopy(formula + [[(first_variable, True)]]), assignment) or solve_recursive(lits, formula + [[(first_variable, False)]], assignment)

def propagate_units(formula: list[list[(int, bool)]]) -> list[(int, bool)]:
    assignment = []

    while True:
        unit_clauses = [clause for clause in formula if len(clause) == 1]

        if len(unit_clauses) == 0:
            break

        for unit_clause in unit_clauses:
            # at this point the clauses may be empty (this is called before the check for empty clauses) 
            if len(unit_clause) == 0:
                continue

            var = unit_clause[0]
            var_to_remove = (var[0], not var[1])

            assignment.append(var)

            for clause in formula:
                if len(clause) == 0:
                    continue

                if var in clause and clause != unit_clause:
                    formula.remove(clause)
                else:
                    if var_to_remove in clause:
                        clause.remove(var_to_remove)
    
    return assignment


def pure_elimination(lits: set[int], formula: list[list[(int, bool)]]) -> list[list[(int, bool)]]:
    for lit in lits:
        first_observed_sign = None
        is_pure = True

        for clause in formula:
            if not lit in clause:
                continue
            
            if first_observed_sign is None:
                first_observed_sign = clause[0][1]
            elif first_observed_sign != clause[0][1]:
                is_pure = False
                break

        if first_observed_sign is not None and is_pure:
            formula.append((lit, first_observed_sign))

            for clause in formula:
                if clause.count((lit, not first_observed_sign)) > 0:
                    formula.remove(clause)

    return formula

def all_lits_covered(lits: set[int], formula: list[list[(int, bool)]]) -> bool:
    for lit in lits:
        if not any(lit in clause for clause in formula):
            return False
    return True

if __name__ == "__main__":
    path = "2025s/sat-solving/test-formulas/sat0.in"
    formula = parse_dimacs(path)
    solution = solve(formula)
    print(solution)
