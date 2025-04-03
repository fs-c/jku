from pysat.solvers import Cadical195

CLAUSES = [
    [-1, -2, 3, -4],
    [-3, 2, -5, -4],
    [3, 1, 5, -2],
    [-3, 4, -1, -2],
    [-4, 3, 5, 1],
    [3, -2, 1, 4],
    [5, -3, -1, -2],
    [5, -1, 2, -3],
    [3, 5, -1, -2],
    [-2, 4, -1, -3],
    [-1, -3, 2, 5],
    [-1, -5, -2, 3],
    [2, -4, 5, 3],
    [5, -1, 3, -4],
    [-1, 3, 5, 4],
    [-1, 2, -3, -5],
    [1, -4, -2, -5],
]

def count_solutions(clauses):
    solutions = 0

    with Cadical195(bootstrap_with=clauses) as solver:
        while solver.solve():
            solutions += 1

            model = solver.get_model()
            print(model)
            
            solver.add_clause([-x for x in model])
        
    return solutions

if __name__ == "__main__":
    print(count_solutions(CLAUSES))
