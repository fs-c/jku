import sys
from pysat.solvers import Cadical195
from pysat.formula import CNF
import json

if __name__ == "__main__":
    if len(sys.argv) == 1:
        print("Usage: python write-all-models.py <path-to-dimacs-file-1> ... <path-to-dimacs-file-n>")
        sys.exit(1)

    for path in sys.argv[1:]:
        if not path.endswith(".in"):
            continue
        formula = CNF(from_file=path)

        solver = Cadical195()
        for clause in formula.clauses:
            solver.add_clause(clause)

        models = list(solver.enum_models())
        with open(f"{path}.models.json", "w") as f:
            json.dump(models, f)
