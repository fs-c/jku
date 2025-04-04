import sys
from pysat.solvers import Cadical195
import time
from typing import List

from solve import Solver, parse_dimacs

if __name__ == "__main__":
    if len(sys.argv) == 1:
        print("Usage: python test.py <path-to-dimacs-file-1> ... <path-to-dimacs-file-n>")
        sys.exit(1)

    passed: List[str] = []
    skipped: List[str] = []
    failed: List[str] = []
    
    for path in sys.argv[1:]:
        print(f"testing {path}...")

        with open(path, "r") as f:
            dimacs = f.read()

        num_vars, clauses = parse_dimacs(dimacs)

        with Cadical195(bootstrap_with=[[lit.var if lit.value else -lit.var for lit in clause.literals] for clause in clauses]) as correct_solver:
            time_before = time.time()
            correct_solver.solve()
            raw_correct_model = correct_solver.get_model()
            correct_model = {abs(val): val > 0 for val in correct_solver.get_model()} if raw_correct_model else None
            time_after = time.time()

            if time_after - time_before > 0.0001:
                skipped.append(path)
                continue

            actual_model = Solver(num_vars, clauses).solve()

            if actual_model != correct_model:
                print(f"[debug] actual: {actual_model}, correct: {correct_model}! ({path})")
                failed.append(path)
            else:
                passed.append(path)

    print(f"{len(passed)} passed, {len(skipped)} skipped, {len(failed)} failed")

    print(f"passed: {passed}")
    print(f"skipped: {skipped}")
    print(f"failed: {failed}")
