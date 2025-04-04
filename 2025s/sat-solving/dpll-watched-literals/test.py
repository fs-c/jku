import sys
from pysat.solvers import Cadical195
import time
from typing import List
import json as json

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

        if not path.endswith(".in"):
            continue

        with open(path, "r") as f:
            dimacs = f.read()

        num_vars, clauses = parse_dimacs(dimacs)

        with Cadical195(bootstrap_with=[[lit.var if lit.value else -lit.var for lit in clause.literals] for clause in clauses]) as correct_solver:            
            time_before = time.time()
            correct_solver.solve()
            time_after = time.time()

            if time_after - time_before > 0.00001:
                skipped.append(path)
                print(f"[debug] [skip] {path} (took {time_after - time_before} seconds)")
                continue

            try:
                actual_model = Solver(num_vars, clauses).solve()
            except Exception as e:
                print(f"[debug] [fail] solver crashed ({path})")
                print(e)
                failed.append(path)
                continue

            correct_models = json.load(open(f"{path}.models.json"))

            if (actual_model is None and correct_models != []) or (actual_model is not None and not [var if val else -var for var, val in actual_model.items()] in correct_models):
                print(f"[debug] [fail] actual: {actual_model}, correct: {correct_models} ({path})")
                failed.append(path)
            else:
                print(f"[debug] [pass] actual: {actual_model}, correct: {correct_models} ({path})")
                passed.append(path)

    print(f"{len(passed)} passed, {len(skipped)} skipped, {len(failed)} failed")

    print(f"passed: {passed}")
    print(f"skipped: {skipped}")
    print(f"failed: {failed}")
