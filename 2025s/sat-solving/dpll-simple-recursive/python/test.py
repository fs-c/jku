import sys
from pysat.solvers import Cadical195
import time

from solve import parse_dimacs, solve

if __name__ == "__main__":
    if len(sys.argv) == 1:
        print("Usage: python test.py <path-to-dimacs-file-1> ... <path-to-dimacs-file-n>")
        sys.exit(1)

    any_failed = False
    skipped = 0
    
    for path in sys.argv[1:]:
        formula = parse_dimacs(path)

        with Cadical195(bootstrap_with=[[-x[0] if not x[1] else x[0] for x in clause] for clause in formula]) as solver:
            time_before = time.time()
            actual_solution = solver.solve()
            time_after = time.time()

            if time_after - time_before > 0.0001:
                print(f"skipping {path} because fast solver took {time_after - time_before} seconds")
                skipped += 1
                continue

            solution = solve(formula)

            if solution != actual_solution:
                print(f"simple recursive: {solution}, actual: {actual_solution}! ({path})")
                any_failed = True

    if not any_failed:
        print(f"all tests passed (skipped {skipped} tests)")
    else:
        print(f"some tests failed (skipped {skipped} tests)")

