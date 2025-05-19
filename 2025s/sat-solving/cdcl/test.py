import sys
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
        if not path.endswith(".in"):
            continue

        with open(path, "r") as f, open(f"{path}.models.json", "r") as correct_models_stream:
            dimacs = f.read()
            correct_models = json.load(correct_models_stream)

        num_vars, clauses = parse_dimacs(dimacs)

        print(f"[debug] solving {path}...")

        try:
            actual_model = Solver(num_vars, clauses).solve()
        except Exception as e:
            print(f"[debug] [fail] solver crashed ({path})")
            print(e)
            failed.append(path)
            continue

        normalized_actual_model = [var if val else -var for var, val in actual_model.items()] if actual_model is not None else None

        if normalized_actual_model in correct_models or (normalized_actual_model is None and correct_models == []):
            print(f"[debug] [pass] {normalized_actual_model} in {correct_models}")
            passed.append(path)
        else:
            print(f"[debug] [fail] {normalized_actual_model} not in {correct_models}")
            failed.append(path)
            
    print(f"{len(passed)} passed, {len(failed)} failed")

    print(f"passed: {passed}")
    print(f"failed: {failed}")
