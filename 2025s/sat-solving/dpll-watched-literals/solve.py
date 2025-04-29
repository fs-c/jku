from typing import List, Set, Dict, Optional, Tuple
from collections import deque
import sys

"""
http://minisat.se/downloads/MiniSat.pdf
"""

Assignment = Dict[int, Optional[bool]]

class Literal:
    def __init__(self, var: int, value: bool):
        self.var = var
        self.value = value

    def __neg__(self) -> 'Literal':
        return Literal(self.var, not self.value)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Literal) and self.var == other.var and self.value == other.value

    def __hash__(self) -> int:
        return hash((self.var, self.value))

    def __repr__(self) -> str:
        return f"{'' if self.value else '!'}x{self.var}"

class Clause:
    def __init__(self, literals: List[Literal]):
        self.literals = literals

    def is_satisfied(self, assignment: Assignment) -> bool:
        return any(assignment[lit.var] == lit.value for lit in self.literals)
    
    def __eq__(self, other: object) -> bool:
        return isinstance(other, Clause) and self.literals == other.literals
    
    def __hash__(self) -> int:
        return hash(tuple(self.literals))

    def __repr__(self) -> str:
        return f"{' & '.join([str(lit) for lit in self.literals])}"

class Solver:
    def __init__(self, num_vars: int, clauses: List[Clause]):
        self.num_vars = num_vars
        self.clauses = clauses

        # write access to this is only allowed through _assign_literal
        self.assignment: Assignment = {i: None for i in range(1, num_vars + 1)}

        # keep track of assignments for backtracking
        # stack to remember order in which variables were assigned
        self.trail: List[Literal] = []
        # for each decision level, remember the trail height (invariant: len(control) == decision level)
        self.control: List[int] = []

        self.propagation_queue: deque[Literal] = deque()

        self.all_literals: Set[Literal] = set()
        for i in range(1, num_vars + 1):
            self.all_literals.add(Literal(i, True))
            self.all_literals.add(Literal(i, False))

        # initialize watch lists
        self.watch_lists: Dict[Literal, Set[Clause]] = {lit: set() for lit in self.all_literals}
        for clause in clauses:
            if len(clause.literals) >= 1:
                self.watch_lists[clause.literals[0]].add(clause)
            if len(clause.literals) >= 2:
                self.watch_lists[clause.literals[1]].add(clause)

    def _assign_literal(self, lit: Literal) -> bool:
        # first, perform the assignment
        self.assignment[lit.var] = lit.value
        self.trail.append(lit)

        # then handle all clauses watching the variable we just assigned
        # (only need to consider the clauses that are watching the negation, the others are trivially satisfied)
        # create a copy of the watch list because we might mutate the original while iterating
        watch_list = list(self.watch_lists[-lit])

        for clause in watch_list:
            # if the clause is (was) already satisfied there's nothing to do
            if clause.is_satisfied(self.assignment):
                continue

            unassigned = [lit for lit in clause.literals if self.assignment[lit.var] is None]
            if len(unassigned) == 0:
                # there are no more unassigned literals and the clause is not satisfied; conflict
                return False
            elif len(unassigned) == 1:
                # there is exactly one unassigned literal left; unit clause
                self.propagation_queue.append(unassigned[0])
            else:
                # we have more than one unassigned literal left; update the watch list
                for potential_lit in unassigned:
                    if not clause in self.watch_lists[potential_lit]:
                        self.watch_lists[potential_lit].add(clause)
                        self.watch_lists[-lit].remove(clause)
                        break
                assert clause not in self.watch_lists[-lit], \
                    f"clause {clause} is still watching {lit} but it should have been removed"

        return True

    def _propagate(self) -> bool:
        while self.propagation_queue:
            # get the next unit clause literal to assign (unless it's already assigned, in which case we skip)
            unit_lit = self.propagation_queue.popleft()
            if self.assignment[unit_lit.var] == unit_lit.value:
                continue

            if not self._assign_literal(unit_lit):
                self.propagation_queue.clear()
                return True

        return False

    """
    walks back the trail until the target height is reached, unassigning variables as it goes
    returns the last literal that was removed from the trail (or None if the trail was below target height)
    """
    def _backtrack(self, target_height: int) -> Optional[Literal]:
        assert len(self.trail) >= target_height, \
            f"current trail height ({len(self.trail)}) >= target height ({target_height}), " \
            f"this is fine in principle but it's probably a mistake"

        lit = None
        while len(self.trail) > target_height:
            lit = self.trail.pop()
            self.assignment[lit.var] = None

        return lit

    def solve(self) -> Optional[Assignment]:
        # handle special cases where formula is trivially satisfiable or unsatisfiable
        # this could be part of a more general simplification/preprocessing step
        if not self.clauses:
            return {}
        if not self.all_literals:
            return None
        
        iteration_count = 0
        max_iterations = 100000

        while True:
            iteration_count += 1
            if iteration_count > max_iterations:
                print(f"exceeded maximum iterations ({max_iterations})")
                return None
            
            print(self.trail)

            conflict = self._propagate()
            if conflict:
                if len(self.control) == 0:
                    return None

                target_height = self.control.pop()
                last_lit = self._backtrack(target_height)

                if last_lit is not None:
                    self.propagation_queue.append(-last_lit)
            else:
                # select a new decision variable
                unassigned = [lit for lit in self.all_literals if self.assignment[lit.var] is None]
                if not unassigned:
                    return {var: val for var, val in self.assignment.items() if val is not None}

                lit = unassigned[0]

                self.control.append(len(self.trail))
                self.propagation_queue.append(lit)

def parse_dimacs(dimacs: str) -> Tuple[int, List[Clause]]:
    lines = dimacs.strip().split('\n')
    num_vars = 0
    clauses: List[Clause] = []

    for line in lines:
        line = line.strip()
        if line.startswith('p'):
            _, _, num_vars, _ = line.split()
            num_vars = int(num_vars)
        elif not line.startswith('c') and line:
            literals: List[Literal] = []
            for lit in line.split()[:-1]:  # Skip the trailing 0
                lit = int(lit)
                literals.append(Literal(abs(lit), lit > 0))
            clauses.append(Clause(literals))

    return num_vars, clauses

def solve_dimacs(dimacs: str) -> Optional[Assignment]:
    num_vars, clauses = parse_dimacs(dimacs)
    solver = Solver(num_vars, clauses)
    return solver.solve()

if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else "test-formulas/add8.in"

    with open(path, "r") as f:
        dimacs = f.read()

    print(f"{solve_dimacs(dimacs)}")
