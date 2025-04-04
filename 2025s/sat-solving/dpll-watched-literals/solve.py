from typing import List, Set, Dict, Optional, Tuple
from collections import deque

"""
https://lara.epfl.ch/w/_media/projects:minisat-anextensiblesatsolver.pdf
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

    def __repr__(self) -> str:
        return f"{' & '.join([str(lit) for lit in self.literals])}"

class Solver:
    def __init__(self, num_vars: int, clauses: List[Clause]):
        self.num_vars = num_vars
        self.clauses = clauses

        # write access to this is only allowed through _assign_literal
        self.assignment: Assignment = {i: None for i in range(1, num_vars + 1)}

        # keeps track of assignments for backtracking
        self.decision_level = 0
        self.trail: List[Tuple[Literal, int]] = []

        self.unit_literal_queue: deque[Literal] = deque()

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
        self.trail.append((lit, self.decision_level))

        # then handle the clauses the negation of the literal we just assigned is watching
        # (the negation because the ones watching the literal itself are now trivially satisfied)
        # create a copy of the watch list because we might mutate the original while iterating
        watch_list = list(self.watch_lists[-lit])
        for clause in watch_list:
            # if the clause is satisfied (under the new assignment) there's nothing to do
            if clause.is_satisfied(self.assignment):
                continue

            unassigned = [lit for lit in clause.literals if self.assignment[lit.var] is None]
            if len(unassigned) == 0:
                # there are no more unassigned literals and the clause is not satisfied; conflict
                return False
            elif len(unassigned) == 1:
                # there is exactly one unassigned literal left; unit clause
                self.unit_literal_queue.append(unassigned[0])
            else:
                # we have more than one unassigned literal left; update the watch list
                for potential_lit in unassigned:
                    if not clause in self.watch_lists[potential_lit]:
                        self.watch_lists[potential_lit].add(clause)
                        self.watch_lists[-lit].remove(clause)
                        break

                raise Exception("invalid state: no unassigned literal is unwatched")

        return True

    def _propagate(self) -> bool:
        while self.unit_literal_queue:
            # get the next unit clause literal to assign (unless it's already assigned, in which case we skip)
            unit_lit = self.unit_literal_queue.popleft()
            if self.assignment[unit_lit.var] == unit_lit.value:
                continue

            if not self._assign_literal(unit_lit):
                return True

        return False

    def _backtrack(self) -> bool:
        self.decision_level -= 1
        while self.trail:
            lit, level = self.trail.pop()
            self.assignment[lit.var] = None
            if level < self.decision_level:
                self.decision_level = level
                self.trail.append((lit, level))
                return True
        return False

    def solve(self) -> Optional[Assignment]:
        while True:
            conflict = self._propagate()
            if conflict:
                if not self._backtrack():
                    return None
            else:
                unassigned = [lit for lit in self.all_literals if self.assignment[lit.var] is None]
                if not unassigned:
                    return {var: val for var, val in self.assignment.items() if val is not None}

                self.decision_level += 1
                self.unit_literal_queue.append(unassigned[0])

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
            # some weird input files have empty clauses, here we assume that this is a mistake and ignore them
            # since pysat also fails on them this seems justified
            # but in principle it really means that the input formula is trivially unsatisfiable
            if len(literals) > 0:
                clauses.append(Clause(literals))

    return num_vars, clauses

def solve_dimacs(dimacs: str) -> Optional[Assignment]:
    num_vars, clauses = parse_dimacs(dimacs)
    solver = Solver(num_vars, clauses)
    return solver.solve()

if __name__ == "__main__":
    with open("../test-formulas/unit5.in", "r") as f:
        dimacs = f.read()

    print(f"{solve_dimacs(dimacs)}")
