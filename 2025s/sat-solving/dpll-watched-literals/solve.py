from typing import List, Set, Dict, Optional, Tuple
from collections import deque

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

    def __repr__(self) -> str:
        return f"{' & '.join([str(lit) for lit in self.literals])}"

class Solver:
    def __init__(self, num_vars: int, clauses: List[Clause]):
        self.num_vars = num_vars
        self.clauses = clauses

        self.assignment: Dict[int, Optional[bool]] = {i: None for i in range(1, num_vars + 1)}

        self.decision_level = 0
        self.decision_stack: List[Tuple[Literal, int]] = []

        self.propagation_queue: deque[Literal] = deque()

        # Initialize watch lists
        self.watch_lists: Dict[Literal, Set[Clause]] = {lit: set() for lit in self._get_all_literals()}
        for clause in clauses:
            if len(clause.literals) >= 1:
                self.watch_lists[clause.literals[0]].add(clause)
            if len(clause.literals) >= 2:
                self.watch_lists[clause.literals[1]].add(clause)

    def _get_all_literals(self) -> Set[Literal]:
        literals: Set[Literal] = set()
        for i in range(1, self.num_vars + 1):
            literals.add(Literal(i, True))
            literals.add(Literal(i, False))
        return literals

    def _get_unit_literal(self, clause: Clause) -> Optional[Literal]:
        unassigned = [lit for lit in clause.literals if self.assignment[lit.var] is None]
        if len(unassigned) == 1:
            return unassigned[0]
        return None

    def _is_clause_satisfied(self, clause: Clause) -> bool:
        return any(self.assignment[lit.var] == lit.value for lit in clause.literals)

    def _is_clause_conflicting(self, clause: Clause) -> bool:
        return all(self.assignment[lit.var] == (not lit.value) for lit in clause.literals)

    def _update_watched_literals(self, clause: Clause, old_lit: Literal) -> bool:
        # Try to find a new watched literal
        for potential_lit in clause.literals:
            if potential_lit != old_lit and self.assignment[potential_lit.var] is None:
                # Update watch lists
                self.watch_lists[old_lit].remove(clause)
                self.watch_lists[potential_lit].add(clause)
                return True
        return False

    def _propagate(self) -> Optional[Clause]:
        while self.propagation_queue:
            lit = self.propagation_queue.popleft()
            # get a copy of the watch list for this literal because we may modify it during iteration
            watch_list = list(self.watch_lists[lit])

            for clause in watch_list:
                if self._is_clause_satisfied(clause):
                    continue

                if self._is_clause_conflicting(clause):
                    return clause

                unit_lit = self._get_unit_literal(clause)
                if unit_lit:
                    self.assignment[unit_lit.var] = unit_lit.value
                    self.propagation_queue.append(unit_lit)
                else:
                    # Try to find a new watched literal
                    if not self._update_watched_literals(clause, lit):
                        # If we can't find a new watched literal and the clause is not satisfied,
                        # it means all other literals are false
                        return clause
        return None

    def _make_decision(self) -> Optional[Literal]:
        for var in range(1, self.num_vars + 1):
            if self.assignment[var] is None:
                # Try both true and false assignments
                # todo: this looks wrong, why make this dependent on the decision level?
                if self.decision_level % 2 == 0:
                    return Literal(var, True)
                else:
                    return Literal(var, False)
        return None

    def _backtrack(self) -> bool:
        if not self.decision_stack:
            return False
        
        while self.decision_stack:
            lit, level = self.decision_stack.pop()
            self.assignment[lit.var] = None
            if level < self.decision_level:
                self.decision_level = level
                self.decision_stack.append((lit, level))
                return True
        return False

    def solve(self) -> Optional[Dict[int, bool]]:
        while True:
            # Propagate unit clauses
            conflict = self._propagate()
            if conflict:
                if not self._backtrack():
                    return None
                continue

            # Make a decision
            # todo: this always returns a true literal, should this not also explore false literals?
            decision = self._make_decision()
            if not decision:
                return {var: val for var, val in self.assignment.items() if val is not None}

            self.decision_level += 1
            self.assignment[decision.var] = True
            self.decision_stack.append((decision, self.decision_level))
            self.propagation_queue.append(decision)

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

def solve_dimacs(dimacs: str) -> Optional[Dict[int, bool]]:
    num_vars, clauses = parse_dimacs(dimacs)
    solver = Solver(num_vars, clauses)
    return solver.solve()

if __name__ == "__main__":
    with open("../test-formulas/sat0.in", "r") as f:
        dimacs = f.read()

    print(f"{solve_dimacs(dimacs)}")
