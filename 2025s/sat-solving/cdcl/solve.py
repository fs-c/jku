from typing import List, Set, Dict, Optional, Tuple, NamedTuple
from collections import deque
import sys
from enum import Enum, auto
import random

"""
http://minisat.se/downloads/MiniSat.pdf
https://cse442-17f.github.io/Conflict-Driven-Clause-Learning/
https://courses.cs.washington.edu/courses/cse507/17wi/lectures/L02.pdf
https://ics.uci.edu/~dechter/courses/ics-275a/winter-2016/readings/SATHandbook-CDCL.pdf
"""

# todo: it seems like the following uses "literal" and "variable" in an incorrect way; 
#  a literal is either xi or -xi, both of which are variables

Assignment = Dict[int, Optional[bool]]

class PropagationResult(Enum):
    NO_CONFLICT = auto()
    CONFLICT = auto()

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
        return f"{'' if self.value else '¬'}x{self.var}"

class Clause:
    def __init__(self, literals: Set[Literal]):
        self.literals = literals

    def is_satisfied(self, assignment: Assignment) -> bool:
        return any(assignment[lit.var] == lit.value for lit in self.literals)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Clause) and self.literals == other.literals

    def __hash__(self) -> int:
        return hash(tuple(self.literals))

    def __repr__(self) -> str:
        return f"{' | '.join([str(lit) for lit in self.literals])}"

    def copy(self) -> 'Clause':
        return Clause(self.literals.copy())

class TrailEntry(NamedTuple):
    literal: Literal
    reason: Optional[Clause]

class Solver:
    @staticmethod
    def _resolve(*args: Literal) -> Clause:
        """
        resolve a list of clauses, returning a new clause that is the result of resolving all of them
        """
        unique_literals: set[Literal] = set(args)
        resolved: set[Literal] = set()

        for lit in unique_literals:
            if -lit in unique_literals:
                continue

            resolved.add(lit)

        return Clause(resolved)

    def __init__(self, num_vars: int, clauses: List[Clause]):
        self.num_vars = num_vars
        self.clauses = clauses

        # write access to this is only allowed through _assign_literal
        self.assignment: Assignment = {i: None for i in range(1, num_vars + 1)}
        # for each variable, remember the decision level at which it was assigned
        # todo: this is duplicate information to the trail but it was more convenient like this, should be refactored
        self.var_to_level: Dict[int, Optional[int]] = {}

        # stack to remember order in which variables were assigned, and the reason (= clause) for the assignment
        # (None if the assignment was due to a decision and not because it was implied during propagation)
        self.trail: List[TrailEntry] = []
        # for each decision level, remember the trail height (invariant: len(control) == current decision level)
        self.control: List[int] = [] # todo: does an initial value make sense?

        # queue of literals to assign during propagation with the reason for assignment (see trail)
        self.propagation_queue: deque[Tuple[Literal, Clause | None]] = deque()

        # initialize list of literals to consider for assignment
        self.all_literals: Set[Literal] = set() 
        for clause in clauses:
            for lit in clause.literals:
                self.all_literals.add(lit)

        # initialize watch lists
        self.watch_lists: Dict[Literal, List[Clause]] = {lit:[] for lit in self.all_literals}
        for clause in clauses:
            literals = list(clause.literals)
            if len(literals) >= 1:
                self.watch_lists[literals[0]].append(clause)
            if len(literals) >= 2:
                self.watch_lists[literals[1]].append(clause)

    def _decision_level(self) -> int:
        return len(self.control)

    def _find_unassigned_literals(self, literals: Set[Literal]) -> List[Literal]:
        return [lit for lit in literals if self.assignment[lit.var] is None]

    def _assign_and_propagate(self, lit: Literal, reason: Optional[Clause]) -> Tuple[PropagationResult, Optional[Clause]]:
        """attempt to assign a literal and propagate through watch lists"""

        # first, perform the assignment
        self.assignment[lit.var] = lit.value
        self.var_to_level[lit.var] = self._decision_level()
        self.trail.append(TrailEntry(lit, reason))

        # then, handle all clauses watching the variable we just assigned (only need to consider the 
        # clauses that are watching the negation, the others are trivially satisfied)
        # create a copy of the watch list so we can mutate the original while iterating
        watch_list = self.watch_lists.get(-lit, []).copy()

        for clause in watch_list:
            # if the clause was already satisfied there's nothing to do
            if clause.is_satisfied(self.assignment):
                continue

            unassigned = self._find_unassigned_literals(clause.literals)
            if len(unassigned) == 0:
                # there are no more unassigned literals and the clause is not satisfied (as per previous check) -> conflict
                return PropagationResult.CONFLICT, clause
            elif len(unassigned) == 1:
                # there is exactly one unassigned literal left -> unit clause, propagate the literal
                self.propagation_queue.append((unassigned[0], clause))
            else:
                # we have more than one unassigned literal left -> update the watch list
                for potential_lit in unassigned:
                    if not clause in self.watch_lists[potential_lit]:
                        self.watch_lists[potential_lit].append(clause)
                        self.watch_lists[-lit].remove(clause)
                        break
                assert clause not in self.watch_lists[-lit], \
                    f"clause {clause} is still watching {lit} but it should have been removed"

        return PropagationResult.NO_CONFLICT, None

    def _process_propagation_queue(self) -> Tuple[PropagationResult, Optional[Clause]]:
        """process the propagation queue until it's empty or a conflict is found"""

        while self.propagation_queue:
            # get the next literal to assign (unless it's already assigned, in which case we skip)
            lit, reason = self.propagation_queue.popleft()
            if self.assignment[lit.var] == lit.value:
                continue

            # assign the literal and perform unit propagation, this may push to the propagation queue
            result, conflict_clause = self._assign_and_propagate(lit, reason)   
            if result == PropagationResult.CONFLICT:
                self.propagation_queue.clear()
                return PropagationResult.CONFLICT, conflict_clause

        return PropagationResult.NO_CONFLICT, None

    def _backtrack(self, target_level: int) -> Optional[Literal]:
        """
        walks back the trail until the target decision level is reached, unassigning variables as it goes
        (all assignments at and below the target level are kept)
        returns the last literal that was removed from the trail (or None if nothing was removed)
        """

        if target_level >= self._decision_level():
            return None

        last_lit = None
        while self._decision_level() > target_level:
            target_height = self.control.pop()
            while len(self.trail) > target_height:
                last_lit, _ = self.trail.pop()
                self.assignment[last_lit.var] = None
                self.var_to_level[last_lit.var] = None

        return last_lit

    def _analyze_conflict_trail(self, conflict: Clause) -> Tuple[Clause, int]:
        """
        assuming that we just found the given conflict clause, this function will return an appropriate
        conflict clause and backtrack level based on the current trail
        largely based on the description in https://courses.cs.washington.edu/courses/cse507/17wi/lectures/L02.pdf,
        which seems suspicously simpler than others (e.g. the one in minisat)
        """

        def current_level_literals(clause: Clause) -> List[Literal]:
            return [lit for lit in clause.literals if self.var_to_level[lit.var] == self._decision_level()]
        
        learned_clause = conflict.copy()

        # only consider the trail content from the current decision level
        relevant_trail = self.trail[self.control[-1]:]

        # iterate through the trail in reverse order (most recent assignments first)
        for lit, reason in reversed(relevant_trail):
            if len(current_level_literals(learned_clause)) <= 1:
                break

            learned_clause = Solver._resolve(*learned_clause.literals, lit, *(reason or Clause(set())).literals)

        level = 0 if len(learned_clause.literals) <= 1 else sorted(self.var_to_level[lit.var] or 0 for lit in learned_clause.literals)[-2]

        return learned_clause, level

    def solve(self) -> Optional[Assignment]:
        # handle special cases where formula is trivially satisfiable or unsatisfiable
        # this could be part of a more general simplification/preprocessing step
        if not self.clauses:
            return {}
        if not self.all_literals:
            return None

        while True:
            result, conflict_clause = self._process_propagation_queue()
            if result == PropagationResult.CONFLICT:
                if self._decision_level() == 0:
                    return None

                assert conflict_clause is not None, "conflict without conflict clause, unexpected state"

                learned_clause, backtrack_level = self._analyze_conflict_trail(conflict_clause)
                if not learned_clause.literals:
                    return None

                # add the learned clause to our clause database
                # todo: factor out the watch list stuff (it's already in the constructor)
                self.clauses.append(learned_clause)
                literals = list(learned_clause.literals)
                if len(literals) >= 1:
                    self.watch_lists[literals[0]].append(learned_clause)
                if len(literals) >= 2:
                    self.watch_lists[literals[1]].append(learned_clause)

                _ = self._backtrack(backtrack_level)
            elif result == PropagationResult.NO_CONFLICT:
                # select a new decision variable
                unassigned = self._find_unassigned_literals(self.all_literals)
                if not unassigned:
                    return {var: val for var, val in self.assignment.items() if val is not None}

                # todo: for now we just pick a random unassigned literal, but something like VSIDS should be implemented
                lit = random.choice(unassigned)

                self.control.append(self._decision_level())
                self.propagation_queue.append((lit, None))
            else:
                assert False, f"unknown propagation result: {result}"

def parse_dimacs(dimacs: str) -> Tuple[int, List[Clause]]:
    # not sure what's up with the type checker here, it's not happy with the split()s

    lines = dimacs.strip().split('\n')
    num_vars = 0
    clauses: List[Clause] = []

    for line in lines:
        line = line.strip()
        if line.startswith('p'):
            _, _, num_vars, _ = line.split() # type: ignore
            num_vars = int(num_vars)
        elif not line.startswith('c') and line:
            literals: Set[Literal] = set()
            for lit in line.split()[:-1]: # skip the trailing 0
                lit = int(lit) # type: ignore
                literals.add(Literal(abs(lit), lit > 0)) # type: ignore
            clauses.append(Clause(literals))

    return num_vars, clauses

def solve_dimacs(dimacs: str) -> Optional[Assignment]:
    num_vars, clauses = parse_dimacs(dimacs)
    solver = Solver(num_vars, clauses)
    return solver.solve()

if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else "../test-formulas/unit4.in"

    with open(path, "r") as f:
        dimacs = f.read()

    solution = solve_dimacs(dimacs)
    if solution is None:
        print("UNSAT")
    else:
        print("SAT")
        print(solution)
