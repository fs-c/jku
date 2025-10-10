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
    # todo: unused?
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

        # for each variable, remember the reason for assignment (None if the assignment was due to a decision)
        # todo: this is duplicate information to the trail but it was more convenient like this, should be refactored
        self.var_to_reason: Dict[int, Optional[Clause]] = {}

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
    
    def _log(self, message: str):
        # print(f"[{self._decision_level()}] ", end=" ")
        # print(message)
        pass

    def _find_unassigned_literals(self, literals: Set[Literal]) -> List[Literal]:
        return [lit for lit in literals if self.assignment[lit.var] is None]
    
    def _find_new_watch(self, clause: Clause, old_watch: Literal) -> Optional[Literal]:
        for lit in clause.literals:
            if lit == old_watch:
                continue

            if self.assignment[lit.var] is not None or self.assignment[lit.var] == lit.value:
                return lit

        return None        

    def _assign_and_propagate(self, lit: Literal, reason: Optional[Clause]) -> Tuple[PropagationResult, Optional[Clause]]:
        """attempt to assign a literal and propagate through watch lists"""

        self._log(f"assigning {lit} with reason {reason} and propagating")

        # perform the assignment
        self.assignment[lit.var] = lit.value
        self.var_to_level[lit.var] = self._decision_level()
        self.var_to_reason[lit.var] = reason
        self.trail.append(TrailEntry(lit, reason))

        # then, handle all clauses potentially affected by this assignment (not really all potentially affected clauses, 
        # but all where we would care about the effect -> i.e. where it could make the clause unsatisfied)
        # only need to consider the clauses that are watching the negation of the literal, the others are trivially satisfied
        # create a copy of the watch list so we can mutate the original while iterating
        watch_list = self.watch_lists.get(-lit, []).copy()
        for clause in watch_list:
            if clause.is_satisfied(self.assignment):
                continue

            # find a new literal to watch
            new_watch = self._find_new_watch(clause, lit)

            if new_watch is not None:
                self.watch_lists[-lit].remove(clause)
                self.watch_lists[new_watch].append(clause)
            else:
                # if we couldn't get a new watch the clause might be unit or conflicting
                unassigned = self._find_unassigned_literals(clause.literals)
                if len(unassigned) == 1:
                    self.propagation_queue.append((unassigned[0], clause))
                else:
                    return PropagationResult.CONFLICT, clause

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
                self.var_to_reason[last_lit.var] = None

        return last_lit

    def _has_one_literal_set_at_current_level(self, clause: Clause) -> Tuple[bool, Optional[Literal]]:
        """
        (1) checks if the clause has exactly one literal set at the given level
        (2) returns the most recently assigned literal (irrespective of (1))
        """

        # todo: this is retarded, should be able to just use the trail

        most_recent_lit = None
        lits_at_current_level = []

        for i in range(len(self.trail) - 1, self.control[-1] - 1, -1):
            entry = self.trail[i]
            if not (entry.literal in clause.literals or -entry.literal in clause.literals):
                continue

            if most_recent_lit is None:
                most_recent_lit = entry.literal

            if self.var_to_level[entry.literal.var] == self._decision_level():
                lits_at_current_level.append(entry.literal)

        return len(lits_at_current_level) == 1, most_recent_lit
            

    def _resolve_clauses(self, clause1: Clause, clause2: Clause, lit: Literal) -> Clause:
        """
        todo: this is idiotic, refactor
        """

        merged = clause1.literals | clause2.literals
        if lit in merged:
            merged.remove(lit)
        if -lit in merged:
            merged.remove(-lit)

        return Clause(merged)

    def _get_backtrack_level(self, conflict_clause: Clause, conflict_level: int) -> int:
        """
        returns the backtrack level for the given conflict clause
        """
        maximum_level_before_conflict_level = -1

        for lit in conflict_clause.literals:
            level = self.var_to_level[lit.var]
            if level is not None and level < conflict_level:
                maximum_level_before_conflict_level = max(maximum_level_before_conflict_level, level)

        return maximum_level_before_conflict_level

    def _analyze_conflict_trail(self, conflict: Clause) -> Tuple[Tuple[Optional[Literal], Optional[Clause]], int]:
        """
        assuming that we just found the given conflict clause, this function will return a literal (and reason) to set 
        and a backtrack level based on the current trail
        """

        conflict_clause = Clause(set(conflict.literals))

        # todo: we need to exit early at decision level 0 or the loop will probably not work but this is not very elegant
        if self._decision_level() == 0:
            return (None, None), -1

        while True:
            # check if the current clause has exactly one literal set at the current decision level
            has_one_lit, latest_lit = self._has_one_literal_set_at_current_level(conflict_clause)

            # if there is exactly one literal set at the current decision level, we have found the first UIP
            # todo: really? why?
            if has_one_lit:
                break

            assert latest_lit is not None, "no literal set at the current decision level, unexpected state"

            latest_lit_reason = self.var_to_reason[latest_lit.var] or Clause(set())

            self._log(f"resolving {conflict_clause} and {latest_lit_reason} with {latest_lit}")
            conflict_clause = self._resolve_clauses(conflict_clause, latest_lit_reason, latest_lit)

        self._log(f"found conflict clause: {conflict_clause}")

        conflict_literals = list(conflict_clause.literals)
        assert len(conflict_literals) >= 1, "conflict clause has no literals, unexpected state"

        if len(conflict_literals) == 1:
            return (conflict_literals[0], None), 0
        else:
            # add the learned clause to our clause database
            # todo: factor out the watch list stuff (it's already in the constructor)
            self.clauses.append(conflict_clause)

            if len(conflict_literals) >= 1:
                self.watch_lists[conflict_literals[0]].append(conflict_clause)
            if len(conflict_literals) >= 2:
                self.watch_lists[conflict_literals[1]].append(conflict_clause)

            # todo/hacky: the latest_lit must match the sign of the lit as it appears in the conflict clause,
            # but this may not be the case
            if latest_lit is not None and not latest_lit in conflict_clause.literals:
                latest_lit = -latest_lit

            return (latest_lit, conflict_clause), self._get_backtrack_level(conflict_clause, self._decision_level())

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

                (implication, implication_reason), backtrack_level = self._analyze_conflict_trail(conflict_clause)
                self._log(f"analyze conflict trail: implication: {implication} (reason: {implication_reason}), backtrack level: {backtrack_level}")
                if not implication or backtrack_level == -1:
                    return None

                _ = self._backtrack(backtrack_level)

                self._log(f"deciding on {implication} after conflict")

                self.propagation_queue.append((implication, implication_reason))
            elif result == PropagationResult.NO_CONFLICT:
                # select a new decision variable
                unassigned = self._find_unassigned_literals(self.all_literals)
                if not unassigned:
                    return {var: val for var, val in self.assignment.items() if val is not None}

                # todo: for now we just pick the first unassigned literal, this could be much faster with something like VSIDS
                lit = unassigned[0]

                self._log(f"deciding on {lit}")

                self.control.append(len(self.trail))
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
    path = sys.argv[1] if len(sys.argv) > 1 else "../test-formulas/add8.in"

    with open(path, "r") as f:
        dimacs = f.read()

    solution = solve_dimacs(dimacs)
    if solution is None:
        print("UNSAT")
    else:
        print("SAT")
        print(solution)
