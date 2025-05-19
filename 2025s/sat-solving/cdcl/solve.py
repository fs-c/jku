from typing import List, Set, Dict, Optional, Tuple, NamedTuple
from collections import deque
import sys
from enum import Enum, auto
import networkx as nx
import matplotlib.pyplot as plt

# enable interactive mode for non-blocking plots
plt.ion()

"""
http://minisat.se/downloads/MiniSat.pdf
"""

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
    def __init__(self, literals: List[Literal]):
        self.literals = literals

    def is_satisfied(self, assignment: Assignment) -> bool:
        return any(assignment[lit.var] == lit.value for lit in self.literals)

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Clause) and self.literals == other.literals

    def __hash__(self) -> int:
        return hash(tuple(self.literals))

    def __repr__(self) -> str:
        return f"{' | '.join([str(lit) for lit in self.literals])}"

# todo: it is possible to just generate the implication graph from the trail/control stacks, 
#  but i didn't want to think about that for now
class ImplicationGraph:
    class NodeType(Enum):
        DECISION = auto()
        IMPLIED = auto()
        CONFLICT = auto()

    def __init__(self):
        self.graph = nx.DiGraph()
        self.lit_to_label: Dict[Literal, str] = {}

        self.type_to_color: Dict[ImplicationGraph.NodeType, str] = {
            ImplicationGraph.NodeType.DECISION: '#d4fb78',
            ImplicationGraph.NodeType.IMPLIED: 'white',
            ImplicationGraph.NodeType.CONFLICT: '#ff7d78'
        }

    def _get_participating_lits(self, assignment: 'Assignment', reason: 'Clause') -> List[Literal]:
        # todo: this is demonic, i am 99% sure there is a much easier/faster way to do this
        #  for now it will remain here like since it's just required for drawing the graph and not for the solver logic
        return [lit for lit in [Literal(var, val) for var, val in assignment.items()] if lit.value is not None and lit.var in [lit.var for lit in reason.literals]]

    def add_implied(self, to_lit: 'Literal', assignment: 'Assignment', reason: 'Clause', decision_level: int, is_conflict: bool = False):
        """add an edge to the implication graph representing that from_lit implies to_lit due to reason"""
        self.add_node(to_lit, decision_level, self.NodeType.IMPLIED if not is_conflict else self.NodeType.CONFLICT)

        for from_lit in self._get_participating_lits(assignment, reason):
            from_label = self.lit_to_label.get(from_lit)
            if from_label:
                self.graph.add_edge(from_label, self.lit_to_label[to_lit], reason=str(reason))

    def add_node(self, lit: 'Literal', decision_level: int, type: 'NodeType'):
        """add a node to the implication graph"""
        label = f"{str(lit)}@{decision_level}"
        self.lit_to_label[lit] = label
        self.graph.add_node(label, type=type)

    def add_conflict(self, reason: 'Clause', assignment: 'Assignment', decision_level: int):
        """add a conflict node to the implication graph, determines the participating literals from the assignment"""
        label = f"κ@{decision_level}"
        self.graph.add_node(label, type=self.NodeType.CONFLICT)

        for from_lit in self._get_participating_lits(assignment, reason):
            self.graph.add_edge(self.lit_to_label[from_lit], label, reason=str(reason))

    def show(self, title: str = "Implication Graph"):
        """display the implication graph using matplotlib"""
        plt.figure(figsize=(12, 8))
        pos = nx.spring_layout(self.graph, seed=1337)

        node_color = [self.type_to_color[self.graph.nodes[node]['type']] for node in self.graph.nodes()]
        nx.draw(self.graph, pos, with_labels=True, cmap=plt.cm.viridis, node_size=2000, font_size=10, node_color=node_color, edgecolors='black')

        edge_labels = nx.get_edge_attributes(self.graph, 'reason')
        nx.draw_networkx_edge_labels(self.graph, pos, edge_labels=edge_labels)
        
        plt.title(title)
        plt.draw()
        # this is a hack to give the plot some time to update
        plt.pause(0.001)

class TrailEntry(NamedTuple):
    literal: Literal
    reason: Optional[Clause]

class Solver:
    @staticmethod
    def _find_unassigned_literals(literals: List[Literal], assignment: Assignment) -> List[Literal]:
        return [lit for lit in literals if assignment[lit.var] is None]

    def __init__(self, num_vars: int, clauses: List[Clause]):
        self.num_vars = num_vars
        self.clauses = clauses

        self.implication_graph = ImplicationGraph()

        # write access to this is only allowed through _assign_literal
        self.assignment: Assignment = {i: None for i in range(1, num_vars + 1)}
        # for each variable, remember the decision level at which it was assigned
        # todo: i am sure there is a smarter way to do this that doesn't require another dict
        self.var_to_level: Dict[int, Optional[int]] = {}

        # stack to remember order in which variables were assigned, and the reason (= clause) for the assignment
        # (None if the assignment was due to a decision and not because it was implied during propagation)
        self.trail: List[TrailEntry] = []
        # for each decision level, remember the trail height (invariant: len(control) == current decision level)
        self.control: List[int] = []

        # queue of literals to assign during propagation with the reason for assignment (see trail)
        self.propagation_queue: deque[Tuple[Literal, Clause | None]] = deque()

        # initialize list of literals to consider for assignment
        self.all_literals: Set[Literal] = set() 
        for clause in clauses:
            for lit in clause.literals:
                self.all_literals.add(lit)

        # initialize watch lists
        self.watch_lists: Dict[Literal, Set[Clause]] = {lit: set() for lit in self.all_literals}
        for clause in clauses:
            if len(clause.literals) >= 1:
                self.watch_lists[clause.literals[0]].add(clause)
            if len(clause.literals) >= 2:
                self.watch_lists[clause.literals[1]].add(clause)

    def _decision_level(self) -> int:
        return len(self.control)

    def _assign_and_propagate(self, lit: Literal, reason: Optional[Clause]) -> PropagationResult:
        """attempt to assign a literal and propagate through watch lists"""

        # first, perform the assignment
        self.assignment[lit.var] = lit.value
        self.var_to_level[lit.var] = self._decision_level()
        self.trail.append(TrailEntry(lit, reason))

        # then, handle all clauses watching the variable we just assigned (only need to consider the 
        # clauses that are watching the negation, the others are trivially satisfied)
        # create a copy of the watch list so we can mutate the original while iterating
        watch_list = list(self.watch_lists.get(-lit, []))

        for clause in watch_list:
            # if the clause was already satisfied there's nothing to do
            if clause.is_satisfied(self.assignment):
                continue

            unassigned = Solver._find_unassigned_literals(clause.literals, self.assignment)
            if len(unassigned) == 0:
                # there are no more unassigned literals and the clause is not satisfied (as per previous check) -> conflict
                self.implication_graph.add_conflict(clause, self.assignment, self._decision_level())
                return PropagationResult.CONFLICT
            elif len(unassigned) == 1:
                # there is exactly one unassigned literal left -> unit clause, propagate the literal
                self.propagation_queue.append((unassigned[0], clause))
                self.implication_graph.add_implied(unassigned[0], self.assignment, clause, self._decision_level())
            else:
                # we have more than one unassigned literal left -> update the watch list
                for potential_lit in unassigned:
                    if not clause in self.watch_lists[potential_lit]:
                        self.watch_lists[potential_lit].add(clause)
                        self.watch_lists[-lit].remove(clause)
                        break
                assert clause not in self.watch_lists[-lit], \
                    f"clause {clause} is still watching {lit} but it should have been removed"

        return PropagationResult.NO_CONFLICT

    def _process_propagation_queue(self) -> PropagationResult:
        """process the propagation queue until it's empty or a conflict is found"""

        while self.propagation_queue:
            # get the next literal to assign (unless it's already assigned, in which case we skip)
            lit, reason = self.propagation_queue.popleft()
            if self.assignment[lit.var] == lit.value:
                continue

            # assign the literal and perform unit propagation, this may push to the propagation queue
            if self._assign_and_propagate(lit, reason) == PropagationResult.CONFLICT:
                self.propagation_queue.clear()
                return PropagationResult.CONFLICT

        return PropagationResult.NO_CONFLICT

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

    def _analyze_conflict_trail(self, initial_reason: Clause) -> Tuple[Clause, int]:
        """
        assuming that a conflict has occured on the trail at the current decision level, returns
        - a new clause ("learned clause") to prevent it in the future
        - the decision level to backtrack to

        this is based largely on https://efforeffort.wordpress.com/2009/03/09/linear-time-first-uip-calculation/,
        a detailed explanation of the conflict clause generation of minisat (http://minisat.se/downloads/MiniSat.pdf)
        """

        learned_clause: Clause = Clause([])

        seen: Set[int] = set()
        counter: int = 0

        # don't want to pop from the trail (still need it for backtracking) so we'll just iterate backwards
        # since this will already be called with trail - 1 as the initial reason, we start at -2
        # todo: verify that this is correct and ideally refactor to avoid
        trail_index: int = len(self.trail) - 2

        cur_literal = None
        cur_reason = initial_reason

        while True:
            # process current reason
            for lit in cur_reason.literals:
                if lit.var in seen:
                    continue
                seen.add(lit.var)

                lit_level = self.var_to_level[lit.var]
                if lit_level is None or lit_level < 0:
                    assert False, f"literal {lit} is part of a conflict but does not have a valid decision level ({lit_level})"
                elif lit_level >= self._decision_level():
                    counter += 1
                else:
                    learned_clause.literals.append(lit)

            # select the next literal to follow
            while True:
                cur_literal, cur_reason = self.trail[trail_index]
                if cur_reason is None:
                    cur_reason = Clause([])

                trail_index -= 1

                if cur_literal.var in seen:
                    break

            counter -= 1
            if counter <= 0:
                break

        # cur_literal is now the first uip node (todo: negate)
        if -cur_literal not in learned_clause.literals:
            learned_clause.literals.append(-cur_literal)

        # todo-optimization: can/should we minimize the learned clause some more?

        assert len(learned_clause.literals) > 0, "learned clause is empty, unexpected state"

        # determine the backtrack level (according to https://courses.cs.washington.edu/courses/cse507/17wi/lectures/L02.pdf slide 14
        # it is the second highest level in the conflict clause or 0 if it's a unit clause)
        backtrack_level = sorted(self.var_to_level[lit.var] for lit in learned_clause.literals)[-2] or 0

        return learned_clause, backtrack_level

    def solve(self) -> Optional[Assignment]:
        # handle special cases where formula is trivially satisfiable or unsatisfiable
        # this could be part of a more general simplification/preprocessing step
        if not self.clauses:
            return {}
        if not self.all_literals:
            return None

        while True:
            result = self._process_propagation_queue()
            if result == PropagationResult.CONFLICT:
                if self._decision_level() == 0:
                    return None

                self.implication_graph.show()

                # get the conflict clause from the last assignment
                # todo: the trail reason is None when a conflict happens as an immediate consequence from the first 
                # assignment, the or case is almost certainly wrong
                conflict_clause = self.trail[-1].reason or Clause([self.trail[-1].literal])

                learned_clause, backtrack_level = self._analyze_conflict_trail(conflict_clause)

                # add the learned clause to our clause database
                # todo: maybe factor out the watch list stuff (it's already in the constructor)
                self.clauses.append(learned_clause)
                if len(learned_clause.literals) >= 1:
                    self.watch_lists[learned_clause.literals[0]].add(learned_clause)
                if len(learned_clause.literals) >= 2:
                    self.watch_lists[learned_clause.literals[1]].add(learned_clause)

                last_lit = self._backtrack(backtrack_level)

                if last_lit is not None:
                    self.propagation_queue.append((-last_lit, None))
            elif result == PropagationResult.NO_CONFLICT:
                # select a new decision variable
                unassigned = Solver._find_unassigned_literals(self.all_literals, self.assignment)
                if not unassigned:
                    return {var: val for var, val in self.assignment.items() if val is not None}

                lit = unassigned[0]

                self.control.append(self._decision_level())
                self.propagation_queue.append((lit, None))
                self.implication_graph.add_node(lit, self._decision_level(), ImplicationGraph.NodeType.DECISION)
            else:
                assert False, f"unknown propagation result: {result}"

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
            for lit in line.split()[:-1]: # skip the trailing 0
                lit = int(lit)
                literals.append(Literal(abs(lit), lit > 0))
            clauses.append(Clause(literals))

    return num_vars, clauses

def solve_dimacs(dimacs: str) -> Optional[Assignment]:
    num_vars, clauses = parse_dimacs(dimacs)
    solver = Solver(num_vars, clauses)
    return solver.solve()

if __name__ == "__main__":
    path = sys.argv[1] if len(sys.argv) > 1 else "../test-formulas/unit5.in"

    with open(path, "r") as f:
        dimacs = f.read()

    solution = solve_dimacs(dimacs)
    if solution is None:
        print("UNSAT")
    else:
        print("SAT")
        print(solution)
