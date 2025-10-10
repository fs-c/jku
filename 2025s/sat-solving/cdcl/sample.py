class Literal:
    """
    Represents a literal in a CNF formula.
    A positive literal is represented by a positive integer,
    and its negation by the negative of that integer.
    """
    def __init__(self, var, negated=False):
        self.var = var
        self.negated = negated
    
    def __repr__(self):
        return f"{'-' if self.negated else ''}{self.var}"
    
    def negate(self):
        """Return the negation of this literal."""
        return Literal(self.var, not self.negated)
    
    def __eq__(self, other):
        if not isinstance(other, Literal):
            return False
        return self.var == other.var and self.negated == other.negated
    
    def __hash__(self):
        return hash((self.var, self.negated))


class ImplicationGraphNode:
    """
    Represents a node in the implication graph of a CDCL solver.
    Each node corresponds to a variable assignment made during the search.
    """
    def __init__(self, literal, decision_level, antecedent=None):
        self.literal = literal
        self.decision_level = decision_level  # Decision level when this assignment was made
        self.antecedent = antecedent  # The clause that led to this assignment, or None if it's a decision
    
    def __repr__(self):
        return f"{self.literal}@{self.decision_level}"


class Trail:
    """
    Represents the assignment trail in a CDCL solver.
    The trail maintains the ordered list of variable assignments.
    """
    def __init__(self):
        self.assignments = []  # List of ImplicationGraphNode objects
        self.variable_to_node = {}  # Maps variable to its node in the trail
    
    def add_assignment(self, literal, decision_level, antecedent=None):
        """Add a new assignment to the trail."""
        node = ImplicationGraphNode(literal, decision_level, antecedent)
        self.assignments.append(node)
        self.variable_to_node[literal.var] = node
        return node
    
    def get_assignment(self, var):
        """Get the assignment information for a variable."""
        return self.variable_to_node.get(var)
    
    def get_current_decision_level(self):
        """Get the current decision level."""
        if not self.assignments:
            return 0
        return self.assignments[-1].decision_level
    
    def get_assignments_at_level(self, level):
        """Get all assignments made at a specific decision level."""
        return [node for node in self.assignments if node.decision_level == level]

    def get_last_assignment_at_level(self, level):
        """Get the last assignment made at a specific decision level."""
        assignments = self.get_assignments_at_level(level)
        return assignments[-1] if assignments else None


def _resolve(*args: Literal) -> set[Literal]:
    """
    resolve a list of clauses, returning a new clause that is the result of resolving all of them
    """
    unique_literals: set[Literal] = set(args)
    resolved: set[Literal] = set()

    for lit in unique_literals:
        if lit.negate() in unique_literals:
            continue

        resolved.add(lit)

    return resolved

def compute_first_uip_conflict_clause(conflict_clause, trail):
    """
    Compute the conflict clause based on the First UIP scheme.
    
    Args:
        conflict_clause: The initial conflict clause (list of Literal objects)
        trail: The current assignment trail (Trail object)
    
    Returns:
        The learned conflict clause (list of Literal objects)
    """
    # Convert conflict clause to a set for easier manipulation
    current_clause = set(conflict_clause)

    # Get current decision level
    current_level = trail.get_current_decision_level()

    # Count variables from current level in the conflict clause
    def count_current_level_vars(clause):
        return sum(1 for lit in clause if trail.get_assignment(lit.var).decision_level == current_level)

    # Initialize a queue with assignments to process in reverse chronological order
    # We only care about assignments at the current decision level
    level_assignments = trail.get_assignments_at_level(current_level)

    # Process assignments in reverse order until we have only one literal from the current level
    # This is the First UIP
    for node in reversed(level_assignments):
        # If we already have only one literal from the current decision level, we found the First UIP
        if count_current_level_vars(current_clause) <= 1:
            break

        current_clause = _resolve(*current_clause, node.literal, *(node.antecedent or set()))

        # # If this literal is in our current clause, resolve it using its antecedent
        # lit = node.literal
        # neg_lit = lit.negate()

        # if neg_lit in current_clause and node.antecedent is not None:
        #     # Remove the literal from the clause
        #     current_clause.remove(neg_lit)

        #     # Add literals from the antecedent clause, except the one being resolved
        #     for antecedent_lit in node.antecedent:
        #         if antecedent_lit != lit:  # Don't add the literal that's being resolved
        #             current_clause.add(antecedent_lit)

    level = 0 if not current_clause else sorted(trail.get_assignment(lit.var).decision_level for lit in current_clause)[-2]
    print(level)
    
    return list(current_clause)


def demonstrate_algorithm():
    """
    Demonstrate the First UIP conflict clause calculation algorithm with an example.
    """
    # Create a trail with some assignments
    trail = Trail()
    
    x1 = Literal(1)
    x2 = Literal(2)
    x3 = Literal(3)
    x4 = Literal(4)
    x5 = Literal(5)
    x6 = Literal(6)
    x7 = Literal(7)
    x8 = Literal(8)

    nx1 = x1.negate()
    nx2 = x2.negate()
    nx3 = x3.negate()
    nx4 = x4.negate()
    nx5 = x5.negate()
    nx6 = x6.negate()
    nx7 = x7.negate()
    nx8 = x8.negate()

    c1 = [nx1, x2, nx4]
    c2 = [nx1, nx2, x3]
    c3 = [nx4, nx3]
    c4 = [x6, x5, nx4]
    c5 = [nx5, x7]
    c6 = [nx8, x7, nx6]

    trail.add_assignment(x1, 1)
    trail.add_assignment(x8, 2)
    trail.add_assignment(nx7, 3)

    trail.add_assignment(nx6, 3, c6)
    trail.add_assignment(nx5, 3, c5)
    trail.add_assignment(x4, 3, c4)
    trail.add_assignment(nx3, 3, c3)
    trail.add_assignment(x2, 3, c1)

    
    conflict_clause = c2
    
    learned_clause = compute_first_uip_conflict_clause(conflict_clause, trail)
    
    # Print results
    print("Trail:")
    for node in trail.assignments:
        antecedent_str = f" (from {node.antecedent})" if node.antecedent else " (decision)"
        print(f"  {node.literal} at level {node.decision_level}{antecedent_str}")
    
    print("\nInitial conflict clause:", conflict_clause)
    print("Learned conflict clause (First UIP):", learned_clause)


if __name__ == "__main__":
    demonstrate_algorithm()