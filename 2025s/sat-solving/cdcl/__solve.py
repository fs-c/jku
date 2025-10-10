class CDCLSolver:
    def __init__(self, formula):
        self.formula = formula  # List of clauses, each clause is list of literals
        self.num_vars = self._get_num_vars()
        
        # Assignment state
        self.assignment = {}  # var -> bool
        self.decision_level = {}  # var -> int
        self.antecedent = {}  # var -> clause
        self.assignment_stack = []  # (var, value, level, antecedent)
        self.current_decision_level = 0
        
        # Watched literals
        self.watch_lists = {}  # literal -> [clauses]
        self.watched = {}  # clause -> (lit1, lit2)
        
        # Unit propagation queue
        self.unit_queue = []
        
        self._initialize_watched_literals()
    
    def _get_num_vars(self):
        max_var = 0
        for clause in self.formula:
            for lit in clause:
                max_var = max(max_var, abs(lit))
        return max_var
    
    def solve(self):
        while True:
            # Unit propagation
            conflict = self._unit_propagate()
            
            if conflict is not None:
                if self.current_decision_level == 0:
                    return False  # UNSAT
                
                # Conflict analysis and learning
                learned_clause, backtrack_level = self._analyze_conflict(conflict)
                self.formula.append(learned_clause)
                self._initialize_watches_for_clause(learned_clause)
                
                # Backtrack
                self._backtrack(backtrack_level)
            else:
                if self._all_variables_assigned():
                    return True  # SAT
                
                # Make decision
                var = self._choose_variable()
                value = self._choose_value(var)
                self.current_decision_level += 1
                self._assign(var, value, self.current_decision_level, None)
    
    def _initialize_watched_literals(self):
        # Initialize watch lists
        for i in range(1, self.num_vars + 1):
            self.watch_lists[i] = []
            self.watch_lists[-i] = []
        
        # Set up watches for each clause
        for clause in self.formula:
            self._initialize_watches_for_clause(clause)
    
    def _initialize_watches_for_clause(self, clause):
        if len(clause) == 0:
            return  # Empty clause
        
        if len(clause) == 1:
            # Unit clause - watch the single literal
            lit = clause[0]
            self.watch_lists[lit].append(clause)
            self.watched[id(clause)] = (lit, None)
            return
        
        # Watch first two literals
        lit1, lit2 = clause[0], clause[1]
        self.watch_lists[lit1].append(clause)
        self.watch_lists[lit2].append(clause)
        self.watched[id(clause)] = (lit1, lit2)
    
    def _unit_propagate(self):
        # Get initial unit literals
        self.unit_queue = self._get_unit_literals()
        
        while self.unit_queue:
            unit_lit = self.unit_queue.pop(0)
            
            if self._is_assigned(abs(unit_lit)):
                if self._get_assignment(unit_lit) == False:
                    return self._find_conflicting_clause(unit_lit)
                continue
            
            # Make assignment
            var = abs(unit_lit)
            value = unit_lit > 0
            antecedent = self._find_unit_antecedent(unit_lit)
            self._assign(var, value, self.current_decision_level, antecedent)
            
            # Process clauses watching the negation
            conflict = self._process_watched_clauses(-unit_lit)
            if conflict is not None:
                return conflict
        
        return None
    
    def _process_watched_clauses(self, falsified_lit):
        watch_list = self.watch_lists[falsified_lit][:]
        self.watch_lists[falsified_lit] = []
        
        for clause in watch_list:
            watched_lits = self.watched[id(clause)]
            
            if len(clause) == 1:
                # Unit clause
                if self._is_falsified(clause):
                    return clause
                self.watch_lists[falsified_lit].append(clause)
                continue
            
            lit1, lit2 = watched_lits
            
            # Determine other watched literal
            if lit1 == falsified_lit:
                other_watched = lit2
            else:
                other_watched = lit1
            
            # If other watched literal is satisfied, keep watching
            if self._is_satisfied(other_watched):
                self.watch_lists[falsified_lit].append(clause)
                continue
            
            # Try to find new literal to watch
            new_watch = self._find_new_watch(clause, lit1, lit2)
            
            if new_watch is not None:
                # Update watch
                if lit1 == falsified_lit:
                    self.watched[id(clause)] = (new_watch, lit2)
                else:
                    self.watched[id(clause)] = (lit1, new_watch)
                
                # Add to new literal's watch list
                self.watch_lists[new_watch].append(clause)
            else:
                # No new watch found - check clause status
                if self._is_falsified_literal(other_watched):
                    return clause  # Conflict
                elif not self._is_assigned(abs(other_watched)):
                    # Unit clause
                    self.unit_queue.append(other_watched)
                    self.watch_lists[falsified_lit].append(clause)
                else:
                    self.watch_lists[falsified_lit].append(clause)
        
        return None
    
    def _find_new_watch(self, clause, current_watch1, current_watch2):
        for lit in clause:
            if lit != current_watch1 and lit != current_watch2:
                if self._is_satisfied(lit) or not self._is_assigned(abs(lit)):
                    return lit
        return None
    
    def _analyze_conflict(self, conflict_clause):
        learned_clause = []
        seen = set()
        counter = 0
        current_clause = conflict_clause
        backtrack_level = 0
        
        while True:
            # Add literals from current clause to learned clause
            for lit in current_clause:
                var = abs(lit)
                
                if var not in seen:
                    seen.add(var)
                    level = self.decision_level.get(var, 0)
                    
                    if level == self.current_decision_level:
                        counter += 1
                    elif level > 0:
                        learned_clause.append(-lit)
                        backtrack_level = max(backtrack_level, level)
            
            # Find next literal to resolve on
            while True:
                var, value, level, antecedent = self.assignment_stack[-1]
                self.assignment_stack.pop()
                if var in seen:
                    lit = var if value else -var
                    break
            
            counter -= 1
            if counter == 0:
                break
            
            current_clause = self.antecedent[var]
        
        # Add the UIP literal
        learned_clause.append(-lit)
        
        if len(learned_clause) == 1:
            backtrack_level = 0
        else:
            # Find second highest decision level
            levels = [self.decision_level.get(abs(lit), 0) for lit in learned_clause]
            levels.sort(reverse=True)
            backtrack_level = levels[1] if len(levels) > 1 else 0
        
        return learned_clause, backtrack_level
    
    def _choose_variable(self):
        # Simple heuristic - first unassigned variable
        for i in range(1, self.num_vars + 1):
            if not self._is_assigned(i):
                return i
        return None
    
    def _choose_value(self, var):
        # Always choose positive
        return True
    
    def _assign(self, var, value, level, antecedent):
        self.assignment[var] = value
        self.decision_level[var] = level
        self.antecedent[var] = antecedent
        self.assignment_stack.append((var, value, level, antecedent))
    
    def _backtrack(self, target_level):
        while (self.assignment_stack and 
               self.assignment_stack[-1][2] > target_level):
            var, value, level, antecedent = self.assignment_stack.pop()
            self._unassign(var)
        
        self.current_decision_level = target_level
    
    def _unassign(self, var):
        if var in self.assignment:
            del self.assignment[var]
        if var in self.decision_level:
            del self.decision_level[var]
        if var in self.antecedent:
            del self.antecedent[var]
    
    def _get_unit_literals(self):
        unit_lits = []
        for clause in self.formula:
            if self._is_unit_clause(clause):
                unit_lit = self._get_unit_literal(clause)
                if unit_lit is not None:
                    unit_lits.append(unit_lit)
        return unit_lits
    
    def _is_unit_clause(self, clause):
        unassigned_count = 0
        satisfied = False
        
        for lit in clause:
            if self._is_satisfied(lit):
                satisfied = True
                break
            if not self._is_assigned(abs(lit)):
                unassigned_count += 1
        
        return not satisfied and unassigned_count == 1
    
    def _is_falsified(self, clause):
        for lit in clause:
            if self._is_satisfied(lit):
                return False
            if not self._is_assigned(abs(lit)):
                return False
        return True
    
    def _is_satisfied(self, lit):
        var = abs(lit)
        if not self._is_assigned(var):
            return False
        
        if lit > 0:
            return self.assignment[var] == True
        else:
            return self.assignment[var] == False
    
    def _is_falsified_literal(self, lit):
        return self._is_assigned(abs(lit)) and not self._is_satisfied(lit)
    
    def _get_unit_literal(self, clause):
        for lit in clause:
            if not self._is_assigned(abs(lit)):
                return lit
        return None
    
    def _all_variables_assigned(self):
        return len(self.assignment) == self.num_vars
    
    def _is_assigned(self, var):
        return var in self.assignment
    
    def _get_assignment(self, lit):
        var = abs(lit)
        if not self._is_assigned(var):
            return None
        
        if lit > 0:
            return self.assignment[var]
        else:
            return not self.assignment[var]
    
    def _find_unit_antecedent(self, unit_lit):
        # Find clause that makes this literal unit
        for clause in self.formula:
            if (self._is_unit_clause(clause) and 
                self._get_unit_literal(clause) == unit_lit):
                return clause
        return None
    
    def _find_conflicting_clause(self, lit):
        # Find clause that conflicts with this assignment
        for clause in self.watch_lists[lit]:
            if self._is_falsified(clause):
                return clause
        return None
    
    def get_model(self):
        """Return satisfying assignment if SAT"""
        if len(self.assignment) == self.num_vars:
            return {var: val for var, val in self.assignment.items()}
        return None

def parse_dimacs(dimacs_content):
    """Parse DIMACS CNF format and return formula and number of variables."""
    lines = dimacs_content.strip().split('\n')
    formula = []
    num_vars = 0
    
    for line in lines:
        line = line.strip()
        if not line or line.startswith('c'):
            continue
        if line.startswith('p'):
            # Parse problem line
            parts = line.split()
            if len(parts) != 4 or parts[1] != 'cnf':
                raise ValueError("Invalid problem line in DIMACS file")
            num_vars = int(parts[2])
            continue
        
        # Parse clause line
        clause = []
        for lit in line.split():
            lit = int(lit)
            if lit == 0:
                break
            clause.append(lit)
        if clause:  # Only add non-empty clauses
            formula.append(clause)
    
    return formula, num_vars

def test_solver():
    dimacs_file = "../test-formulas/sat5.in"
    
    try:
        with open(dimacs_file, 'r') as f:
            dimacs_content = f.read()
        
        formula, num_vars = parse_dimacs(dimacs_content)
        print(formula)

        solver = CDCLSolver(formula)
        
        if solver.solve():
            print("SAT")
            model = solver.get_model()
            if model:
                print("Satisfying assignment:")
                for var, val in sorted(model.items()):
                    print(f"x{var} = {val}")
        else:
            print("UNSAT")
            
    except FileNotFoundError:
        print(f"Error: Could not find file {dimacs_file}")
    except Exception as e:
        print(f"Error: {str(e)}")

if __name__ == "__main__":
    test_solver()