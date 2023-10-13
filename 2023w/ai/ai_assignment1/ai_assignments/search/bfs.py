from .. problem import Problem
from .. datastructures.queue import Queue


# please ignore this
def get_solver_mapping():
    return dict(bfs=BFS)


class BFS(object):
    # TODO, exercise 1:
    # - implement Breadth First Search (BFS)
    # - use 'problem.get_start_node()' to get the node with the start state
    # - use 'problem.is_end(node)' to check whether 'node' is the node with the end state
    # - use a set() to store already visited nodes
    # - use the 'queue' datastructure that is already imported as the 'fringe'/ the 'frontier'
    # - use 'problem.successors(node)' to get a list of nodes containing successor states
    def solve(self, problem: Problem):
        visited = set()
        fringe = Queue()

        initial = problem.get_start_node()
        visited.add(initial)
        fringe.put(initial)

        while fringe.has_elements():
            current = fringe.get()

            if problem.is_end(current):
                return current

            for node in problem.successors(current):
                if node not in visited:
                    fringe.put(node)
                    visited.add(node)

        return None
