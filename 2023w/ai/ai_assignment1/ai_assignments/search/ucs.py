from .. problem import Problem
from .. datastructures.priority_queue import PriorityQueue


def get_solver_mapping():
    return dict(ucs=UCS)


class UCS(object):
    # TODO, excercise 2:
    # - implement Uniform Cost Search (UCS), a variant of Dijkstra's Graph Search
    # - use the provided PriorityQueue where appropriate
    # - to put items into the PriorityQueue, use 'pq.put(<priority>, <item>)'
    # - to get items out of the PriorityQueue, use 'pq.get()'
    # - store visited nodes in a 'set()'
    def solve(self, problem: Problem):
        visited = set()
        pq = PriorityQueue()

        initial = problem.get_start_node()
        visited.add(initial)
        pq.put(initial.cost, initial)

        while pq.has_elements():
            current = pq.get()

            if problem.is_end(current):
                return current

            for node in problem.successors(current):
                if node not in visited:
                    pq.put(node.cost, node)
                    visited.add(node)

        return None
