from .. problem import Problem
import random


# please ignore this
def get_solver_mapping():
    return dict(rs=RS)


class RS(object):
    def solve(self, problem: Problem):
        # this is important, please leave it as is
        random.seed(1234)

        # we ask the problem to tell as where to start the search
        current = problem.get_start_node()

        # TODO, exercise 0: uncomment these lines to solve the problem!

        while not problem.is_end(current):       # as long as the current node is not the end
            nodes = problem.successors(current)  # get the successor nodes for the current node
            current = random.choice(nodes)       # choose a random successor node

        # the loop above only terminates, when current is the end node (== the solution)
        return current
