import networkx as nx
import matplotlib.pyplot as plt

ASSIGNMENT = [
    -9,
    -10,
    -11,
    12,
    13,
    1
]

CLAUSES = [
    [-1, 2],
    [-1, 3, 9],
    [-2, -3, 4],
    [-4, 5, 10],
    [-4, 6, 11],
    [-5, -6],
    [1, 7, -12],
    [1, 8],
    [-7, -8, -13],
]

def build_implication_graph(clauses, assignment):
    graph = nx.DiGraph()

    # see https://www.cs.princeton.edu/courses/archive/fall13/cos402/readings/SAT_learning_clauses.pdf

    # 1. add a node for each variable of the assignment
    for variable in assignment:
        graph.add_node(variable)

    # 2. while there exists a clause C = ( li, ... , lk, l ) such that !li, ... , !lk are in the graph
    #    (and l is not):
    # (this is incredibly stupid and not according to the algorithm in the document, the given algorithm
    # would just loop forever and i couldn't think of a nice way to find a stopping condition so we just 
    # do it a bunch of times and assume that it converges)
    for i in range(len(clauses)):
        for clause in clauses:
            # get the literals where the negation is not in the graph
            missing_literals = []
            for literal in clause:
                if not graph.has_node(-literal):
                    missing_literals.append(literal)
            # if there is exactly one literal where the negation is not in the graph, we found our clause
            # (the current graph state forces this literal to be true)
            if len(missing_literals) == 1:
                l = missing_literals[0]
                print("debug: found clause", clause, "with exactly one missing literal", l)
                graph.add_node(l)
                for literal in clause:
                    if literal != l:
                        if not graph.has_node(-literal):
                            print("unmet invariant: !li is not in the graph")
                            exit(1)
                        print("debug: adding edge from", -literal, "to", l)
                        graph.add_edge(-literal, l)

    return graph

def draw_graph(graph):
    pos = nx.arf_layout(graph)
    nx.draw(graph, pos, with_labels=True, edge_color='black', node_size=2000, font_size=12)
    plt.show()

if __name__ == "__main__":
    graph = build_implication_graph(CLAUSES, ASSIGNMENT)
    draw_graph(graph)
