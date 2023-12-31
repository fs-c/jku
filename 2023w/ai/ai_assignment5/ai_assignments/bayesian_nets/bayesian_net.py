import matplotlib
import numpy as np
import networkx as nx
import matplotlib.pyplot as plt

from math import prod

matplotlib.use('TkAgg')


def extend_dict(e, var, val):
    """ Creates new dict with everything contained in e, plus var:val items. """
    return {**e, var: val}


class BayesianNode:
    """ Building stone for BayesianNet class. Represents conditional probability distribution
        for a boolean random variable, P(X | parents). """
    def __init__(self, X: str, parents: str, cpt: dict = None):
        """
        X: String describing variable name

        parents: String containing parent variable names, separated with a whitespace

        cpt: dict that contains the distribution P(X=true | parent1=v1, parent2=v2...).
             Dict should be structured as follows: {(v1, v2, ...): p, ...}, and each key must have
             as many values as there are parents. Values (v1, v2, ...) must be True/False.
        """
        if not isinstance(X, str) or not isinstance(parents, str):
            raise ValueError("Use valid arguments - X and parents have to be strings (but at least one is not)!")
        self.rand_var = X
        self.parents = parents.split()
        self.children = []

        # in case of 0 or 1 parent, fix tuples first
        if cpt and isinstance(cpt, (float, int)):
            cpt = {(): cpt}
        elif cpt and isinstance(cpt, dict):
            if isinstance(list(cpt.keys())[0], bool):
                # only one parent
                cpt = {(k, ): v for k, v in cpt.items()}
        elif cpt:
            raise ValueError("Define cpt with a valid data type (dict, or int).")
        # check format of cpt dict
        if cpt:
            for val, p in cpt.items():
                assert isinstance(val, tuple) and len(val) == len(self.parents)
                assert all(isinstance(v, bool) for v in val)
                assert 0 <= p <= 1

        self.cpt = cpt

    def __repr__(self):
        """ String representation of Bayesian Node. """
        return repr((self.rand_var, ' '.join(["parent(s):"] + self.parents)))

    def cond_probability(self, value: bool, event: dict):
        """
            Returns conditional probability P(X=value | event) for an atomic event,
            i.e. where each parent needs to be assigned a value.
            value: bool (value of this random variable)
            event: dict, assigning a value to each parent variable
        """
        assert isinstance(value, bool)
        if self.cpt:
            prob_true = self.cpt[self.get_event_values(event)]
            return prob_true if value else 1 - prob_true

        return None

    def get_event_values(self, event: dict):
        """ Given an event (dict), returns tuple of values for all parents. """
        return tuple(event[p] for p in self.parents)


class BayesianNet:
    """ Bayesian Network class for boolean random variables. Consists of BayesianNode-s.  """
    def __init__(self, node_specs: list):
        """
            Creates BayesianNet with given node_specs. Nodes should be in causal order (parents before children).
            node_specs should be list of parameters for BayesianNode class.
        """
        self.nodes = []
        self.rand_vars = []
        for spec in node_specs:
            self.add_node(spec)

    def add_node(self, node_spec):
        """ Creates a BayesianNode and adds it to the net, if the variable does *not*, and the parents do exist. """
        node = BayesianNode(*node_spec)
        if node.rand_var in self.rand_vars:
            raise ValueError("Variable {} already exists in network, cannot be defined twice!".format(node.rand_var))
        if not all((parent in self.rand_vars) for parent in node.parents):
            raise ValueError("Parents do not all exist yet! Make sure to first add all parent nodes.")
        self.nodes.append(node)
        self.rand_vars.append(node.rand_var)
        for parent in node.parents:
            self.get_node_for_name(parent).children.append(node)

    def get_node_for_name(self, node_name):
        """ Given the name of a random variable, returns the according BayesianNode of this network. """
        for n in self.nodes:
            if n.rand_var == node_name:
                return n

        raise ValueError("The variable {} does not exist in this network!".format(node_name))

    def __repr__(self):
        """ String representation of this Bayesian Network. """
        return "BayesianNet:\n{0!r}".format(self.nodes)

    def _chain_atomic(self, atomic_event: dict):
        """
            Given a particular atomic event, applies chain rule of BN to determine
            of P(event). Must assign a value to each random variable of the BN.
            atomic_event: dict, where keys are names of random variables, which are associated with their values.
        """
        return prod([node.cond_probability(atomic_event[node.rand_var], atomic_event) for node in self.nodes])

    def event_probability(self, event):
        """
            Recursive function to compute probability of any (non-atomic) event. Must not assign value to each
            random variable in the world of the BN.

            event: dict, where entries are: {random variable: value}
            Returns: probability of `event` in this BN.
        """
        # get all missing variables
        Y = [rand_var for rand_var in self.rand_vars if rand_var not in event.keys()]

        if len(Y) == 0:
            # atomic event
            return self._chain_atomic(event)
        cur_Y = Y[0]
        return sum([self.event_probability(extend_dict(event, cur_Y, y_vals)) for y_vals in [True, False]])

    def _get_depth(self, rand_var):
        """ Given random variable, returns "depth" of node in graph for plotting. """
        node = self.get_node_for_name(rand_var)
        if len(node.parents) == 0:
            return 0

        return max([self._get_depth(p) for p in node.parents]) + 1

    def draw(self, title, save_path=None):
        """ Draws the BN with networkx. Requires title for plot. """
        plt.figure(figsize=(14, 8))
        nx_bn = nx.DiGraph()
        nx_bn.add_nodes_from(self.rand_vars)
        pos = {rand_var: (10, 10) for rand_var in self.rand_vars}
        for rand_var in self.rand_vars:
            node = self.get_node_for_name(rand_var)
            for c in node.children:
                nx_bn.add_edge(rand_var, c.rand_var)
                pos.update({c.rand_var: (pos[c.rand_var][0], pos[c.rand_var][1] - 3)})

        depths = {rand_var: self._get_depth(rand_var) for rand_var in self.rand_vars}
        _, counts = np.unique(list(depths.values()), return_counts=True)
        xs = [list(np.linspace(6, 14, c)) if c > 1 else [10] for c in counts]
        pos = {rand_var: (xs[depths[rand_var]].pop(), 10 - depths[rand_var] * 3) for rand_var in self.rand_vars}

        nx.set_node_attributes(nx_bn, pos, 'pos')
        nx.draw_networkx(nx_bn, arrows=True, pos=nx.get_node_attributes(nx_bn, "pos"),
                         node_shape="o", node_color="white", node_size=7000, edgecolors="gray")
        plt.title(title)
        plt.box(False)
        plt.margins(0.3)
        plt.tight_layout()
        if save_path:
            plt.savefig(save_path, dpi=400)
        else:
            plt.show()


if __name__ == '__main__':
    T = True
    F = False
    bn = BayesianNet([
        ('Burglary', '', 0.001),
        ('Earthquake', '', {(): 0.002}),
        ('Alarm', 'Burglary Earthquake',
         {(T, T): 0.95, (T, F): 0.94, (F, T): 0.29, (F, F): 0.001}),
        ('JohnCalls', 'Alarm', {T: 0.90, F: 0.05}),
        ('MaryCalls', 'Alarm', {T: 0.70, F: 0.01})
    ])
    bn.draw("")
