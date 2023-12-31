from bayesian_net import BayesianNet

bn = BayesianNet([
    # TODO: construct the Bayesian network based on story on Moodle (A5 "Constructing a Bayesian Net": The Story)
    # TODO: you don't need to initialize the conditional probability tables
    ["Mane", ""],
    ["Sleep", ""],
    ["Speed", "Sleep"],
    ["Competitors", ""],
    ["Rewards", ""],
    ["Racing", "Speed Competitors Rewards"]
])


# TODO: visualize the result
# TODO: include your first name and matriculation number in the title
bn.draw("Laurenz Weixlbaumer, k11804751", "construct_a_net.png")
