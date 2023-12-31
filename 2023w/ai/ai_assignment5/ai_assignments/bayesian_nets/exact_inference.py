from bayesian_net import BayesianNet

T, F = True, False


def build_network():
    # TODO: build network that is provided for you on Moodle: A5 Exact Inference, include probability distributions
    bn = BayesianNet([
        ["VA", "", 0.09],
        ["RE", "VA", {(True): 0.85, (False): 0.6}],

        ["MP", "", 0.1],
        ["DA", "MP", {(True): 0.3, (False): 0.05}],
        ["SI", "MP", {(True): 0.2, (False): 0.03}],

        ["HA", "RE SI", {(True, True): 0.7, (True, False): 0.65, (False, True): 0.1, (False, False): 0.01}]
    ])

    return bn


if __name__ == '__main__':
    bn = build_network()

    # optional: visualize network to check whether the structure is correct
    bn.draw("Laurenz Weixlbaumer, k11804751", "exact_inference.png")

    # TODO: compute the answers to the probabilistic queries (provided on Moodle A5 Exact Inference)
    # TODO: print results
    # TODO: enter required numbers in Moodle
    # Hint: use bn.event_probability(event)

    print(1 / bn.event_probability({"MP": False, "HA": True, "VA": True, "RE": True}))
    print(bn.event_probability({"MP": False, "SI": True, "HA": True, "VA": True, "RE": True}))
    print(bn.event_probability({"MP": False, "SI": False, "HA": True, "VA": True, "RE": True}))
    print(bn.get_node_for_name("SI").cond_probability(True, {"MP": False, "HA": True, "VA": True, "RE": True}))
    print(bn.get_node_for_name("SI").cond_probability(False, {"MP": False, "HA": True, "VA": True, "RE": True}))    
