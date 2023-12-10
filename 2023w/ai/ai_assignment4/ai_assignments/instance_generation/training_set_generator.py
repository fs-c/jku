from sklearn.datasets import make_classification
from ai_assignments.instance_generation.training_set import TrainingSet
import numpy as np


def get_problem(rng, size, toy=True):
    n_features = 10
    n_informative = 8

    if toy:
        n_features = 2
        n_informative = 2

    n_redundant = n_features - n_informative

    X, y = make_classification(n_samples=size,
                               n_classes=2,
                               n_features=n_features,
                               n_informative=n_informative,
                               n_redundant=n_redundant,
                               n_clusters_per_class=2)
    # if digitize:
    #     X = np.digitize(X, [-0.75, 0])
    #     X = np.array([["abcdefgh"[i] for i in row] for row in X], dtype=str)
    return TrainingSet(X,  y)


def get_minimum_problem_size():
    return 0