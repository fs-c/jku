from .. import register_decision_tree_learning_method
from . id3 import ID3

register_decision_tree_learning_method('id3', ID3)
