import ai_assignments
import argparse
import textwrap
import hashlib
import time
import copy
import os
import json
import pickle

def main():
    parser = argparse.ArgumentParser(
        description=textwrap.dedent('''
        this script reads in a training set in JSON format, and learns
        a decision tree. the learned decision tree is written into a file
        in the same directory as the training set.
        '''),
        epilog=textwrap.dedent('''
        example usage:

        $ python learn.py test/trainset.json id3
        this loads the training set stored in 'test/trainset.json' and learns
        a decision tree using the 'id3' algorithm. the decision tree
        is written to the file 'test/id3.tree'.
        '''),
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument(
        'training_set_name',
        type=str,
        help='the name of the file that stores the training set'
    )
    parser.add_argument(
        'decision_tree_learning_methods',
        nargs='+',
        choices=ai_assignments.get_decision_tree_learning_methods(),
        help='''choose one or more methods
        to learn a decision tree.

        the decision tree will be written into a file in the same directory
        as the training_set with the name <method_name>.tree.

        solution hashes will be written to a text file in the same directory
        as the training_set with the name <method_name>.hash'''
    )
    args = parser.parse_args()

    # TODO comment in again
    if not os.path.exists(args.training_set_name):
        print('the training set ({}) does not exist'.format(args.training_set_name))
        exit()

    training_set = ai_assignments.load_problem_instance(args.training_set_name)
    # TODO: move this to other class?
    # with open(args.training_set_name, 'r') as fh:
    #     training_set = json.loads(fh.read())
    training_set_directory, _ = os.path.split(args.training_set_name)

    for dt_method_name in args.decision_tree_learning_methods:
        # the training set is copied, so that each of the training
        # methods gets a fresh copy to train on, and all counts are reset
        current_training_set = copy.deepcopy(training_set)
        tree = ai_assignments.get_decision_tree_learning_method(dt_method_name)()

        t_start = time.time()
        tree.fit(current_training_set.X, current_training_set.y) # todo: return not necessary
        t_end = time.time()
        t_diff = t_end - t_start

        outcome_filename = os.path.join(
            training_set_directory,
            '{}.tree'.format(dt_method_name)
        )
        tree_str = str(tree)
        with open(outcome_filename, 'w') as fh:
            fh.write(tree_str)

        tree_hash_as_str = hashlib.sha256(tree_str.encode('UTF-8')).hexdigest()
        tree_hash_filename = os.path.join(
            training_set_directory,
            '{}.hash'.format(dt_method_name)
        )
        with open(tree_hash_filename, 'w') as fh:
            fh.write(tree_hash_as_str)

        tree_pickle_name = os.path.join(
            training_set_directory,
            '{}.pt'.format(dt_method_name)
        )

        with open(tree_pickle_name, 'wb') as fh:
            pickle.dump(tree, fh)

        # output some info, for convenience
        print(f'### decision tree learning method: {dt_method_name:>8s} #####################')
        print(f'training took           {t_diff:4.2f} seconds')
        print("this is what the tree looks like:")
        tree.print_decision_tree()
        print(f'string representation   {tree_str}')
        print(f'tree hash               {tree_hash_as_str}')


if __name__ == '__main__':
    main()
