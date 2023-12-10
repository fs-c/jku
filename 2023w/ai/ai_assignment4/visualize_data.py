import ai_assignments
import matplotlib.pyplot as plt
import argparse
import textwrap
import warnings
import pickle

def plot_data(training_set):
    symbols = [["x", "o"][index] for index in training_set.y]
    for y in set(training_set.y):
        X = training_set.X[training_set.y == y, :]
        plt.scatter(X[:, 0], X[:, 1],
                    color=["red", "blue"][y],
                    marker=symbols[y],
                    label="class: {}".format(y))

def plot_node_boundaries(node, limit_left, limit_right, limit_top, limit_bottom, max_depth=None, level=1):
    split_point = node.split_point
    limit_left_updated = limit_left
    limit_right_updated = limit_right
    limit_top_updated = limit_top
    limit_bottom_updated = limit_bottom

    if node.split_feature == 0:
        if limit_bottom == limit_top:
            warnings.warn('limit_bottom equals limit_top; extending by 0.1')
            plt.plot([split_point, split_point], [limit_bottom - 0.1, limit_top + 0.1], color="purple", alpha=1 / level)
        else:
            plt.plot([split_point, split_point], [limit_bottom, limit_top], color="purple", alpha=1 / level)
        limit_left_updated = split_point
        limit_right_updated = split_point

    else:
        if limit_left == limit_right:
            warnings.warn('limit_left equals limit_right; extending by 0.1')
            plt.plot([limit_left - 0.1, limit_right + 0.1], [split_point, split_point], color="purple", alpha=1 / level)
        else:
            plt.plot([limit_left, limit_right], [split_point, split_point], color="purple", alpha=1 / level)
        limit_top_updated = split_point
        limit_bottom_updated = split_point

    if level == max_depth:
        return
    if node.left_child is not None: plot_node_boundaries(node.left_child, limit_left, limit_right_updated,
                                                         limit_top_updated, limit_bottom, max_depth, level + 1)
    if node.right_child is not None: plot_node_boundaries(node.right_child, limit_left_updated, limit_right, limit_top,
                                                          limit_bottom_updated, max_depth, level + 1)


def main():
    parser = argparse.ArgumentParser(
        description=textwrap.dedent('''
        this script lets you view a 2D-training set in JSON format,
        and will optionally display decision boundaries.
        '''),
        epilog=textwrap.dedent('''
        example usage:

        $ python visualize_data.py test/data.json --tree test/id3.tree --depth 3
        this will visualize the data set 'test/trainset.json', and add
        'test/id3.tree' decision boundaries until depth 3.
        '''),
        formatter_class=argparse.RawDescriptionHelpFormatter
    )
    parser.add_argument('training_set_name', type=str)
    parser.add_argument('--tree', type=str, default=None)
    parser.add_argument('--depth', type=int, default=None)

    args = parser.parse_args()

    training_set = ai_assignments.load_problem_instance(args.training_set_name)
    if training_set.X.shape[1] != 2:
        print('nr. of features in the training set for visualize_data.py needs to be 2, but is {}.'.format(training_set.X.shape[1]))
        print('can you come up with a nice script for visualizing a higher-dimensional dataset and the corresponding tree? contact us for bonus points!')
        exit()
    
    fig = plt.figure()
    plot_data(training_set)

    if args.tree is not None:
        with open(args.tree, 'rb') as fh:
            tree = pickle.load(fh)

            plot_node_boundaries(tree.root,
                                 limit_left=min(training_set.X[:, 0]),
                                 limit_right=max(training_set.X[:, 0]),
                                 limit_top=max(training_set.X[:, 1]),
                                 limit_bottom=min(training_set.X[:, 1]),
                                 max_depth=args.depth
                                 )


    plt.legend()
    plt.tight_layout()
    plt.show()


if __name__ == '__main__':
    main()
