# read all dimacs files in the given directory and print the number of clauses and variables

import os

def count_clauses_and_variables(file_path):
    with open(file_path, 'r') as file:
        for line in file:
            if line.startswith('p cnf'):
                _, _, num_vars, num_clauses = line.split()
                return int(num_vars), int(num_clauses)
    return 0, 0

def explore_directory(directory_path):
    for file_name in os.listdir(directory_path):
        print(file_name + ": " + str(count_clauses_and_variables(os.path.join(directory_path, file_name))))

if __name__ == "__main__":
    explore_directory("../../test-formulas/")
