import unittest
import numpy as np
from a11_ex1 import create_grid, count_neighbours, number_of_live_cells, print_grid
from a11_ex2 import apply_rules
from a11_ex3 import load_grid_from_file, save_grid_to_file
import os

class TestGameOfLife(unittest.TestCase):

    def test_create_grid_dimensions(self):
        grid = create_grid(10, 15)
        self.assertEqual(grid.shape, (10, 15))

    def test_create_grid_randomness(self):
        np.random.seed(42)  # Set seed explicitly to ensure determinism
        grid1 = create_grid(5, 5)
        np.random.seed(42)
        grid2 = create_grid(5, 5)
        np.testing.assert_array_equal(grid1, grid2, "Grid creation should be deterministic with the same seed.")

    def test_number_of_live_cells_empty(self):
        grid = np.zeros((5, 5), dtype=int)
        self.assertEqual(number_of_live_cells(grid), 0)

    def test_number_of_live_cells_full(self):
        grid = np.ones((5, 5), dtype=int)
        self.assertEqual(number_of_live_cells(grid), 25)

    def test_number_of_live_cells_mixed(self):
        grid = np.array([[1, 0, 0], [0, 1, 1], [1, 1, 0]])
        self.assertEqual(number_of_live_cells(grid), 5)

    def test_count_neighbours_corner(self):
        grid = np.array([[1, 0], [0, 1]])
        self.assertEqual(count_neighbours(grid, 0, 0), 1)

    def test_count_neighbours_edge(self):
        grid = np.array([[1, 1, 0], [0, 1, 0], [1, 0, 0]])
        self.assertEqual(count_neighbours(grid, 0, 1), 2)

    def test_count_neighbours_center(self):
        grid = np.array([[1, 1, 0], [0, 1, 0], [1, 0, 1]])
        self.assertEqual(count_neighbours(grid, 1, 1), 4)

    def test_apply_rules_underpopulation(self):
        grid = np.array([[0, 1, 0], [0, 1, 0], [0, 0, 0]])
        expected = np.array([[0, 0, 0], [0, 0, 0], [0, 0, 0]])
        result = apply_rules(grid)
        np.testing.assert_array_equal(result, expected)

    def test_apply_rules_survival(self):
        grid = np.array([[0, 1, 0], [1, 1, 0], [0, 1, 0]])
        expected = np.array([[1, 1, 0], [1, 1, 1], [1, 1, 0]])
        result = apply_rules(grid)
        np.testing.assert_array_equal(result, expected)

    def test_apply_rules_overpopulation(self):
        grid = np.array([[1, 1, 1], [1, 1, 1], [1, 1, 1]])
        expected = np.array([[1, 0, 1], [0, 0, 0], [1, 0, 1]])
        result = apply_rules(grid)
        np.testing.assert_array_equal(result, expected)

    def test_apply_rules_reproduction(self):
        grid = np.array([[0, 1, 0], [1, 0, 0], [0, 1, 0]])
        expected = np.array([[0, 0, 0], [1, 1, 0], [0, 0, 0]])
        result = apply_rules(grid)
        np.testing.assert_array_equal(result, expected)

    def test_stable(self):
        grid = np.array([[0, 1, 0], [1, 0, 1], [0, 1, 0]])
        result = apply_rules(grid)
        np.testing.assert_array_equal(grid, result)

    def test_load_grid_from_file(self):
        with open("test_input.txt", "w") as f:
            f.write("101\n010\n101\n")
        expected = np.array([[1, 0, 1], [0, 1, 0], [1, 0, 1]])
        result = load_grid_from_file("test_input.txt")
        np.testing.assert_array_equal(result, expected)
        os.remove("test_input.txt")

    def test_save_grid_to_file(self):
        grid = np.array([[1, 0, 1], [0, 1, 0], [1, 0, 1]])
        save_grid_to_file(grid, "test_output.txt")
        with open("test_output.txt", "r") as f:
            content = f.read()
        self.assertEqual(content, "101\n010\n101\n")
        os.remove("test_output.txt")

    def test_file_round_trip(self):
        original = np.array([[1, 0, 1], [0, 1, 0], [1, 0, 1]])
        save_grid_to_file(original, "test_round_trip.txt")
        loaded = load_grid_from_file("test_round_trip.txt")
        np.testing.assert_array_equal(original, loaded)
        os.remove("test_round_trip.txt")

    def test_print_grid(self):
        grid = np.array([[1, 0, 1], [0, 1, 0], [1, 0, 1]])
        expected_output = "* . *\n. * .\n* . *\n\n"
        from io import StringIO
        import sys
        captured_output = StringIO()
        sys.stdout = captured_output
        print_grid(grid)
        sys.stdout = sys.__stdout__
        self.assertEqual(captured_output.getvalue(), expected_output)

    def test_large_grid_performance(self):
        grid = create_grid(100, 100)
        apply_rules(grid)

    def test_edge_case_empty_grid(self):
        grid = np.zeros((0, 0), dtype=int)
        self.assertEqual(number_of_live_cells(grid), 0)

    def test_edge_case_single_cell(self):
        grid = np.array([[1]])
        self.assertEqual(count_neighbours(grid, 0, 0), 0)
        result = apply_rules(grid)
        expected = np.array([[0]])
        np.testing.assert_array_equal(result, expected)

    def test_grid_after_200_steps(self):
        initial_grid = load_grid_from_file("initial_grid.txt")
        expected_grid = load_grid_from_file("grid_after_200.txt")

        current_grid = initial_grid
        for _ in range(200):
            current_grid = apply_rules(current_grid)

        np.testing.assert_array_equal(current_grid, expected_grid, "Grid after 200 steps does not match expected.")

if __name__ == "__main__":
    unittest.main()
