from a11_ex1 import create_grid, print_grid, number_of_live_cells
from a11_ex2 import apply_rules
from a11_ex3 import load_grid_from_file, save_grid_to_file

def main():
    print("Welcome to the Game of Life!")

    load_from_file = input("Load initial state from file? (y/n): ")
    if load_from_file == "y":
        filename = input("Enter filename: ")
        grid = load_grid_from_file(filename)
    else:
        rows, cols = [int(x) for x in input("Enter the number of rows and columns: ").split()]
        grid = create_grid(rows, cols)

    print_grid(grid)

    generation = 0
    while True:
        print(f"Generation {generation}, live cells {number_of_live_cells(grid)}")
        generation += 1

        grid = apply_rules(grid)
        print_grid(grid)

        if generation % 10 == 0:
            command = input("Press ENTER to continue, 's' to save, or 'q' to quit: ")

            if command == "s":
                filename = input("Enter filename: ")
                save_grid_to_file(grid, filename)
            elif command == "q":
                break        

if __name__ == "__main__":
    main()
