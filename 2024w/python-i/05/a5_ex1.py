# fix: don't use set() as default value, it will be shared between calls
def analyze_and_update_collection(my_list, my_set = None):
    """
    Takes a list of integers and an optional set. Adds the mean of the list to the set after checking conditions.

    Args:
    - my_list (list of int): List of integers.
    - my_set (set of int, optional): Set of integers.

    Returns:
    - set of int: Updated set including the mean of `my_list`.
    """

    # fix: ensure that input types match expectations
    assert isinstance(my_list, list), 'Aborted as my_list is not a list'
    assert all(isinstance(item, int) for item in my_list), 'Aborted as my_list contains non integer values'

    # Print out last element of `my_list`
    n = len(my_list)
    # fix: ensure that the list is not empty
    assert n != 0, 'Aborted as my_list must not be empty'
    # fix: list[length] will always be out of bounds, use list[length - 1]
    print(f'The last element of my_list is {my_list[n - 1]}')

    # Check if `my_set` and `my_list` contain the same elements
    # fix: `is` is for checking reference equality, use `==` to check value equality
    if my_set == set(my_list):
        print('my_set and my_list contain the same elements')

    # Add the round mean value of `my_list` to `my_set`
    mean = int(sum(my_list) / n)
    # fix: bad practice to modify inputs, we return a new set
    new_set = set(my_set) if isinstance(my_set, set) else set()
    new_set.add(mean)
    return new_set

if __name__ == "__main__":
    
    items1 = [1,2,4,5]
    items2 = [2,4,6]

    s = analyze_and_update_collection(items1)
    print('Current set:', s)
    s = analyze_and_update_collection(items2)
    print('Current set:', s)
    s = analyze_and_update_collection(items1, my_set=set(items1))
    print('Current set:', s)
    s = analyze_and_update_collection(items1, my_set=set(items2))
    print('Current set:', s)

    try:
        s = analyze_and_update_collection([])
    except AssertionError as e:
        print(e)

    try:
        s = analyze_and_update_collection([str(i) for i in items1])
    except AssertionError as e:
        print(e)
