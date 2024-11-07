def analyze_and_update_collection(my_list, my_set = set()):
    """
    Takes a list of integers and an optional set. Adds the mean of the list to the set after checking conditions.
    
    Args:
    - my_list (list of int): List of integers.
    - my_set (set of int, optional): Set of integers.

    Returns:
    - set of int: Updated set including the mean of `my_list`.
    """

    # Print out last element of `my_list`
    n = len(my_list)
    print(f'The last element of my_list is {my_list[n]}')
    
    # Check if `my_set` and `my_list` contain the same elements
    if my_set is set(my_list) : 
        print('my_set and my_list contain the same elements')

    # Add the round mean value of `my_list` to `my_set`
    mean = int(sum(my_list) / n)
    my_set.add(mean)
    
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
