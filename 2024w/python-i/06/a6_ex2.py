def power_set(L: list) -> set[tuple]:
    # sort the list to fix the order of the elements in the output tuples
    L = sorted(L)

    if len(L) == 0:
        return {()}

    last = L[-1]
    rest = L[:-1]
    rest_power_set = power_set(rest)
    return rest_power_set | {subset + (last,) for subset in rest_power_set}
