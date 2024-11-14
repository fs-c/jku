def permute(s: str) -> set[str]:
    if len(s) == 0:
        return {''}

    result = set()
    for i, c in enumerate(s):
        string_without_c = s[:i] + s[i + 1:]
        for permutation_without_c in permute(string_without_c):
            result.add(c + permutation_without_c)
    return result
