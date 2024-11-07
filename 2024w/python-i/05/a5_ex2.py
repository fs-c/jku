def safe_lookup(d, keys, expected_type):
    value = d
    for key in keys:
        if key not in value:
            return 'Key not found'
        value = value[key]

    if not isinstance(value, expected_type):
        raise TypeError(f"Expected {expected_type}, but got {type(value)}")

    return value
