def aggregate(*args, **kwargs):
    occurrences = dict()

    for arg in args:
        occurrences[arg] = occurrences.get(arg, 0) + 1
    
    for key, value in kwargs.items():
        occurrences[key] = occurrences.get(key, 0) + value

    return occurrences
