def flatten_dict(d: dict) -> dict:
    def recursive_flatten_dict(d, parent_key=None) -> dict:
        flattened: dict[str, type] = dict()

        for key, value in d.items():
            new_key = f"{parent_key}.{key}" if parent_key else key

            if isinstance(value, dict):
                flattened |= recursive_flatten_dict(value, new_key)
            else:
                flattened[new_key] = value

        return flattened
    
    return recursive_flatten_dict(d)
