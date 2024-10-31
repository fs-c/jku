def compose(*functions):
    def composed_function(x):
        result = x
        for function in functions[::-1]:
            result = function(result)
        return result
    return composed_function
