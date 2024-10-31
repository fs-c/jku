def check_parentheses(s: str):
    open_parentheses = 0

    for c in s:
        if c == "(":
            open_parentheses += 1
        elif c == ")":
            open_parentheses -= 1
            if open_parentheses < 0:
                return False
    
    return open_parentheses == 0
