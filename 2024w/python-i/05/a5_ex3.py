def safe_list_access(lst, index):
    try:
        return lst[index]
    except TypeError:
        if not isinstance(lst, list):
            return 'First argument is not a list'
        print('Converting Index to integer')
        try:
            return lst[int(index)]
        except ValueError:
            return 'Index cannot be converted to an integer'
        except IndexError:
            return 'Index out of range'
    except IndexError:
        return 'Index out of range'
    finally:
        print('Operation completed')
