def file_statistics(path: str, encoding: str = 'CP1252') -> tuple[int, int, int, list[str]]:
    latin_lowercase = [chr(i) for i in range(ord('a'), ord('z'))]
    latin_uppercase = [chr(i) for i in range(ord('A'), ord('Z'))]
    latin_alph = latin_lowercase + latin_uppercase

    with open(path, encoding = encoding, mode = "r") as file:
        text = file.read()

        latin = 0
        digits = 0
        spaces = 0

        special_chars = []

        for char in text:
            if char in latin_alph:
                latin += 1
            elif char.isdigit():
                digits += 1
            elif char.isspace():
                spaces += 1
            else:
                special_chars.append(char)

        return latin, digits, spaces, special_chars

if __name__ == "__main__":
    print(file_statistics("a7_ex3_cp1252.txt", "CP1252"))
    print(file_statistics("a7_ex3_utf8.txt", "utf-8"))
    print(file_statistics("a7_ex3_utf8.txt", "CP1252"))
