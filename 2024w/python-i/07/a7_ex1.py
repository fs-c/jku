import os

def get_output_filename(filename: str, keyword: str) -> str:
    name, extension = os.path.splitext(filename)
    return f"{name}_{keyword}{extension}"

def analyze_log_file(filename: str, keyword: str):
    count = 0

    try:
        input_file = open(filename, encoding = 'utf-8', mode = 'r')
        output_file = open(get_output_filename(filename, keyword), encoding = 'utf-8', mode = 'w')

        with input_file, output_file:
            lines = input_file.readlines()

            for line in lines:
                if keyword in line:
                    count += 1
                    output_file.write(line)
    except FileNotFoundError:
        return None

    return count
