import os
import dill as pickle

def analyze_and_append_logs(directory: str, output_file: str):
    log_file_to_occurences: dict[str, int] = dict()

    for path, _, file_names in os.walk(directory):
        for file_name in file_names:
            file_path = os.path.join(path, file_name)

            if file_name.endswith(".log"):
                with open(file_path, mode = "r") as log_file:
                    content = log_file.read()
                    log_file_to_occurences[file_path] = content.count("ERROR")

    if os.path.exists(output_file):
        with open(output_file, mode = "rb") as existing_file:
            existing_data = pickle.load(existing_file)
            log_file_to_occurences.update(existing_data)

    with open(output_file, mode = "wb") as output:
        pickle.dump(log_file_to_occurences, output)
