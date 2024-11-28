import os
import shutil

def organize_directory(src_path: str):
    destination_dir_parent = f"{src_path}_organized"

    with open("move.log", encoding = "utf-8", mode = "w") as log_file:
        if not os.path.exists(src_path):
            log_file.write(f"Error: '{src_path}' is not a valid directory.\n")
            return

        for path, _, file_names in os.walk(src_path):
            for file_name in file_names:
                file_path = os.path.join(path, file_name)

                _, extension = os.path.splitext(file_name)

                destination_dir = os.path.join(destination_dir_parent, extension[1:])
                os.makedirs(destination_dir, exist_ok = True)

                destination_path = os.path.join(destination_dir, file_name)
                shutil.copy2(file_path, destination_path)

                log_file.write(f"Copied '{file_path}' to '{destination_path}'\n")

if __name__ == "__main__":
    organize_directory("a7_ex2_dir")
