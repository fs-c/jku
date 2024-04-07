declare -a directories
read -a directories

globs=()

for directory in $directories; do
    globs+=("$directory/**/*.tex")
done

echo "${globs}"
