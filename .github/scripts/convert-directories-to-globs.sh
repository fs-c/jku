directories=$1
globs=()

for directory in $directories; do
    globs+=("$directory/**/*.tex")
done

echo "${globs}"
