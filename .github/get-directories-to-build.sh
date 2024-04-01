#!/usr/bin/env bash

changed_files=( $(git diff --name-only --diff-filter=ACDMR origin/master..HEAD) )

for changed_file in "${changed_files[@]}"; do
    # get the directory of the changed file
    current_dir=$(dirname "${changed_file}")
    dir_to_build=""

    # walk up the parent directories until we find one that contains a .tex file
    while [ "$current_dir" != "." ]; do
        if ls "${current_dir}"/*.tex 1> /dev/null 2>&1; then
            # if this directory contains a .tex file, mark it as the directory to build
            dir_to_build="${current_dir}"
            # don't break out of the loop, this way the 'highest' directory will be chosen
        fi

        # move to the parent directory
        current_dir=$(dirname "${current_dir}")
    done

    if [ -n "${dir_to_build}" ]; then
        echo "${dir_to_build}"
    fi
done
