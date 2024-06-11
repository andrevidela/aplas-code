#!/bin/bash

# Define the directory to search
search_dir="src"

replace_extension() {
    local file_path="$1"
    local new_extension="$2"
    # Extract the filename without extension
    filename="${file_path%.*}"
    # Add the new extension
    new_file_path="${filename}.${new_extension}"
    echo "$new_file_path"
}

redirect_to_file() {
    local output_file="$1"
    local output_dir

    # Extract the directory path from the output file path
    output_dir=$(dirname "$output_file")

    # Create the directory if it doesn't exist
    mkdir -p "$output_dir"

    # Save the current stdout (file descriptor 1) to another descriptor (3)
    exec 3>&1

    # Redirect stdout (file descriptor 1) to the output file
    exec 1> "$output_file"
}

# Function to restore stdout
restore_stdout() {
    # Restore the original stdout from descriptor 3
    exec 1>&3

    # Close descriptor 3 as it's no longer needed
    exec 3>&-
}

# Define your script or command to run on each file
process_file() {
    local file_path="$1"
    # Replace the following line with your actual script or command
    echo "Processing file: ../$file_path"
    # For example, you could run a Python script like this:
    # python your_script.py "$file_path"
    #
    local ttm=$(replace_extension $file_path ttm)
    local html=$(replace_extension $file_path html)
    redirect_to_file html/$html
    katla html --config ../config.dhall $file_path ../build/ttc/2024012300/$ttm
    restore_stdout
}

# Export the function so it's available to the subshell
export -f process_file

cd $search_dir
rm -rf html
mkdir html
# Use find to locate all files and process each one
find "." -type f | while read -r file; do
    process_file "$file"
done

cd ..
