#!/bin/bash

set -e

# Save original directory
ORIG_DIR="$PWD"

# Export environment variables
export L4CAP="/home/ubuntu/playground/chambers/02_pci/haskell"
export L4CPP=""

# Get the translator directory (where this script is located)
TRANSLATOR_DIR="/home/ubuntu/playground/tools/haskell-translator"

# Check if input file is provided
if [ -z "$1" ]; then
    echo "Usage: $0 <input_file>"
    echo "Example: $0 /tmp/filenames.txt"
    exit 1
fi

# Convert input file to absolute path
INPUT_FILE="$(realpath "$1")"

# Check if input file exists
if [ ! -f "$INPUT_FILE" ]; then
    echo "Error: Input file '$INPUT_FILE' not found"
    exit 1
fi

# Go to translator directory
cd "$TRANSLATOR_DIR"

# Run the translator
echo "Running translator with:"
echo "  L4CAP=$L4CAP"
echo "  L4CPP=$L4CPP"
echo "  Input: $INPUT_FILE"
echo ""

python3 pars_skl.py "$INPUT_FILE"

# Return to original directory
cd "$ORIG_DIR"

echo ""
echo "Translation complete. Returned to $ORIG_DIR"
