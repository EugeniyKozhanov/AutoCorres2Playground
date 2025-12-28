#!/usr/bin/env python3
"""
Insert FNSPEC annotations from source C file into preprocessed .i file
"""
import sys
import re

def extract_fnspecs(source_file):
    """Extract FNSPEC blocks and their associated function signatures"""
    fnspecs = {}
    with open(source_file, 'r') as f:
        lines = f.readlines()
    
    i = 0
    while i < len(lines):
        # Look for DONT_TRANSLATE
        if 'DONT_TRANSLATE' in lines[i]:
            fnspec_start = i
            # Find the end of the comment block
            while i < len(lines) and '*/' not in lines[i]:
                i += 1
            i += 1  # Include the */ line
            fnspec_block = ''.join(lines[fnspec_start:i])
            
            # Look for function declaration after the comment
            while i < len(lines) and lines[i].strip() == '':
                i += 1
            
            if i < len(lines):
                func_line = lines[i].strip()
                # Extract function name
                match = re.search(r'(\w+)\s*\(', func_line)
                if match:
                    func_name = match.group(1)
                    fnspecs[func_name] = fnspec_block
        i += 1
    
    return fnspecs

def insert_fnspecs(preprocessed_file, fnspecs, output_file):
    """Insert FNSPEC annotations before matching function declarations"""
    with open(preprocessed_file, 'r') as f:
        lines = f.readlines()
    
    with open(output_file, 'w') as out:
        for line in lines:
            # Check if this line is a function declaration we have FNSPEC for
            # Must have return type, function name, and opening paren with semicolon at end
            inserted = False
            for func_name, fnspec in fnspecs.items():
                # Match declaration: return_type func_name(...); not calls like func_name(...)
                if re.match(rf'^[a-zA-Z_][\w\*\s]+{func_name}\s*\([^)]*\)\s*;', line):
                    out.write(fnspec)
                    inserted = True
                    break
            out.write(line)

if __name__ == '__main__':
    if len(sys.argv) != 4:
        print("Usage: insert_fnspec.py <source.c> <preprocessed.i> <output.i>")
        sys.exit(1)
    
    source = sys.argv[1]
    preprocessed = sys.argv[2]
    output = sys.argv[3]
    
    fnspecs = extract_fnspecs(source)
    print(f"Extracted {len(fnspecs)} FNSPEC annotations: {', '.join(fnspecs.keys())}")
    
    insert_fnspecs(preprocessed, fnspecs, output)
    print(f"Generated: {output}")
