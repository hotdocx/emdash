import re
import sys

def find_candidates(filename):
    with open(filename, 'r') as f:
        content = f.read()

    # Regex to find symbol declarations.
    # Matches: symbol name (params) : type
    # We are looking for (Arg : Type) which is used later.
    
    # Simplified parser: split by "symbol" or "rule" to isolate declarations
    # This is rough but should catch definitions.
    
    lines = content.splitlines()
    
    for i, line in enumerate(lines):
        line = line.strip()
        if line.startswith("symbol") or line.startswith("constant symbol") or line.startswith("injective symbol"):
            # This is a declaration line.
            # Look for explicit arguments like (A : Cat) or (A B : Cat)
            
            # Regex for explicit args: \(([\w\s]+):([\w\s]+)\)
            # This is too simple for multi-line but let's try line-based first.
            
            explicit_args = re.findall(r'\(([\w\s]+)\s*:\s*([\w\s]+)\)', line)
            
            if explicit_args:
                # print(f"Line {i+1}: {line}")
                for args, type_ in explicit_args:
                    arg_names = args.split()
                    # Check if these args are used in the REST of the line (after their declaration)
                    # We need to find the position of the match to check "after"
                    
                    match = re.search(r'\(' + re.escape(args) + r'\s*:\s*' + re.escape(type_) + r'\)', line)
                    if match:
                        rest = line[match.end():]
                        for arg in arg_names:
                            # Heuristic: arg used as "Obj arg" or "arg ..." or "Type arg"
                            # Simple check: is arg present in rest?
                            if re.search(r'\b' + re.escape(arg) + r'\b', rest):
                                print(f"Line {i+1}: Argument '{arg}' in '({args} : {type_})' is explicit but used later. Candidate for implicit?")
                                # print(f"  Context: {line}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 find_explicit_candidates.py <file.lp>")
        sys.exit(1)
    find_candidates(sys.argv[1])
