"""
Compute anonymized ID for the competition results
Usage:
    python3 hash.py
Place this script in the same directory as your solver.py
"""

import hashlib
import re

def normalize(text: str) -> str:
    text = re.sub(r"#.*", "", text)
    text = "".join(text.split())
    return text

def main():
    try:
        with open("solver.py", "r", encoding="utf-8") as f:
            raw = f.read()
    except FileNotFoundError:
        print("Error: solver.py not found in the current directory. Make sure about file name and directory")
        return

    norm = normalize(raw)
    h = hashlib.sha256(norm.encode("utf-8")).hexdigest()

    print(h[:8])  # <- THIS 8 letter code is what you should look for on the results!

if __name__ == "__main__":
    main()


#6c3ca784