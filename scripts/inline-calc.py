#!/usr/bin/env python3
"""Copy the calculus modules of post/lab into the essay, which stays a single file.

  python3 -I scripts/inline-calc.py           rewrite post/atoms-and-probes.html in place
  python3 -I scripts/inline-calc.py --check   exit 1 if the essay's copy is out of date

The modules post/lab/{ski,tree,net,graph}.js (in that order: net.js needs tree.js) go between
the markers

  /* BEGIN CALC (generated from post/lab; do not edit here) */ ... /* END CALC */

in a <script> of their own just before the essay's script. If the markers are missing, that
script is inserted before the first <script> of the body. Running it twice changes nothing.
Standard library only.
"""
import argparse
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ESSAY = os.path.join(ROOT, "post", "atoms-and-probes.html")
MODULES = ["ski.js", "tree.js", "net.js", "graph.js"]
BEGIN = "/* BEGIN CALC (generated from post/lab; do not edit here) */"
END = "/* END CALC */"


def block():
    parts = [BEGIN]
    for name in MODULES:
        src = open(os.path.join(ROOT, "post", "lab", name), encoding="utf-8").read().rstrip("\n")
        if "</script" in src.lower():
            sys.exit(f"post/lab/{name} contains '</script', which would end the inline script")
        parts.append(f"/* ---- post/lab/{name} ---- */")
        parts.append(src)
    parts.append(END)
    return "\n".join(parts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    text = open(ESSAY, encoding="utf-8").read()
    new_block = block()
    i, j = text.find(BEGIN), text.find(END)
    if i >= 0 and j > i:
        new = text[:i] + new_block + text[j + len(END):]
    elif i < 0 and j < 0:
        body = text.find("<body")
        k = text.find("<script>", body if body >= 0 else 0)
        if k < 0:
            sys.exit("no <script> in the essay to insert before")
        new = text[:k] + "<script>\n" + new_block + "\n</script>\n" + text[k:]
    else:
        sys.exit("only one of the CALC markers is in the essay")
    if new == text:
        print("essay up to date")
        return
    if a.check:
        print("the essay's copy of post/lab is out of date: run python3 -I scripts/inline-calc.py")
        sys.exit(1)
    open(ESSAY, "w", encoding="utf-8").write(new)
    print("inlined " + ", ".join(MODULES) + " into post/atoms-and-probes.html")


if __name__ == "__main__":
    main()
