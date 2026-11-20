#!/usr/bin/env python3
"""Point every Lean link in the posts at a pinned commit of the public mirror.

  python3 -I scripts/lean-links.py SHA            rewrite links in place
  python3 -I scripts/lean-links.py SHA --check    report only; exit 1 on any problem

Links are found in two forms:

* HTML (post/atoms-and-probes.html):
    <a class="lean" data-lean="SKI.fundamental_K" href="...">   declaration
    <a data-lean-file="AXIOMS.md" href="...">                   file at the commit
    <a data-lean-tree="" href="...">                            repository at the commit
    <code data-lean-commit="">...</code>                         the short commit, as text
* Markdown (post/technical-companion.md): reference definitions `[name]: URL` whose URL points into this
  repository; `name` is the declaration.

A declaration name resolves to the unique declaration whose full name (namespaces + name as
written) equals `FormalComputation.NAME` or ends in `.NAME`. The commit must already be on
the GitHub mirror. Standard library only.
"""
import argparse
import re
import subprocess
import sys

BASE = "https://github.com/maxinelevesque/formal-computation"
FILES = ["post/atoms-and-probes.html", "post/technical-companion.md"]
DECL = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+([^\s:({\[]+)")


def git(*args):
    return subprocess.run(["git", *args], check=True, capture_output=True, text=True).stdout


def index(sha):
    decls = []
    paths = [p for p in git("ls-tree", "-r", "--name-only", sha).split()
             if p.endswith(".lean") and p.startswith("FormalComputation")]
    for path in paths:
        stack = []  # (kind, [components])
        for n, line in enumerate(git("show", f"{sha}:{path}").splitlines(), 1):
            m = re.match(r"^namespace\s+(\S+)", line)
            if m:
                stack.append(("ns", m.group(1).split(".")))
                continue
            m = re.match(r"^section\b\s*(\S*)", line)
            if m:
                stack.append(("sec", [m.group(1)] if m.group(1) else []))
                continue
            m = re.match(r"^end\b\s*(\S*)", line)
            if m and stack:
                stack.pop()
                continue
            m = DECL.match(line)
            if m:
                ns = [c for kind, comps in stack if kind == "ns" for c in comps]
                decls.append((".".join(ns + [m.group(1)]), path, n))
    return decls


def resolve(decls, name):
    exact = [d for d in decls if d[0] == "FormalComputation." + name or d[0] == name]
    if len(exact) == 1:
        return exact[0], None
    cands = [d for d in decls if d[0].endswith("." + name)]
    if len(cands) == 1:
        return cands[0], None
    return None, ("ambiguous: " + ", ".join(d[0] for d in cands)) if cands else "not found"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sha")
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    sha = git("rev-parse", a.sha).strip()
    subprocess.run(["git", "fetch", "-q", "github"], capture_output=True)  # best effort; the check uses the cached ref
    on_mirror = subprocess.run(["git", "merge-base", "--is-ancestor", sha, "github/main"]).returncode == 0
    problems = [] if on_mirror else [f"commit {sha[:12]} is not on github/main"]
    decls = index(sha)
    url = lambda d: f"{BASE}/blob/{sha}/{d[1]}#L{d[2]}"
    total = 0
    for f in FILES:
        text = open(f, encoding="utf-8").read()

        def decl_html(m):
            nonlocal total
            total += 1
            d, err = resolve(decls, m.group(1))
            if err:
                problems.append(f"{f}: {m.group(1)}: {err}")
                return m.group(0)
            return f'data-lean="{m.group(1)}" href="{url(d)}"'

        def decl_md(m):
            nonlocal total
            total += 1
            d, err = resolve(decls, m.group(1))
            if err:
                problems.append(f"{f}: [{m.group(1)}]: {err}")
                return m.group(0)
            return f"[{m.group(1)}]: {url(d)}"

        new = re.sub(r'data-lean="([^"]+)" href="[^"]*"', decl_html, text)
        new = re.sub(r'data-lean-file="([^"]+)" href="[^"]*"',
                     lambda m: f'data-lean-file="{m.group(1)}" href="{BASE}/blob/{sha}/{m.group(1)}"', new)
        new = re.sub(r'data-lean-tree="" href="[^"]*"',
                     lambda m: f'data-lean-tree="" href="{BASE}/tree/{sha}"', new)
        new = re.sub(r'(<code data-lean-commit="">)[^<]*(</code>)', rf"\g<1>{sha[:7]}\g<2>", new)
        new = re.sub(r"^\[([^\]]+)\]: \S*formal-computation\S*$", decl_md, new, flags=re.M)
        new = re.sub(r"(Lean links point to commit `)[0-9a-f]+(`)", rf"\g<1>{sha[:7]}\g<2>", new)
        if new != text:
            if a.check:
                stale = sum(1 for x, y in zip(re.findall(r'href="[^"]*"', text), re.findall(r'href="[^"]*"', new)) if x != y)
                problems.append(f"{f}: {stale} stored link(s) differ from the pin {sha[:12]} (re-run without --check)")
            else:
                open(f, "w", encoding="utf-8").write(new)
    print(f"{total} declaration links at {sha[:12]}; {len(problems)} problems")
    for p in problems:
        print("  " + p)
    sys.exit(1 if problems else 0)


if __name__ == "__main__":
    main()
