#!/usr/bin/env python3
"""Copy the essay to the private tailnet preview host under a label.

  python3 -I scripts/preview.py LABEL [NOTE]

Writes ~/srv/fc-preview/LABEL/index.html (the essay as in the working tree, with the
commit it came from) and rebuilds ~/srv/fc-preview/index.html. Served by the user unit
fc-preview.service on 127.0.0.1:8770 and exposed tailnet-only by `tailscale serve` at
https://the dev machine.taila07ffd.ts.net:8443/. Standard library only.
"""
import html, json, os, re, shutil, subprocess, sys, time

ROOT = os.path.expanduser("~/srv/fc-preview")
label = re.sub(r"[^a-z0-9._-]", "-", sys.argv[1].lower())
note = sys.argv[2] if len(sys.argv) > 2 else ""
repo = subprocess.run(["git", "rev-parse", "--show-toplevel"], capture_output=True, text=True, check=True).stdout.strip()
sha = subprocess.run(["git", "-C", repo, "rev-parse", "--short", "HEAD"], capture_output=True, text=True, check=True).stdout.strip()
dirty = subprocess.run(["git", "-C", repo, "status", "--porcelain", "post/atoms-and-probes.html"], capture_output=True, text=True).stdout.strip()
os.makedirs(os.path.join(ROOT, label), exist_ok=True)
shutil.copy(os.path.join(repo, "post/atoms-and-probes.html"), os.path.join(ROOT, label, "index.html"))
meta_path = os.path.join(ROOT, "previews.json")
meta = json.load(open(meta_path)) if os.path.exists(meta_path) else {}
meta[label] = {"commit": sha + ("+edits" if dirty else ""), "note": note, "time": time.strftime("%Y-%m-%d %H:%M")}
json.dump(meta, open(meta_path, "w"), indent=1)
items = "".join(
    f'<li><a href="{html.escape(k)}/">{html.escape(k)}</a> · commit <code>{html.escape(v["commit"])}</code> · {html.escape(v["time"])}'
    + (f'<br><span style="color:#555">{html.escape(v["note"])}</span>' if v["note"] else "") + "</li>"
    for k, v in sorted(meta.items(), key=lambda kv: kv[1]["time"], reverse=True))
open(os.path.join(ROOT, "index.html"), "w").write(
    '<!doctype html><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Essay previews</title>'
    '<style>body{font:16px/1.5 Georgia,serif;max-width:40em;margin:3em auto;padding:0 1em;color:#222}a{color:#1f5f8b}li{margin:.6em 0}</style>'
    '<h1>Essay previews</h1><p>Private to the tailnet. “Atoms and Probes”, from <code>formal-computation</code>.'
    ' Add <code>#calc=tree</code> or <code>#calc=net</code> to a URL to switch the figures.</p><ul>' + items + "</ul>")
print(f"https://the dev machine.taila07ffd.ts.net:8443/{label}/  (commit {meta[label]['commit']})")
