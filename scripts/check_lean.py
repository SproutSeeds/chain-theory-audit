"""Check the Lean files in lean/ against an already-built Mathlib v4.26.0 project and record the results.

Runs `lake env lean <file>` inside a Lake project whose Mathlib v4.26.0 is built. The default is
this repository's `lean/` project (run `lake update` and `lake exe cache get` there first); set
MATHLIB_PROJECT to use another built project.
Usage: python3 scripts/check_lean.py [ChainRP|ChoiDark ...]   (default: all)
"""
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FILES = {"ChainRP": ("ChainRP", "lean_chainrp_check.json"), "ChoiDark": ("ChoiDark", "lean_choidark_check.json"),
         "ReadCap": ("ChainReadCap", "lean_readcap_check.json"),
         "Duality": ("ChainDuality", "lean_duality_check.json")}
# Local modules compiled to .olean first, in order, into a temporary directory.
DEPS = {"ReadCap": ["ChoiDark"], "Duality": ["ChoiDark", "ReadCap"]}
PROJECT = Path(os.environ.get("MATHLIB_PROJECT", str(ROOT / "lean")))
STANDARD = {"propext", "Classical.choice", "Quot.sound"}
ENCODE = json.JSONEncoder(indent=2).encode

def check(name):
    ns, out_name = FILES[name]
    SRC = ROOT / "lean" / f"{name}.lean"
    OUT = ROOT / "results" / out_name
    env = dict(os.environ)
    build = tempfile.TemporaryDirectory()
    if DEPS.get(name):
        env["LEAN_PATH"] = build.name
    for dep in DEPS.get(name, []):
        subprocess.run(["lake", "env", "lean", f"--root={ROOT / 'lean'}", "-o", f"{build.name}/{dep}.olean",
                        str(ROOT / "lean" / f"{dep}.lean")], cwd=PROJECT, capture_output=True, text=True,
                       check=True, env=env)
    run = subprocess.run(["lake", "env", "lean", str(SRC)], cwd=PROJECT, capture_output=True, text=True, env=env)
    build.cleanup()
    version = subprocess.run(["lake", "env", "lean", "--version"], cwd=PROJECT,
                             capture_output=True, text=True).stdout.strip()
    manifest = json.loads((PROJECT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    text = run.stdout + run.stderr
    axioms = {k: [a.strip() for a in v.split(",") if a.strip()]
              for k, v in re.findall(r"'(" + ns + r"\.[\w.]+)' depends on axioms: \[([^\]]*)\]", text)}
    source = SRC.read_text()
    record = {
        "checked_at": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "source": str(SRC.relative_to(ROOT)),
        "source_sha256": hashlib.sha256(source.encode()).hexdigest(),
        "lean_version": version,
        "mathlib_rev": mathlib.get("inputRev"),
        "mathlib_commit": mathlib.get("rev"),
        "returncode": run.returncode,
        "errors": text.count(": error"),
        "warnings": text.count(": warning"),
        "sorry_in_source": len(re.findall(r"\bsorry\b", source)),
        "theorems": len(re.findall(r"^theorem ", source, re.M)),
        "axioms": axioms,
        "standard_axioms_only": all(set(a) <= STANDARD for a in axioms.values()),
    }
    record["pass"] = (record["returncode"] == 0 and record["errors"] == 0 and record["sorry_in_source"] == 0
                      and record["standard_axioms_only"] and len(axioms) > 0)
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(ENCODE(record) + "\n")
    summary = {k: record[k] for k in ("pass", "returncode", "errors", "warnings", "theorems",
                                      "sorry_in_source", "standard_axioms_only", "lean_version")}
    print(name, ENCODE(summary))
    if not record["pass"]:
        print(text[-3000:], file=sys.stderr)
    return record["pass"]


if __name__ == "__main__":
    names = sys.argv[1:] or list(FILES)
    ok = all([check(n) for n in names])
    sys.exit(0 if ok else 1)
