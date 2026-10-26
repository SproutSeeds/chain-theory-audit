"""Has the author published anything new? Read-only check of Chain Theory's public sources.

Compares the live Letter, compendium and talk PDFs and the GitHub head of alexwg/chain-theory with the
baseline in results/source_watch.json (created from the copies downloaded on 25 Oct 2026). A change
means: register any new numbers with analysis/blind_test.py before scoring them.

  python3 scripts/watch_sources.py baseline DIR   record hashes of the saved copies in DIR
  python3 scripts/watch_sources.py check          compare the live sources with the baseline
"""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STATE = ROOT / "results" / "source_watch.json"
SOURCES = {
    "ChainTheoryAlpha.pdf": "https://alexwg.org/publications/ChainTheoryAlpha.pdf",
    "ChainTheoryCompendium.pdf": "https://alexwg.org/publications/ChainTheoryCompendium.pdf",
    "ChainTheoryTalk.pdf": "https://alexwg.org/publications/ChainTheoryTalk.pdf",
}
REPO = "https://github.com/alexwg/chain-theory.git"
ENC = json.JSONEncoder(indent=1)


def sha(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def repo_head() -> str:
    out = subprocess.run(["git", "ls-remote", REPO, "HEAD"], capture_output=True, text=True, timeout=60)
    return out.stdout.split()[0] if out.returncode == 0 and out.stdout else f"error: {out.stderr.strip()[:200]}"


def main(argv):
    cmd = argv[1] if len(argv) > 1 else "check"
    now = datetime.now(timezone.utc).isoformat()
    if cmd == "baseline":
        folder = Path(argv[2])
        state = {"baseline_from": "local copies downloaded 2026-10-25", "recorded_at": now,
                 "files": {name: sha((folder / name).read_bytes()) for name in SOURCES},
                 "repo_head": repo_head(), "checks": []}
        STATE.write_text(ENC.encode(state) + "\n")
        print(ENC.encode(state))
        return
    state = json.loads(STATE.read_text())
    result = {"checked_at": now, "files": {}, "repo_head": repo_head()}
    for name, url in SOURCES.items():
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "chain-theory-audit-watch"})
            with urllib.request.urlopen(req, timeout=60) as r:
                h = sha(r.read())
            result["files"][name] = {"sha256": h, "changed": h != state["files"][name]}
        except Exception as e:  # report, never guess
            result["files"][name] = {"error": str(e)[:200]}
    result["repo_changed"] = result["repo_head"] != state["repo_head"]
    result["any_change"] = result["repo_changed"] or any(v.get("changed") for v in result["files"].values())
    state["checks"].append(result)
    STATE.write_text(ENC.encode(state) + "\n")
    print(ENC.encode(result))


if __name__ == "__main__":
    main(sys.argv)
