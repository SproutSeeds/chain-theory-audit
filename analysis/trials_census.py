"""Lane 1a: the trials-factor census of the alpha Letter's definitional choices.

1. Validate `census_engine` (a Python port of ChainAlpha.lean, Part 1) against the author's Lean
   file, perturbed exactly as the author's `mutations.py` perturbs it: every single mutation, and
   every pair of mutations whose text edits are compatible, are checked by Lean itself.
2. Check the extra alternatives of the Letter's Table S5 and the readout dimensions of Table S2.
3. Enumerate every combination of the alternatives and report how often a value lands near
   1/alpha = 137.035999..., and how dense the explored values are there.

Usage:
  git clone https://github.com/alexwg/chain-theory   # commit a28db89 was used
  CHAIN_THEORY_REPO=chain-theory LEAN=<lean 4.33+> python3 analysis/trials_census.py [--skip-lean]
"""
from __future__ import annotations

import itertools
import json
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

from mpmath import mp, mpf, sqrt

sys.path.insert(0, str(Path(__file__).resolve().parent))
import census_engine as ce  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results" / "trials_census.json"
UPSTREAM = Path(os.environ.get("CHAIN_THEORY_REPO", str(ROOT / "chain-theory")))  # clone of alexwg/chain-theory
LEAN = os.environ.get("LEAN", "lean")  # Lean 4.33 or later; the author's file pins 4.35.0
CODATA, SIGMA = mpf("137.035999177"), mpf("0.000000021")
UNEXPANDED, SIGMA_U = mpf("137.0359991778"), mpf("0.0000000084")
mp.dps = 40

# The author's mutation names and the engine switches that state the same definition.
MUTATION_SWITCHES = {
    "BASE": {}, "fixesFar_always_true": {}, "reads_at_qubit": {"read_end": "swapped"},
    "X_at_far_end": {"wx": "far"}, "X_where_letters_sit": {"kof": "letters_sit"},
    "Y_at_center": {"wy": "center"}, "X_Y_factors_swapped": {"kof": "swapped"},
    "moved_per_letter": {"moved": "per_letter"}, "copies_separate": {"copies": "separate"},
    "survival_ignores_own_sign": {"survival": "ignore_sign"},
    "commutator_records_carry_no_reads": {"comm_reads": "none"},
    "register_full_unread": {"unread": "full"}, "no_commutator_records": {"comm": "none"},
    "commutators_keep_sums": {"comm": "sum"}, "commutators_keep_both": {"comm": "both"},
    "exch_shift1": {"exch": 1}, "drop_fixed": {"recset": "drop_fixed"},
    "drop_even": {"recset": "drop_even"}, "born_weights": {"weight": "born"},
    "wX_dA_equiv": {"wx": "dA"},
}


# ------------------------------------------------------------------ Lean ground truth
def load_mutations():
    text = (UPSTREAM / "papers/alpha/lean/mutations.py").read_text()
    prefix = text.split("L=os.environ.get")[0]
    ns = {"__file__": str(UPSTREAM / "papers/alpha/lean/mutations.py")}
    exec(compile(prefix, "mutations.py", "exec"), ns)
    return ns["base"], ns["tail"], ns["M"]


def lean_readout(base, tail, subs):
    s = base
    for old, new in subs:
        if old not in s:
            return None  # incompatible edits (two alternatives of one clause)
        s = s.replace(old, new, 1)
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(s + tail)
        path = f.name
    try:
        out = subprocess.run([LEAN, path], capture_output=True, text=True, timeout=600).stdout
    finally:
        os.unlink(path)
    # The #eval output is printed last; an error message from a failed theorem quotes the
    # unperturbed statement (with the base readout) earlier, so take the last match.
    matches = list(re.finditer(r"\(\[((?:\(\d+, -?\d+\)(?:, )?)*)\], (\d+)\)", out))
    if not matches:
        return "no-readout"
    m = matches[-1]
    counts = {int(k): int(v) for k, v in re.findall(r"\((\d+), (-?\d+)\)", m.group(1))}
    return dict(sorted(counts.items())), int(m.group(2))


def engine_readout(switches):
    sw = dict(switches)
    if sw.get("wx") == "dA":  # x = dA, the center dimension, for every read-end rule
        sw.pop("wx")
        counts, nrec = ce_numerator_with_x(3, 2, **sw)
        return dict(sorted(counts.items())), ce.readout_dim(3, 2, (2,), sw.get("unread", "traceless"))
    return ce.readout(3, 2, (2,), **sw)


def ce_numerator_with_x(c, e, **switches):
    sw = dict(ce.DEFAULTS, **switches)
    dA, dB = ce.read_end(c, e, sw["read_end"]), ce.far_end(c, e, sw["read_end"])
    counts: dict[int, int] = {}
    rs = ce.recs(dA, dB, sw["exch"], sw["comm"], sw["comm_reads"], sw["recset"])
    for r in rs:
        k = ce.k_of(r, c, sw, c, e)
        k = {"sqrt": k, "born": k * k, "none": 1}[sw["weight"]]
        counts[k] = counts.get(k, 0) + 1
    return counts, len(rs)


def validate_against_lean(skip):
    base, tail, M = load_mutations()
    names = list(M)
    jobs = [(n,) for n in names] + list(itertools.combinations([n for n in names if n != "BASE"], 2))
    results = []
    if skip:
        return {"skipped": True}

    def run(job):
        subs = [e for n in job for e in M[n]]
        sw = {}
        for n in job:
            for k, v in MUTATION_SWITCHES[n].items():
                if k in sw and sw[k] != v:
                    return job, "conflict", None
                sw[k] = v
        lean = lean_readout(base, tail, subs)
        if lean is None:
            return job, "incompatible-edits", None
        return job, lean, engine_readout(sw)

    with ThreadPoolExecutor(max_workers=6) as pool:
        for job, lean, eng in pool.map(run, jobs):
            if lean in ("conflict", "incompatible-edits"):
                results.append({"mutations": list(job), "status": lean})
                continue
            results.append({"mutations": list(job), "lean": [lean[0], lean[1]] if lean != "no-readout" else lean,
                            "engine": [eng[0], eng[1]], "agree": lean != "no-readout" and lean == eng})
    checked = [r for r in results if "agree" in r]
    return {"singles": sum(1 for r in checked if len(r["mutations"]) == 1),
            "pairs": sum(1 for r in checked if len(r["mutations"]) == 2),
            "skipped_pairs": sum(1 for r in results if "status" in r),
            "agree": sum(r["agree"] for r in checked), "checked": len(checked),
            "disagreements": [r for r in checked if not r["agree"]], "cases": results}


# ------------------------------------------------------------------ the Letter's own tables
def validate_tables():
    rows = []

    def inv(counts, den):
        return float(1 / (sum(mpf(n) * sqrt(k) for k, n in counts.items()) / den))
    checks = [
        ("no weights", dict(weight="none"), (3, 2, (2,)), 180.837),
        ("normalized by the 172 records", dict(norm="records"), (3, 2, (2,)), 0.758),
        ("smallest readable configuration: two (2,2) reads at a shared qubit", {}, (2, 2, ()), 3.535),
    ]
    for name, sw, cfg, expected in checks:
        c, d = ce.readout(*cfg, **sw)
        rows.append({"alternative": name, "readout": [c, d], "inverse": round(inv(c, d), 3),
                     "table_S5": expected, "agree": abs(inv(c, d) - expected) < 5e-4})
    dims = {"qutrit center, 2R 2R": ((3, 2, ()), 1296), "2R 2R 2U (the object)": ((3, 2, (2,)), 31104),
            "2R 2R 3U": ((3, 2, (3,)), 82944), "2R 2R 2U 2U": ((3, 2, (2, 2)), 746496),
            "2R 2R 2U 3U": ((3, 2, (2, 3)), 1990656), "2R 2R 3U 3U": ((3, 2, (3, 3)), 5308416),
            "qubit center, 2R 2R": ((2, 2, ()), 256), "qubit center, 2R 2R 2U": ((2, 2, (2,)), 2304),
            "qubit center, 2R 2R 3U": ((2, 2, (3,)), 6144)}
    for name, (cfg, expected) in dims.items():
        c, d = ce.readout(*cfg)
        nrec = sum(c.values())
        rows.append({"configuration": name, "readout_dim": d, "table_S2": expected, "records": nrec,
                     "agree": d == expected})
    return rows


# ------------------------------------------------------------------ the census
GROUPS = {
    "read_end": ["rule", "swapped"], "wx": ["read", "far", "dA"],
    "kof": ["std", "letters_sit", "swapped"], "wy": ["moved", "center"], "moved": ["set", "per_letter"],
    "copies": ["one", "separate"], "survival": ["own_sign", "ignore_sign"],
    "comm": ["diff", "sum", "both", "none"], "comm_reads": ["carry", "none"],
    "recset": ["all", "drop_fixed", "drop_even"], "weight": ["sqrt", "born", "none"],
    "exch": [2, 1],
}
DEN_GROUPS = {"unread": ["traceless", "full"], "norm": ["N", "records"]}
CONFIGS = [(3, 2, u) for u in [(), (2,), (3,), (2, 2), (2, 3), (3, 3)]] + [(2, 2, u) for u in [(), (2,), (3,)]]


def census():
    names = list(GROUPS)
    readouts = Counter()        # exact readout -> number of definition combinations giving it
    combos = 0
    for c, e, _ in {(c, e, None) for c, e, _ in CONFIGS}:
        unreads = [u for cc, ee, u in CONFIGS if (cc, ee) == (c, e)]
        for vals in itertools.product(*(GROUPS[n] for n in names)):
            sw = dict(zip(names, vals))
            if sw["wx"] == "dA":
                sw2 = {k: v for k, v in sw.items() if k != "wx"}
                counts, nrec = ce_numerator_with_x(c, e, **sw2)
            else:
                counts, nrec = ce.numerator(c, e, **sw)
            num = tuple(sorted(counts.items()))
            for unread, norm in itertools.product(*DEN_GROUPS.values()):
                for u in unreads:
                    den = ce.readout_dim(c, e, u, unread) if norm == "N" else nrec
                    readouts[(num, den)] += 1
                    combos += 1
    # Two readouts are the same number exactly when their canonical forms agree: write each
    # sqrt(k) as a * sqrt(s) with s squarefree and divide through by the denominator
    # (square roots of distinct squarefree integers are linearly independent over Q).
    by_value: dict[tuple, list] = {}
    for (num, den), mult in readouts.items():
        canon = canonical(num, den)
        if not canon:
            continue
        entry = by_value.setdefault(canon, [0, num, den])
        entry[0] += mult
    values = []
    for canon, (mult, num, den) in by_value.items():
        v = sum(n * k ** 0.5 for k, n in num) / den
        if v > 0:
            values.append((1 / v, num, den, mult))
    return combos, readouts, values


def canonical(num, den):
    from fractions import Fraction
    acc: dict[int, Fraction] = {}
    for k, n in num:
        a, s, p = 1, k, 2
        while p * p <= s:
            while s % (p * p) == 0:
                s //= p * p
                a *= p
            p += 1
        acc[s] = acc.get(s, Fraction(0)) + Fraction(n * a, den)
    return tuple(sorted((s, c) for s, c in acc.items() if c))


def main():
    skip = "--skip-lean" in sys.argv
    print("validating the engine against Lean ...", flush=True)
    lean = validate_against_lean(skip)
    if not skip:
        print(f"  Lean cases checked: {lean['checked']} ({lean['singles']} single, {lean['pairs']} pairs), "
              f"agree {lean['agree']}; skipped pairs (alternatives of one clause): {lean['skipped_pairs']}")
        if lean["disagreements"]:
            print("  DISAGREEMENTS:", json.JSONEncoder().encode(lean["disagreements"][:5]))
    tables = validate_tables()
    print(f"  Letter tables: {sum(r['agree'] for r in tables)}/{len(tables)} agree")
    print("running the census ...", flush=True)
    combos, readouts, values = census()
    distinct = len(values)
    target = float(CODATA)
    near = sorted(values, key=lambda t: abs(t[0] - target))
    base_key = (tuple(sorted({1: 79, 2: 48, 3: 42, 6: 3}.items())), 31104)

    def hp_inverse(num, den):
        return 1 / (sum(mpf(n) * sqrt(k) for k, n in num) / den)
    within = {}
    for label, rel in [("1%", 1e-2), ("0.1%", 1e-3), ("1e-4", 1e-4), ("1e-6", 1e-6), ("1e-8", 1e-8)]:
        within[label] = sum(1 for t in values if abs(t[0] - target) / target < rel)
    one_sigma = [t for t in values if abs(hp_inverse(t[1], t[2]) - CODATA) <= SIGMA]
    band = [t for t in values if 130 <= t[0] <= 145]
    density = len(band) / 15.0
    expected_chance = density * 2 * float(SIGMA)
    summary = {
        "definition_combinations": combos,
        "distinct_raw_readouts": len(readouts),
        "distinct_values": distinct,
        "base_multiplicity": sum(t[3] for t in values if canonical(t[1], t[2]) == canonical(*base_key)),
        "within_relative": within,
        "within_1sigma_codata": [{"inverse": float(hp_inverse(t[1], t[2])), "readout": [dict(t[1]), t[2]],
                                  "combinations": t[3]} for t in one_sigma],
        "distinct_values_with_inverse_in_130_145": len(band),
        "density_per_unit_inverse_near_137": density,
        "expected_chance_1sigma_hits_in_this_space": expected_chance,
        "search_size_factor_for_even_odds": (0.69 / expected_chance) if expected_chance else None,
        "nearest_other_values": [{"inverse": round(t[0], 6), "readout": [dict(t[1]), t[2]],
                                  "combinations": t[3]} for t in near[1:11]],
    }
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(json.JSONEncoder(indent=1).encode(
        {"summary": summary, "lean_validation": lean, "table_validation": tables,
         "groups": GROUPS, "denominator_groups": DEN_GROUPS,
         "configurations": [list(c[:2]) + [list(c[2])] for c in CONFIGS]}) + "\n")
    print(json.JSONEncoder(indent=1).encode(summary))


if __name__ == "__main__":
    main()
