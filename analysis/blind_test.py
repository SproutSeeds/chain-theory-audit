"""Step 3: a pre-registered luck test for Chain Theory's numbers.

The protocol (PROTOCOL below) is fixed text. Its SHA-256 is written to an append-only, hash-chained
log (results/blind_log.jsonl) before anything is scored. A future prediction is first *registered*
(its value and closed form, with a timestamp), and only then *scored* against measurement.

Two questions per number:
  M  Does it agree with measurement? z = (c - v) / s with the measurement's own s;
     |z| <= 2 consistent, <= 3 tension, > 3 excluded (the ledger's decision rule).
  L  Is the agreement surprising? The null family is every formula of the same grammar that is no more
     complex than the prediction itself (its own denominators, coefficients and exponents bound the
     family). lambda = expected number of family members at least as close to the measurement, from the
     family's local density; P_chance = 1 - exp(-lambda). P_chance < 0.01 surprising, < 0.5 weakly
     surprising, otherwise expected by chance. The realized count of such members is reported too.

Subcommands:
  python3 analysis/blind_test.py protocol        append the protocol hash to the log (once)
  python3 analysis/blind_test.py register FILE   append a prediction (JSON) to the log, unscored
  python3 analysis/blind_test.py dryrun          score the ledger's numbers (NOT blind: already seen)
"""
from __future__ import annotations

import hashlib
import json
import math
import sys
from datetime import datetime, timezone
from fractions import Fraction
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
LOG = ROOT / "results" / "blind_log.jsonl"
ENC = json.JSONEncoder(sort_keys=True, ensure_ascii=False)

PROTOCOL = """blind-protocol/v1 (Chain Theory study, 26 Oct 2026)
1. Register before scoring: a new number is appended to results/blind_log.jsonl with its closed form,
   source and timestamp before any comparison with measurement is computed.
2. Measurement verdict: z = (c - v)/s with the measurement's own quoted standard uncertainty s and no
   expansion factor; |z| <= 2 consistent, 2 < |z| <= 3 tension, |z| > 3 excluded. For CODATA, report
   the expanded and unexpanded comparisons.
3. Luck test: the null family is all formulas of the prediction's grammar no more complex than the
   prediction (its own bounds). Grammars: rational a/b with b <= B; squared rational (a/b)^2 with b <= B;
   the Letter's form (n1 + n2 sqrt2 + n3 sqrt3 + n4 sqrt6)/(2^p 3^q) with n_i <= C, p <= P, q <= Q.
   Window w = |c - v| (how close the prediction came), floored at s. lambda = local family density
   times 2w; P_chance = 1 - exp(-lambda). Report the realized number of family members within w.
   P_chance < 0.01 surprising; < 0.5 weakly surprising; otherwise expected by chance. For a prediction
   the measurement excludes, the same number only says how unusual the near miss is (near_miss).
4. Only numbers the source identifies with a measured quantity are scored, plus identifications we
   infer from the source's own words, marked as ours. Unidentified numbers are never compared against
   a list of constants (that would be a look-elsewhere search). Numbers without a unit or scale, and
   mathematical bounds, are recorded as unscoreable with the reason.
5. Every score is appended to the log; nothing in the log is edited or deleted.
"""


# ---------- log ----------

def _append(kind: str, payload: dict) -> dict:
    LOG.parent.mkdir(parents=True, exist_ok=True)
    prev = "0" * 64
    seq = 0
    if LOG.exists():
        lines = [l for l in LOG.read_text().splitlines() if l.strip()]
        if lines:
            last = json.loads(lines[-1])
            prev, seq = last["hash"], last["seq"] + 1
    entry = {"seq": seq, "time": datetime.now(timezone.utc).isoformat(), "kind": kind,
             "payload": payload, "prev_hash": prev}
    entry["hash"] = hashlib.sha256(ENC.encode(entry).encode()).hexdigest()
    with LOG.open("a") as f:
        f.write(ENC.encode(entry) + "\n")
    return entry


def verify_log() -> bool:
    prev = "0" * 64
    for i, line in enumerate(l for l in LOG.read_text().splitlines() if l.strip()):
        e = json.loads(line)
        h = e.pop("hash")
        if e["seq"] != i or e["prev_hash"] != prev or hashlib.sha256(ENC.encode(e).encode()).hexdigest() != h:
            return False
        prev = h
    return True


# ---------- verdicts ----------

def measurement_verdict(c: float, v: float, s: float) -> dict:
    z = (c - v) / s
    a = abs(z)
    return {"z": z, "verdict": "consistent" if a <= 2 else "tension" if a <= 3 else "excluded"}


def classify(p: float) -> str:
    return "surprising" if p < 0.01 else "weakly surprising" if p < 0.5 else "expected by chance"


def finish(row: dict) -> dict:
    """For an excluded prediction, relabel the luck test as a near-miss measure (protocol item 3)."""
    m, l = row.get("measurement"), row.get("luck_own_grammar")
    if m and l and m["verdict"] == "excluded" and l.get("P_chance") is not None:
        p = l["P_chance"]
        l["luck"] = "not applicable (excluded)"
        l["near_miss"] = ("an unusually close miss" if p < 0.01 else "a somewhat close miss" if p < 0.5
                          else "a miss as close as chance gives")
    return row


def farey_density(B: int) -> float:
    """Distinct fractions with denominator <= B per unit length (asymptotic 3B^2/pi^2)."""
    return 3 * B * B / math.pi ** 2


def count_fractions(lo: float, hi: float, B: int, exclude: Fraction | None = None) -> int:
    n = 0
    for b in range(1, B + 1):
        for a in range(math.ceil(lo * b), math.floor(hi * b) + 1):
            if math.gcd(a, b) == 1 and Fraction(a, b) != exclude:
                n += 1
    return n


def luck_rational(c: Fraction, v: float, s: float, squared: bool = False) -> dict:
    """Luck test in the family a/b (or (a/b)^2) with b <= the prediction's own denominator."""
    base = c if not squared else None
    if squared:
        root = Fraction(math.isqrt(c.numerator), math.isqrt(c.denominator))
        assert root * root == c
        base = root
    B = base.denominator
    w = max(abs(float(c) - v), s)
    if squared:
        y, wy = math.sqrt(v), w / (2 * math.sqrt(v))
    else:
        y, wy = v, w
    lam = farey_density(B) * 2 * wy
    realized = count_fractions(y - wy, y + wy, B, exclude=base) if B <= 5000 else None
    p = 1 - math.exp(-lam)
    return {"grammar": "(a/b)^2" if squared else "a/b", "B": B, "window": w, "lambda": lam,
            "realized_members_as_close": realized, "P_chance": p, "luck": classify(p)}


def luck_letter_form(inv_c: float, inv_v: float, s: float, C: int, P: int, Q: int) -> dict:
    """Family (n1 + n2 r2 + n3 r3 + n4 r6)/(2^p 3^q), compared in 1/alpha."""
    r2, r3, r6 = math.sqrt(2), math.sqrt(3), math.sqrt(6)
    alpha_v = 1 / inv_v
    w = max(abs(inv_c - inv_v), s)
    wide = 0.05                      # density window in 1/alpha
    n = np.arange(C + 1, dtype=np.float64)
    n2, n3, n4 = np.meshgrid(n, n, n, indexing="ij")
    irr = (n2 * r2 + n3 * r3 + n4 * r6).ravel()
    values, wide_values = set(), set()
    with np.errstate(divide="ignore", invalid="ignore"):
        for p in range(P + 1):
            for q in range(Q + 1):
                N = 2.0 ** p * 3.0 ** q
                # at most one n1 per irr keeps 1/alpha inside the wide window (its width in n1 is < 1)
                lo = N / (inv_v + wide) - irr
                hi = N / (inv_v - wide) - irr
                n1 = np.ceil(lo)
                ok = (n1 <= hi) & (n1 >= 0) & (n1 <= C)
                inv = N / (n1[ok] + irr[ok])
                wide_values.update(np.round(inv, 10).tolist())
                values.update(np.round(inv[np.abs(inv - inv_v) <= w], 10).tolist())
    within = len(values)
    density = len(wide_values) / (2 * wide)   # distinct values per unit of 1/alpha
    lam = density * 2 * w
    p = 1 - math.exp(-lam)
    return {"grammar": "(n1 + n2 sqrt2 + n3 sqrt3 + n4 sqrt6)/(2^p 3^q)", "C": C, "P": P, "Q": Q,
            "window": w, "density_per_unit_inverse": density, "lambda": lam,
            "realized_distinct_values_as_close_including_prediction": within,
            "P_chance": p, "luck": classify(p)}


# ---------- dry run on the ledger ----------

def dry_run() -> list[dict]:
    ledger = json.loads((ROOT / "results/preregistration-ledger-2026-10-25.json").read_text())
    out = []

    # alpha
    inv_c = float(ledger["A_alpha"]["inverse_alpha"][:20])
    codata, s = 137.035999177, 0.000000021
    census = json.loads((ROOT / "results/trials_census.json").read_text())["summary"]
    out.append({"number": "alpha candidate (the Letter)", "identified_by": "source (Conjecture 1)",
                "measurement": measurement_verdict(inv_c, codata, s),
                "measurement_unexpanded": measurement_verdict(inv_c, 137.0359991778, 0.0000000084),
                "luck_own_grammar": luck_letter_form(inv_c, codata, s, C=79, P=7, Q=5),
                "luck_census_of_listed_alternatives": {
                    "expected_chance_1sigma_hits": census["expected_chance_1sigma_hits_in_this_space"],
                    "luck": classify(1 - math.exp(-census["expected_chance_1sigma_hits_in_this_space"]))},
                "note": "Two null families give opposite answers: the paper's own listed alternatives make the "
                        "match surprising; all formulas of the same algebraic form and size do not."})

    # mass ratios (our inference: m_x/m_e = (p_x/p_e)^2)
    meas = {"m_mu/m_e": (206.7682827, 0.0000046), "m_tau/m_e": (3477.23, 0.23), "m_p/m_e": (1836.152673426, 0.000000032)}
    cells = ledger["C_compendium_cells"]["cells"]
    ratios = next(c for c in cells if c["quantity"].startswith("mass ratios"))
    for row in ratios["rows"]:
        c = Fraction(row["inferred_value"])
        v, s_ = meas[row["ratio"]]
        out.append({"number": f"{row['ratio']} = {row['inferred_value']} ({row['source_cell']})",
                    "identified_by": "our inference from p. 122 ('mass office is its Born square')",
                    "measurement": measurement_verdict(float(c), v, s_),
                    "luck_own_grammar": luck_rational(c, v, s_, squared=True)})

    # Koide, from the CODATA mass ratios
    rmu, rtau, srtau = 206.7682827, 3477.23, 0.23
    def koide(rt):
        return (1 + rmu + rt) / (1 + math.sqrt(rmu) + math.sqrt(rt)) ** 2
    K, sK = koide(rtau), abs(koide(rtau + srtau) - koide(rtau - srtau)) / 2
    for name, val, who in (("K1_dock", "16684819/24990001", "source prints it beside 2/3"),
                           ("K1_hub", "1857859/2927521", "source prints it beside 2/3"),
                           ("2/3", "2/3", "source: 'equals two thirds in the field at no reading' (Open result 157.1); "
                                          "the relation is Koide's (1981), not original to Chain Theory; "
                                          "the source's own computed values (K1_dock, K1_hub) do not give it")):
        c = Fraction(val)
        out.append({"number": f"Koide {name} = {val}", "identified_by": who,
                    "measurement": measurement_verdict(float(c), K, sK) | {"measured": K, "sigma": sK},
                    "luck_own_grammar": luck_rational(c, K, sK)})

    # weak mixing angle, on-shell cos^2 = MW^2/MZ^2 (PDG 2024)
    MW, sMW, MZ, sMZ = 80.3692, 0.0133, 91.1876, 0.0021
    c2 = (MW / MZ) ** 2
    sc2 = c2 * math.hypot(2 * sMW / MW, 2 * sMZ / MZ)
    out.append({"number": "cos^2 theta_W = 1/2 (Theorem 164.5, conditional)", "identified_by": "source",
                "measurement": measurement_verdict(0.5, c2, sc2) | {"measured_on_shell": c2, "sigma": sc2},
                "luck_own_grammar": luck_rational(Fraction(1, 2), c2, sc2),
                "note": "The source states no energy scale; compared with the on-shell value MW^2/MZ^2."})

    # generations
    out.append({"number": "generations = 3 (Theorem 83.1, at the adopted reading)", "identified_by": "source",
                "measurement": measurement_verdict(3, 2.9963, 0.0074) | {"measured_N_nu": "2.9963(74), PDG 2024"},
                "luck_own_grammar": {"grammar": "small integers", "P_chance": None,
                                     "luck": "not assessable: any small-integer family hits 3 by construction"},
                "note": "Other readings print other counts (Open result 67.1: two)."})

    # unscoreable
    for name, why in (
            ("largest Jarlskog square = 1/108 (p. 391)",
             "a mathematical bound, not a prediction: |J| <= 1/(6 sqrt3) for every 3x3 unitary matrix, so J^2 <= 1/108; "
             "the measured J ~ 3e-5 is far below it"),
            ("Lambda = 36^-63 (Theorem 115.1, conditional)", "no unit is fixed ('compared with nothing here')"),
            ("Higgs displays 16/67, 12/67 (p. 492)", "no GeV scale is fixed"),
            ("alpha_joined = 42^2 = 1764 (p. 343)", "no measured quantity is named")):
        out.append({"number": name, "unscoreable": why})
    return [finish(r) for r in out]


def main(argv):
    cmd = argv[1] if len(argv) > 1 else "dryrun"
    if cmd == "protocol":
        print(_append("protocol", {"sha256": hashlib.sha256(PROTOCOL.encode()).hexdigest(), "text": PROTOCOL})["hash"])
    elif cmd == "register":
        print(_append("register", json.loads(Path(argv[2]).read_text()))["hash"])
    elif cmd == "dryrun":
        rows = dry_run()
        entry = _append("dryrun", {"label": "NOT blind: the ledger's numbers were seen on 25 Oct before this protocol",
                                   "protocol_sha256": hashlib.sha256(PROTOCOL.encode()).hexdigest(), "rows": rows})
        (ROOT / "results/blind_dryrun.json").write_text(json.JSONEncoder(indent=1).encode(entry) + "\n")
        print("log ok:", verify_log())
        for r in rows:
            m = r.get("measurement", {})
            l = r.get("luck_own_grammar", {})
            print(f"- {r['number'][:70]:70s} | {m.get('verdict', r.get('unscoreable', ''))[:60]:12s} "
                  f"z={m.get('z', float('nan')):.3g} | luck: {l.get('luck', '')} P={l.get('P_chance')}")
    elif cmd == "verify":
        print("log ok:", verify_log())


if __name__ == "__main__":
    main(sys.argv)
