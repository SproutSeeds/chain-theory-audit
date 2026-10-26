"""Lane 1b: a pre-registration ledger of Chain Theory's numbers, fixed before new data.

Writes results/preregistration-ledger-2026-10-25.json and prints its SHA-256. The git commit that
adds the ledger, pushed to GitHub, is its timestamp.

Sections
  A  The alpha candidate to 60 digits, its offsets from today's determinations, and a decision
     rule for future ones.
  B  What the Letter's arithmetic gives at other configurations and link types (computed here
     with the Lean port, analysis/census_engine.py). These are NOT claims of the author; they are
     registered so that a later identification of any of them with a measured constant can be
     recognized as post hoc.
  C  Numbers the compendium prints, verbatim, with pages (Release 0.1, 23 Oct 2026), and the
     ratios we infer from them, labelled as our inference.
"""
from __future__ import annotations

import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

from mpmath import mp, mpf, nstr, sqrt

sys.path.insert(0, str(Path(__file__).resolve().parent))
import census_engine as ce  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results" / "preregistration-ledger-2026-10-25.json"
mp.dps = 80
ENCODE = json.JSONEncoder(indent=1, ensure_ascii=False).encode


def alpha_section():
    a = (79 + 48 * sqrt(2) + 42 * sqrt(3) + 3 * sqrt(6)) / 31104
    inv = 1 / a
    dets = [  # value, standard uncertainty, source
        ("CODATA 2022 recommended (input uncertainties expanded x2.5)", "137.035999177", "0.000000021",
         "Mohr et al., RMP 97, 025002 (2025); expansion factor 2.5 on items D1-D6 (checked in the text)"),
        ("Weighted mean of the three inputs, unexpanded (chi2 = 31 on 2 dof)", "137.0359991778", "0.0000000084",
         "computed here from the three rows below"),
        ("Electron g-2 with the SM prediction (Northwestern 2023)", "137.035999166", "0.000000015",
         "Fan et al., PRL 130, 071801 (2023), as quoted in the Letter, Fig. 3"),
        ("Rubidium recoil (LKB Paris 2020)", "137.035999206", "0.000000011",
         "Morel et al., Nature 588, 61 (2020)"),
        ("Cesium recoil (Berkeley 2018)", "137.035999046", "0.000000027",
         "Parker et al., Science 360, 191 (2018)"),
    ]
    rows = [{"determination": n, "inverse_alpha": v, "sigma": s, "source": src,
             "candidate_minus_value_in_sigma": float((inv - mpf(v)) / mpf(s))} for n, v, s, src in dets]
    return {
        "closed_form": "(79 + 48*sqrt(2) + 42*sqrt(3) + 3*sqrt(6)) / 31104",
        "alpha": nstr(a, 60),
        "inverse_alpha": nstr(inv, 60),
        "status_in_source": "Conjecture 1 (Photon) of the Letter: the identification with alpha(0) is conjectured; "
                            "the number is a Lean-checked consequence of stated definitions",
        "current_determinations": rows,
        "decision_rule": {
            "statement": "For a future determination v +/- s of 1/alpha(0) with its own quoted standard uncertainty "
                         "(no expansion factor): |c - v| <= 2s consistent; 2s < |c - v| <= 3s tension; "
                         "|c - v| > 3s excluded by that determination. For a CODATA adjustment, report both the "
                         "expanded and the unexpanded comparison.",
            "decisive_case": "A new cesium-type result agreeing with Berkeley 2018 would exclude the candidate at "
                             "about 5 sigma; agreement of new g-2 and rubidium results near the candidate would "
                             "support it at the next digit.",
            "awaited": ["next-generation electron g-2 (Northwestern)", "rubidium recoil (LKB Paris)",
                        "cesium recoil (Berkeley)", "CODATA 2026 adjustment"],
        },
    }


def elsewhere_section():
    def entry(label, c, e, unread, note=""):
        counts, den = ce.readout(c, e, unread)
        v = sum(n * sqrt(k) for k, n in counts.items()) / den
        return {"configuration": label, "center_dim": c, "read_far_dim": e, "unread_far_dims": list(unread),
                "readout": {"numerator": {str(k): n for k, n in counts.items()}, "denominator": den},
                "value": nstr(v, 25), "inverse": nstr(1 / v, 25), "note": note}
    rows = [
        entry("the Letter's object: qutrit center, two (3,2) reads, one (3,2) unread", 3, 2, (2,),
              "the alpha candidate, for reference"),
        entry("qutrit center, two (3,2) reads, no unread link", 3, 2, ()),
        entry("qutrit center, two (3,2) reads, one (3,3) unread", 3, 2, (3,)),
        entry("qubit center, two (2,2) reads, no unread link (Letter Table S5)", 2, 2, ()),
        entry("qubit center, two (2,2) reads, one (2,2) unread", 2, 2, (2,)),
        entry("(3,3) link, two reads and one unread of its type", 3, 3, (3,), "a dark genre; not readable in the Letter"),
        entry("(4,2) link, two reads and one unread of its type", 4, 2, (2,), "a dark genre; not readable in the Letter"),
        entry("(4,3) link, two reads and one unread of its type", 4, 3, (3,), "a dark genre; not readable in the Letter"),
        entry("(4,4) link, two reads and one unread of its type", 4, 4, (4,), "a dark genre; not readable in the Letter"),
    ]
    return {"label": "Heuristic: our evaluation of the Letter's arithmetic outside its stated scope. NOT claims of "
                     "the author. Registered to make any later identification checkable for post-hoc fitting.",
            "rows": rows}


def compendium_section():
    measured = {"m_mu/m_e": ("206.7682827", "0.0000046"), "m_tau/m_e": ("3477.23", "0.23"),
                "m_p/m_e": ("1836.152673426", "0.000000032")}
    first_powers = {
        "p. 77, eq. (29), one reading": {"e": 67, "mu": 69, "tau": 432, "p": 2709, "n": 8127},
        "p. 79, eq. (31), first power at the stop clause": {"e": 67, "mu": 621, "tau": 432, "p": 8613},
        "p. 79, eq. (31) and p. 95, eq. (45), derived cells": {"e": 67, "mu": 963, "tau": 3969, "p": 2871},
    }
    inferred = []
    for src, fp in first_powers.items():
        for x, mname in (("mu", "m_mu/m_e"), ("tau", "m_tau/m_e"), ("p", "m_p/m_e")):
            if x in fp:
                r = Fraction(fp[x], fp["e"]) ** 2
                v, s = measured[mname]
                inferred.append({"source_cell": src, "ratio": mname, "inferred_value": f"{r.numerator}/{r.denominator}",
                                 "decimal": nstr(mpf(r.numerator) / r.denominator, 12),
                                 "measured_CODATA_2022": f"{v}({s})",
                                 "relative_difference": float((mpf(r.numerator) / r.denominator - mpf(v)) / mpf(v))})
    kd, kh = Fraction(16684819, 24990001), Fraction(1857859, 2927521)
    me, mmu, mtau = mpf("0.51099895069"), mpf("105.6583755"), mpf("1776.86")
    koide_measured = (me + mmu + mtau) / (sqrt(me) + sqrt(mmu) + sqrt(mtau)) ** 2
    cells = [
        {"quantity": "first powers of the bodies (three rule sets, printed side by side)", "pages": "77, 79, 95",
         "printed": first_powers,
         "compendium_says": "\"the passed records at the leptons and the passed leg at the proton are objects of two "
                            "rules\" (p. 78); \"The proton in the electron unit stands outside the comparison by "
                            "orders at every reading the construction has produced\" (p. 419)"},
        {"quantity": "mass ratios (OUR inference: the compendium does not print these ratios)", "pages": "122 (basis)",
         "basis": "\"the standing mass office is its Born square\" (p. 122), read as m_x/m_e = (p_x/p_e)^2",
         "rows": inferred},
        {"quantity": "Koide relation, two spellings", "pages": "362-363, eq. (219)",
         "printed": {"K1_dock": "16684819/24990001", "K1_dock_minus_2/3": "74455/74970003",
                     "K1_hub": "1857859/2927521", "K1_hub_minus_2/3": "-281465/8782563"},
         "decimal": {"K1_dock": nstr(mpf(kd.numerator) / kd.denominator, 12),
                     "K1_hub": nstr(mpf(kh.numerator) / kh.denominator, 12)},
         "measured_from_CODATA_2022_masses": nstr(koide_measured, 10),
         "compendium_says": "\"equals two thirds in the field at no reading\" (Open result 157.1)"},
        {"quantity": "weak mixing angle", "pages": "386, Theorem 164.5 (conditional)",
         "printed": {"cos2_theta_W": "784/1568 = 1/2"}},
        {"quantity": "cosmological term", "pages": "282, eq. (158), Theorem 115.1 (conditional)",
         "printed": {"Lambda": "36^-63"}, "decimal": nstr(mpf(36) ** -63, 12),
         "compendium_says": "\"compared with nothing here\"; no unit is fixed"},
        {"quantity": "coupling at the cap and through the joined web", "pages": "343, eqs. (198)-(199)",
         "printed": {"alpha_cap(k)": "(79 + 48 sqrt2 + 42 sqrt3 + 3 sqrt6) / 319^k",
                     "alpha_cap(k+1)/alpha_cap(k)": "1/319", "alpha_joined": "42^2 = 1764"}},
        {"quantity": "Higgs mass displays", "pages": "492", "printed": {"faces": ["16/67", "12/67"]},
         "compendium_says": "no GeV scale is fixed"},
        {"quantity": "quark mixing", "pages": "391", "printed": {"largest_Jarlskog_square": "1/108"},
         "decimal": {"largest_|J|": nstr(1 / sqrt(108), 12)}},
        {"quantity": "number of generations", "pages": "209-211, Theorem 83.1",
         "printed": {"rungs_at_termination": 3},
         "compendium_says": "at the adopted reading; other readings print other counts (Open result 67.1: two)"},
    ]
    return {"source": "Chain Theory compendium, Release 0.1, working draft dated 23 Oct 2026 "
                      "(https://alexwg.org/publications/ChainTheoryCompendium.pdf); pages are printed page numbers",
            "cells": cells}


def main():
    ledger = {
        "ledger": "Chain Theory pre-registration ledger",
        "prepared": "2026-10-25",
        "purpose": "Fix the theory's numbers before new measurements or new identifications, so that later "
                   "agreement can be told apart from post-hoc fitting.",
        "labels": "ORP: the alpha closed form and the arithmetic are Verified; every identification with a "
                  "physical constant is a Conjecture of its source or our Heuristic inference, as marked.",
        "A_alpha": alpha_section(),
        "B_same_arithmetic_elsewhere": elsewhere_section(),
        "C_compendium_cells": compendium_section(),
    }
    body = ENCODE(ledger) + "\n"
    digest = hashlib.sha256(body.encode()).hexdigest()  # over the exact file bytes
    OUT.parent.mkdir(exist_ok=True)
    OUT.write_text(body)
    (OUT.with_suffix(".sha256")).write_text(f"{digest}  {OUT.name}\n")
    print("sha256", digest)
    print("inverse alpha", ledger["A_alpha"]["inverse_alpha"])
    for r in ledger["A_alpha"]["current_determinations"]:
        print(f"  {r['candidate_minus_value_in_sigma']:+6.2f} sigma  {r['determination']}")
    for r in ledger["B_same_arithmetic_elsewhere"]["rows"]:
        print(f"  1/value = {float(r['inverse']):14.6f}  {r['configuration']}")
    for r in ledger["C_compendium_cells"]["cells"][1]["rows"]:
        print(f"  {r['ratio']:10s} {r['decimal']:>16s} vs {r['measured_CODATA_2022']:>22s}  ({r['relative_difference']:+.2e})  [{r['source_cell']}]")
    k = ledger["C_compendium_cells"]["cells"][2]
    print("  Koide:", k["decimal"], "measured", k["measured_from_CODATA_2022_masses"])


if __name__ == "__main__":
    main()
