# chain-theory-audit

An independent audit of the fine-structure-constant candidate in A. D. Wissner-Gross's
**Chain Theory** (23 October 2026):

α = (79 + 48√2 + 42√3 + 3√6)/31104, with 1/α = 137.035999189566…

The results are in **[REPORT.md](REPORT.md)**. In brief:

| Finding | Label |
|---|---|
| The arithmetic and the author's Lean file check; the 172-record count reproduces independently | Verified |
| Of all 1,492,992 combinations of the alternatives the Letter lists, only the published value lies within 1σ of CODATA 2022 | Verified |
| Against the unexpanded CODATA inputs the candidate is 1.4σ off (0.6σ with CODATA's ×2.5 expansion) | Verified |
| The photon identification conflicts with the program's own charge assignment, unbroken generator and weak angle | Exact, given the Letter's assignments |
| Maximally entangled links straight across a mirror are Osterwalder–Schrader reflection positive (Lean) | Verified |
| The dark direction of the read cap: every type with d₁d₂ ≥ 8 has a positive, non-decomposable map between its ends (Lean; includes an explicit integer map M₂ → M₄) | Verified |
| A timestamped ledger of the theory's numbers, fixed before new measurements | Verified (values) |

## Reproduce

| What | Command | Needs |
|---|---|---|
| Rebuild the 172 records and the closed form | `python3 analysis/reproduce_records.py` | `mpmath` |
| Chance hits in the formula family | `python3 analysis/numerology_density.py` | `numpy` |
| Census of the alternatives | `CHAIN_THEORY_REPO=chain-theory LEAN=lean python3 analysis/trials_census.py` | a clone of github.com/alexwg/chain-theory, and Lean 4.33 or later for the cross-check; `--skip-lean` runs the census alone |
| Pre-registration ledger | `python3 analysis/preregistration.py`, then `cd results && shasum -a 256 -c preregistration-ledger-2026-10-25.sha256` | `mpmath` |
| Internal consistency checks | `python3 analysis/consistency_checks.py` | `mpmath` |
| Reflection-positivity certificates | `python3 analysis/rp_chain_webs.py` | standard library only |
| A link as a reflection-positive double (numerical) | `python3 analysis/rp_double_check.py` | `numpy` |
| How the (2,4) witness was found (SDP, exact rationalization) | see `analysis/dark24/README.md` | `cvxpy`, `numpy` |
| Lean proofs | `cd lean && lake update && lake exe cache get && cd .. && python3 scripts/check_lean.py` | Lean 4.26.0 and Mathlib v4.26.0 |

Recorded outputs are in `results/`.

## Scope

- Nothing here tests Chain Theory's physics beyond the checks named.
- The measurements due from electron g−2 and atom-recoil experiments will decide the candidate.
- The Lean results are classical mathematics; what is new is the formal check:
  - Choi 1975 and the Horodecki family for `ChoiDark.lean`;
  - Woronowicz 1976 for `ReadCap.lean`, which reduces the read cap to his M₂ → M₃ theorem;
  - Lieb 1989 and Lieb–Schupp for `ChainRP.lean`.

Corrections are welcome by issue.

## License

Apache License 2.0 (see [LICENSE](LICENSE)). Copyright 2026 Cody Mitchell.
