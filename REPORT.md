# An audit of Chain Theory's fine-structure-constant candidate

Cody Mitchell, Fractal Research Group, 25 October 2026.

This audits A. D. Wissner-Gross, *A Parameter-Free Candidate for the Fine-Structure Constant from
Entangled Qudits* (the Letter), its Lean file, and the Chain Theory compendium (Release 0.1), all
dated 23 October 2026. Sources are listed at the end.

**Claim labels.**

| Label | Meaning |
|---|---|
| Exact | a proof or exact computation |
| Verified | checked by an executable hook |
| Heuristic | a reasoned estimate or reading |
| Conjecture | an open statement |

Every Verified or Exact claim names the command that checks it.

## Summary

- **Holds.**
  - The arithmetic. The Lean file checks, and the 172-record count reproduces independently.
  - The value's uniqueness among the alternatives the Letter itself lists. Of 1,492,992
    combinations, only the published one lies within 1σ of CODATA 2022.
- **Open.** How many structurally different constructions were explored during development is
  not in the public record. It is the remaining look-elsewhere question.
- **In tension.** The identification of the number with the photon coupling (Conjecture 1 of the
  Letter) conflicts with the program's own charge assignment, its own unbroken generator and its
  own weak angle.
- **Additional results**, true independently of Chain Theory's physics:
  - Maximally entangled links straight across a mirror are Osterwalder–Schrader reflection
    positive, and so are the webs built from them by mirrored operations.
  - The (3,3) link type is dark: the Choi map is positive and not decomposable. This is proved in
    Lean and discharges the (3,3) instance of the Letter's `ReadCap` hypothesis.

## 1. Replication

Label: Verified.

- **Value.** α = (79 + 48√2 + 42√3 + 3√6)/31104 and 1/α = 137.035999189566155029…
  Hook: `python3 analysis/reproduce_records.py`.
- **Independent rebuild.** Working from the Letter's text alone gives 169 products, 172 records,
  sectors 79/48/42/3 and N = 31104 (same hook).
- **The author's Lean file.** `ChainAlpha.lean` (github.com/alexwg/chain-theory, commit `a28db89`)
  checks on Lean 4.33.1; the file pins 4.35.0. It has no `sorry`, and `main` depends on `propext`
  only.
- **The author's scripts.** `audit.py` passes. `mutations.py` behaves as the Supplement states:
  18 of its 19 mutations fail `main`, and the 19th leaves the value unchanged.

## 2. A census of the Letter's alternatives

Label: Verified (exact enumeration). The interpretation is Heuristic.

- **Hook.** `analysis/census_engine.py` and `analysis/trials_census.py`; results in
  `results/trials_census.json`.
- **Engine.** `census_engine.py` ports Part 1 of `ChainAlpha.lean` line by line, with one switch
  per alternative named in the Letter's Table S5 and the author's `mutations.py`. It also covers
  the nine configurations of Table S2.
- **Validation.** Lean itself agrees with the engine on all 185 checks: the 20 single mutations,
  and all 165 compatible pairs of them. The engine also reproduces Table S5's extra values and
  every Table S2 readout dimension (12 of 12).

| Result | Value |
|---|---|
| Combinations | 1,492,992 |
| Distinct values | 9,275 |
| Within 1σ of CODATA 2022 | 1, the published value |
| Within 1% / 0.1% / 10⁻⁴ / 10⁻⁶ relative | 38 / 5 / 2 / 1 |
| Nearest other values of 1/α | 137.0444, 137.0559, 137.0625 |
| Density near 137 | about 13 distinct values per unit of 1/α |
| Expected chance 1σ hits in the whole space | 5.6 × 10⁻⁷ |

- **Reading.** Within everything the Letter names, the hit is unique and isolated.
  - For a chance 1σ match, a search would need to be about 10⁶ times larger than this whole
    space, roughly 10¹⁰ distinct values.
  - An independent estimate agrees. Among the 1.26 × 10¹⁰ numbers
    (n₁ + n₂√2 + n₃√3 + n₄√6)/(2ᵖ3^q) with nᵢ ≤ 100 and p, q ≤ 10, the candidate is the only one
    within 1σ (`analysis/numerology_density.py`).
- **Limits.** The census covers only the alternatives that can be written down. The formula
  carries about as many bits as the digits it matches, so its evidential weight rests on the
  definitions having been fixed before the comparison.
- **Note.** Table S5's "sums and differences of the commutators both kept"
  (79+48√2+42√3+6√6) differs from `mutations.py`'s `commutators_keep_both` (79+48√2+45√3+3√6).
  The census follows the Lean version.

## 3. Pre-registration ledger

Label: Verified (values).

- **File.** `results/preregistration-ledger-2026-10-25.json`, SHA-256 in the adjacent `.sha256`
  file (`e78c6be6…`). Rebuild with `python3 analysis/preregistration.py`.
- **What it fixes.**
  - The candidate to 60 digits.
  - A decision rule for future determinations: with v ± s and the quoted s, |c − v| ≤ 2s is
    consistent, 2–3s is tension, and > 3s excludes.
  - What the Letter's arithmetic gives at other configurations and link types. These are not
    claims of the author; they are recorded so that a later identification can be told apart
    from fitting after the fact.
  - The compendium's printed numerical cells, with pages.
- **One example.** The compendium prints three rule sets of "first powers" side by side
  (pp. 77, 79, 95).
  - Read through "the standing mass office is its Born square" (p. 122), the "derived cells"
    give (2871/67)² = 1836.186, 18 ppm from m_p/m_e.
  - The other two rule sets miss by factors.
  - These ratios are our reading; the compendium says the proton "stands outside the comparison
    by orders" (p. 419).

## 4. The comparison with measurement

Label: Verified.

| Determination | Candidate offset |
|---|---|
| CODATA 2022 | +0.60σ |
| Electron g−2 (2023) | +1.57σ |
| Rubidium recoil (2020) | −1.49σ |
| Cesium recoil (2018) | +5.32σ |

- **The CODATA expansion.** CODATA 2022 expanded the uncertainties of its α inputs (items D1–D6)
  by 2.5. Against the unexpanded weighted mean of the same three inputs, 137.0359991778(84)
  with χ² = 31 on 2 degrees of freedom, the candidate is 1.40σ off.
- **The decisive case.** A new cesium-type result agreeing with Berkeley 2018 would exclude the
  candidate at about 5σ.

## 5. Internal consistency of the photon identification

Label: Exact computations, given the Letter's own assignments. Hook:
`python3 analysis/consistency_checks.py`.

1. **The stabilizer of the pair ket** reproduces the Letter's Theorem S3: action rank 8,
   dimension 4, and U = i diag(1,1;−1,−1,0) in it.
2. **The unbroken generator.** U = (1/3)(6Y) − (1/3) diag(0,0;1,1,−2). It has no weak-isospin
   component and a color component, so it is not electric charge in any normalization.
3. **No direction of electric charge leaves the pair-ket ray invariant.**
   - The ray's symmetries have dimension 5; they meet weak su(2) in 0 dimensions and color
     su(3) in 1.
   - In the T3 basis, the two terms of the pair ket have electric charges +2/3 and −1/3. These
     are the up and down members of the left-handed quark doublet, which is how the Letter
     describes the link's quantum numbers (Sec. S3).
4. **The weak angle.** The compendium gives cos²θ_W = 1/2 (Theorem 164.5), and
   α_em = α_Y cos²θ_W.
   - If the readout is a hypercharge-type coupling, the implied 1/α_em is 274.07 (per unit Y),
     68.52 (per unit 2Y), 7.61 (per unit Q = 6Y) or 456.79 (GUT-normalized).
   - A match would need a charge scale of √2.
5. **The Ward identity.** It holds for the unit functional and fails for Q and U (Letter
   Theorem S4; compendium p. 317). The compendium reports that the records weighted by U sum to
   zero (Open result 131.1).
6. **The running ladder.** α_cap(k) = numerator/319ᵏ (compendium p. 343) never equals the
   Letter's value, because 31104 is not a power of 319.

## 6. Reflection positivity of chain webs

- **Setting.** A pure state on two mirrored halves has a coefficient matrix C. The reflection is
  θ(F⊗1) = 1⊗F̄, which is the transpose identity of a maximally entangled pair read from the far
  end.
- **Lean.** `lean/ChainRP.lean`, 19 theorems; label Verified.
  - If C = BᴴB, then ⟨Ψ, θ(F)FΨ⟩ = Σ|(BFBᴴ)ₐᵦ|² ≥ 0.
  - Gram form is preserved by: pairs straight across the mirror, mirrored product states,
    mirrored local maps (matchings), tensoring, superposition, and distillations that straddle
    the mirror (a partial trace).
  - Counterexamples: a twisted pair (the singlet) and a crossed pair of pairs both give −2.
  - The core implication is classical (Lieb 1989; Lieb–Schupp, math-ph/9910037); the formal
    check is new.
- **Exact certificates.** `analysis/rp_chain_webs.py`, standard library only; label Verified.
  The full Osterwalder–Schrader Gram matrix of each web is certified by exact LDLᵀ, or refuted by
  a rational witness.

| Case | Result |
|---|---|
| Pairs (2,2), (3,3), (4,4) | All reflection positive, so reflection positivity does not see the read cap |
| The α object under the exchange of its read links | Reflection positive; the Osterwalder–Schrader space has dimension 1 before the join and 36 after |
| Washed (isotropic) pairs | Reflection positive exactly when F ≥ 1/d², while entanglement needs F > 1/d |
| 60 random mirror-symmetric webs | 60 of 60 reflection positive |
| Symmetry-breaking controls | 50 of 59 fail. All 9 survivors are explained: either a repeated projection, or a positive operator acting on a flat state. |

## 7. The (3,3) link type is dark

Label: Verified. Hook: `lean/ChoiDark.lean`, 29 theorems.

The Letter calls a type readable when every positive map between its ends is decomposable, and
carries the read cap (readable ⇔ d₁d₂ ≤ 6) as a named hypothesis citing Størmer, Woronowicz and
Choi. `ChoiDark.lean` proves the (3,3) instance of the dark direction:

- **Choi's inequality.** Proved from a cyclic AM–GM inequality and a weighted Lagrange identity.
  The Choi map takes every positive semidefinite matrix to a positive semidefinite one.
- **The witness.** The PPT state ρ₇/₂ (the Horodecki family) and its partial transpose are
  written as nonnegative sums of rational rank-one terms. The witness tr(ρ C_Φ) is a sum of
  squares on every X ↦ KXKᴴ and every X ↦ LXᵀLᴴ, but −1/14 on the Choi map. So the Choi map is
  not decomposable.
- **Corollaries.** `dark_33`. Also, ρ₇/₂ is PPT and entangled.
- **Not covered.** The (2,4) case (Woronowicz's map), the embedding into larger types, and the
  readable direction (Størmer, Woronowicz).

## Sources

- The Letter: https://alexwg.org/publications/ChainTheoryAlpha.pdf
- The compendium: https://alexwg.org/publications/ChainTheoryCompendium.pdf
- The Lean file and scripts: https://github.com/alexwg/chain-theory
- Announcement: https://youtu.be/udKNcCgP4rA
- CODATA 2022: Mohr, Newell, Taylor and Tiesinga, Rev. Mod. Phys. 97, 025002 (2025)
- Measurements: Fan et al., PRL 130, 071801 (2023); Morel et al., Nature 588, 61 (2020); Parker
  et al., Science 360, 191 (2018)
- Choi, Linear Algebra Appl. 12, 95 (1975); Horodecki, Horodecki and Horodecki, Phys. Lett. A 223,
  1 (1996) and PRL 80, 5239 (1998); Lieb and Schupp, math-ph/9910037

Credit to the author for publishing the Lean file, the alternatives table and the mutation
script. They made this audit possible.
