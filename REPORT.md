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
  - The dark direction of the Letter's `ReadCap` hypothesis: every type with d₁d₂ ≥ 8 has a
    positive, non-decomposable map between its ends. This is proved in Lean via the Choi map and
    an explicit integer map M₂ → M₄.
  - The readable direction is reduced, in Lean, to Woronowicz's theorem for M₂ → M₃: the Letter's
    `ReadCap` holds for its own readability exactly when that theorem does (§7).
  - Readability is a two-mirror reflection-positivity condition on reads. Dark reads are rare among
    random positive maps but robust near the Choi map and Φ₂₄ (§8).
- **Prepared.** A registered protocol for scoring the theory's future numbers blind, with a dry run on
  the numbers it has already printed (§9).

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

## 7. The dark direction of the read cap

Label: Verified. Hook: `lean/ChoiDark.lean`, 59 theorems.

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
- **Extension.** `dark_of_three_le`: for all d₁, d₂ ≥ 3, X ↦ J₂ Φ(J₁ᴴ X J₁) J₂ᴴ is positive and not
  decomposable, since a decomposition would compress to one of the Choi map. This covers Chain
  Theory's (3,3), (3,4), (4,3) and (4,4) genres, so 3 of its 4 dark sectors.
- **The (2,4) case.** An explicit integer map Φ₂₄ : M₂ → M₄.
  - Positivity: a sum-of-squares identity, ‖v‖²·w†Φ₂₄(vv†)w = Σ (rational ≥ 0)·|linear form|²,
    with 40 squares.
  - Non-decomposability: P. Horodecki's 2⊗4 PPT state at b = 3/5 gives tr(ρ C_Φ) = −1.
  - The map and certificate were found by semidefinite programming and rationalized exactly
    (`analysis/dark24/`, `results/dark24_certificate.json`).
  - It extends to M₂ → M_d for every d ≥ 4.
- **Conclusion.** `readable_imp_le_six`: if every positive linear map between the two ends of a
  type (d₁, d₂), d₁, d₂ ≥ 2, is decomposable, then d₁d₂ ≤ 6. This is the dark half of the Letter's
  `ReadCap` hypothesis, for all four of its dark genres.
- **Correction (26 Oct 2026).** The first published version of this theorem (commit `3b95151`)
  held vacuously: its `Readable` ranged over all functions and its positivity asked only for a
  nonnegative real part, so no type was readable (`lean/evidence/VacuityDemo.lean`). The
  definitions now use linear maps and positive semidefiniteness; the concrete maps were unaffected.
- **The readable direction.** `ReadCap.lean` proves `ReadCap Readable ↔ Woronowicz23`: for the
  Letter's own readability, the read cap holds exactly when every positive map M₂ → M₃ is
  decomposable (Woronowicz 1976), which is not formalized here. Compression and Hilbert–Schmidt
  adjoints reduce (2,2) and (3,2) to (2,3). 18 theorems.
- **States to maps.** `Duality.lean` proves that if every PPT state on ℂⁿ⊗ℂᵐ is separable, every
  positive map Mₙ → Mₘ is decomposable (Hahn–Banach, with the decomposable cone shown closed). So the
  read cap follows from the state form of Woronowicz's theorem, the form the literature proves.
  51 theorems.

## 8. Readable as a two-mirror test, and how rare darkness is

Hook: `analysis/readcap_mirror.py` → `results/readcap_mirror.json` (seeded; about 5 minutes with Clarabel).

- **The dictionary.** Label: Exact; 78 random checks agree.
  - Vectorize an operator W on ℂ^{d₁}⊗ℂ^{d₂} as a state on (ket, ket | bra, bra).
  - For a coefficient matrix C the Osterwalder–Schrader form is tr(C†FCF†). For Hermitian C its form
    matrix has eigenvalues λᵢλⱼ, so it is nonnegative for every F exactly when C is semidefinite.
  - The mirror that reflects kets onto bras has coefficient matrix W. The mirror that also swaps the
    second factor's ket and bra has W^Γ.
  - So W ⪰ 0 and W^Γ ⪰ 0 are reflection positivity for two different mirrors. A map is decomposable
    exactly when its Choi matrix splits into a part positive for the first mirror and a part positive
    for the second.
  - This repackages published results: reflection positivity ⇔ complete positivity (Zhao–Liu,
    arXiv:2510.20662, Thm 2.7; Jaffe–Janssens, arXiv:1506.04197), and the partial transpose as a
    different cut or a local time reversal (Calabrese–Cardy–Tonni; Sanpera–Tarrach–Vidal).
- **State-level reflection positivity cannot see darkness.** Label: Verified.
  - A mirrored read Φ ⊗ Φ̄ keeps every reflection-positive state reflection positive, for every
    linear Φ: the dark Choi map, and even a random linear map that is not positive.
  - This is why dark pairs are as reflection positive as readable ones (§6).
- **How common are dark reads?** Label: Verified numerics, in the stated ensemble.
  - Random boundary positive maps W = H − μ(H)·1 (H from the Gaussian unitary ensemble; μ the minimum
    over product vectors) were tested against PPT states by semidefinite programming.
  - None of 1,850 was dark, in any of 2×2, 2×3, 3×2, 2×4, 3×3 (300 each), 3×4 (200) or 4×4 (150).
  - Dark maps still fill open regions. The Choi map stays dark under random perturbations of 10% of its
    norm (60/60), and partly at 30% (37/60). Φ₂₄ stays dark up to 3% (58/60).
  - Normalized darkness margins: Choi −0.0258, Φ₂₄ −0.0036.
  - Darkness is real and robust near special maps, but a random read on a dark link is almost always
    decomposable.

## 9. Blind tests of future numbers

Hooks: `analysis/blind_test.py`, `results/blind_log.jsonl` (hash chained; `python3 analysis/blind_test.py
verify`), `results/blind_dryrun.json`, `scripts/watch_sources.py`.

- **Protocol** `blind-protocol/v1` (sha256 `fb3547453e63c1a091f6ac13a0a864e20ed87d91d348bc2ece700c7a0283404c`,
  entry 0 of the log).
  - A number is registered before it is compared with measurement.
  - The measurement verdict uses §4's rule.
  - The luck test counts how many formulas of the same grammar, no more complex than the prediction,
    land at least as close.
  - Unidentified numbers are never matched against lists of constants.
- **Dry run on the ledger's numbers.** Not blind: they were known before the protocol.
  - **α.** Consistent (z = 0.60 against CODATA 2022 as published, 1.40 unexpanded).
    - Against the Letter's listed alternatives (§2) the match is surprising.
    - Against all formulas of its own form and size (coefficients ≤ 79, denominator 2⁷3⁵) about 0.013
      chance hits are expected: P ≈ 1.3%.
  - **Inferred mass ratios.** All nine readings of m_μ/m_e, m_τ/m_e and m_p/m_e as squared ratios of
    the compendium's first powers are excluded. The nearest misses are as close as fractions with
    denominator ≤ 67 give by chance.
  - **Koide and the weak angle.**
    - The compendium's own Koide values are excluded. Its "two thirds" agrees, but that relation is
      Koide's (1981).
    - cos²θ_W = 1/2 is excluded at the on-shell value 0.7768.
  - **Unscoreable.**
    - "Largest Jarlskog square = 1/108" is the mathematical maximum of J² for any 3×3 unitary.
    - Λ = 36⁻⁶³ and the Higgs displays carry no unit or scale.
- **Source watch.** `scripts/watch_sources.py check` compares the live Letter, compendium and talk and
  the head of github.com/alexwg/chain-theory with the 25 Oct copies. On 26 Oct nothing had changed.

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
