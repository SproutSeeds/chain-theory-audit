# Lean files

Lean 4.26.0 with Mathlib v4.26.0. All four files check with no `sorry`, and every reported declaration
depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

```sh
cd lean && lake update && lake exe cache get && cd ..
python3 scripts/check_lean.py          # writes results/lean_*_check.json
```

To use another Lake project with Mathlib v4.26.0 built, set `MATHLIB_PROJECT`.

## ChoiDark.lean: every link type with d₁d₂ ≥ 8 is dark (the dark direction of the read cap)

| Declaration | Statement |
|---|---|
| `choi_real` | Choi's inequality in real form: `(Σ aᵢbᵢ)² ≤ Σ (2bᵢ² + b_{i+1}²) aᵢ²`, via a cyclic AM–GM inequality and a weighted Lagrange identity |
| `choi_positive`, `choi_positive_psd` | The Choi map takes every positive semidefinite `Bᴴ B` to a positive semidefinite matrix |
| `rho_partialTranspose`, `rho_ppt` | `ρ₇/₂` and its partial transpose are nonnegative sums of rational rank-one terms (kernel-checked) |
| `W_kraus`, `W_transpose`, `W_choi` | The witness `tr(ρ C_Φ)` is a sum of squares on every `X ↦ K X Kᴴ` and `X ↦ L Xᵀ Lᴴ`, and `-1/14` on the Choi map |
| `choi_not_decomposable` | No finite families give `Φ(X) = Σ K X Kᴴ + Σ L Xᵀ Lᴴ` |
| `rho_entangled` | `ρ` is not a nonnegative combination of product states |
| `dark_33` | There is a positive, non-decomposable map on `M₃(ℂ)` |
| `extendChoi_positive`, `extendChoi_not_decomposable`, `dark_of_three_le` | For all `d₁, d₂ ≥ 3`, the Choi map extended by `X ↦ J₂ Φ(J₁ᴴ X J₁) J₂ᴴ` is positive and not decomposable, so every type with both ends at least 3 is dark |
| `phi24_certificate`, `phi24_positive_psd` | An integer map Φ₂₄ : M₂ → M₄ is positive, by a sum-of-squares identity with multiplier ‖v‖² (found by SDP, rationalized exactly; see `analysis/dark24/`) |
| `rho24_pt`, `W2_kraus`, `W2_transpose`, `W2_phi24`, `phi24_not_decomposable` | P. Horodecki's 2⊗4 PPT state at b = 3/5 gives witness −1 on Φ₂₄ and a sum of squares on every CP and co-CP part, so Φ₂₄ is not decomposable |
| `extend24_positive`, `extend24_not_decomposable` | The same for its extension M₂ → M_d, d ≥ 4 |
| `readable_imp_le_six` | **The dark direction of the read cap**: if every positive linear map between the ends of a type (d₁, d₂), d₁, d₂ ≥ 2, is decomposable, then d₁d₂ ≤ 6 |

- **Definitions.** `Readable` ranges over ℂ-linear maps. `IsPositive` asks that every `w† Φ(Bᴴ B) w`
  be real and nonnegative, which is positive semidefiniteness of `Φ(Bᴴ B)`.
- **Correction, 26 Oct 2026.** Commit `3b95151` defined `Readable` over all functions and `IsPositive`
  by a nonnegative real part only. Under those definitions no type is readable, so
  `readable_imp_le_six` held vacuously. `lean/evidence/VacuityDemo.lean` proves `¬ Readable 2 2`
  under the old definitions, twice: with a nonlinear map that vanishes on positive matrices, and with
  the linear map X ↦ (1 + i) X. The concrete maps and their theorems were unaffected. With the
  corrected definitions, `dark_33`, `dark_of_three_le` and `readable_imp_le_six` say what their
  docstrings say. The theorem count (59) is unchanged; the positivity theorems now also prove that
  the imaginary part vanishes.

- **Scope.** The existence results are classical: Choi 1975, Woronowicz 1976, and the Horodecki
  families. The explicit integer (2,4) map and its certificate are new here. The readable direction
  d₁d₂ ≤ 6 (Størmer, Woronowicz) is reduced to one theorem in `ReadCap.lean` (below).
- **Decomposability** is stated with Kraus families.

## ReadCap.lean: the read cap is equivalent to Woronowicz's theorem

`ReadCap` is copied verbatim from the Letter's `ChainAlpha.lean`. `Woronowicz23` says every positive
linear map M₂ → M₃ is decomposable (Woronowicz 1976; not formalized here). `ReadCap.lean` imports
`ChoiDark` (the check script compiles it first). 18 theorems.

| Declaration | Statement |
|---|---|
| `allDecomposable_mono`, `stormer_of_woronowicz` | Compression: if every positive map M_n → M_m is decomposable, so is every positive map M_{n'} → M_{m'} with n' ≤ n, m' ≤ m; so Woronowicz's theorem gives Størmer's (M₂ → M₂) |
| `adj_positive`, `decomposable_of_adj`, `allDecomposable_symm` | The Hilbert–Schmidt adjoint of a positive map is positive, and a map is decomposable when its adjoint is; so M_n → M_m and M_m → M_n stand or fall together |
| `readable_iff_allDecomposable` | Readability is decomposability of all positive maps in one direction |
| `readcap_iff_woronowicz` | **`ReadCap Readable ↔ Woronowicz23`**: for the Letter's own notion of readability, the read cap is equivalent to Woronowicz's theorem |
| `readable_one_one`, `twist_not_positive` | Regression guards for the corrected definitions: the readable predicate is satisfiable, and X ↦ (1 + i) X is not positive |

- **Prior art.** P. Horodecki and Woronowicz's results are classical. A Lean proof that 2×2 PPT
  matrices are separable (Størmer's theorem in state form, by a different route) is in
  physical-superintelligence/oqp-batch-2026. We know of no formal proof of the 2×3 case.

## Duality.lean: from separable PPT states to decomposable maps

`ReadCap.lean` needs Woronowicz's theorem for maps; the literature proves it for states (every PPT
state on ℂ²⊗ℂ³ is separable). This file bridges the two. 51 theorems; imports `ReadCap`.

| Declaration | Statement |
|---|---|
| `hermitian_of_im_quad`, `positive_conjTranspose`, `choi_hermitian` | A real quadratic form means a Hermitian matrix; positive maps preserve Hermiticity, so their Choi matrices are Hermitian |
| `choi_block_positive` | The Choi matrix of a positive map is nonnegative on product vectors |
| `isClosed_decCone` | The cone {P + Q^Γ : P, Q ⪰ 0} is closed (its bounded-trace slices are images of compact sets) |
| `decomposable_of_choi_mem` | A Choi matrix in that cone gives Kraus families, via the Gram factorization P = B†B |
| `allDecomposable_of_allPPTSeparable` | **If every PPT state on ℂⁿ⊗ℂᵐ is separable, every positive map Mₙ → Mₘ is decomposable** (complex Hahn–Banach: a Choi matrix outside the cone is negative on some PPT state) |
| `readcap_of_pptSeparable23` | **The Letter's read cap follows from the state form of Woronowicz's theorem** |

- The converse (decomposability of all positive maps implies PPT = separable) is classical too but
  is not formalized here.

## ChainRP.lean: reflection positivity of mirror-symmetric webs

| Declaration | Statement |
|---|---|
| `rpForm_eq_sum`, `rpForm_eq_trace` | The Osterwalder–Schrader form `⟨Ψ, (F ⊗ F̄) Ψ⟩` of a state with coefficient matrix `C` is `tr(Cᴴ F C Fᴴ)` |
| `rpForm_of_gram`, `IsGram.rp` | If `C = Bᴴ B`, the form is `Σ |(B F Bᴴ)_ab|²`: real and nonnegative |
| `rpForm_one` | A pair straight across the mirror gives the Hilbert–Schmidt norm |
| `IsGram.mirrorMap`, `.kronecker`, `.add`, `.ptrace`, `.distill` | Gram form is preserved by mirrored local maps, tensoring, superposition, and distillations straddling the mirror (partial trace) |
| `mirrorMap_vec`, `distill_vec` | Those operations act on the state vector as stated |
| `singlet_not_rp`, `crossed_not_rp` | A twisted pair and a crossed pair of pairs give the form `-2` |
| `alpha_object_before_join_rp`, `alpha_object_after_join_rp` | The Letter's object under the exchange of its read links |

**Scope.** The core implication is classical (Lieb 1989; Lieb–Schupp, math-ph/9910037).
