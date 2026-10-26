# Lean files

Lean 4.26.0 with Mathlib v4.26.0. Both files check with no `sorry`, and every reported declaration
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
| `readable_imp_le_six` | **The dark direction of the read cap**: if every positive map between the ends of a type (d₁, d₂), d₁, d₂ ≥ 2, is decomposable, then d₁d₂ ≤ 6 |

- **Scope.** The existence results are classical: Choi 1975, Woronowicz 1976, and the Horodecki
  families. The explicit integer (2,4) map and its certificate are new here. The readable direction
  d₁d₂ ≤ 6 (Størmer, Woronowicz) is not formalized.
- **Decomposability** is stated with Kraus families.

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
