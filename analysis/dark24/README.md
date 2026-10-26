# How the (2,4) witness was found

The (2,4) part of `lean/ChoiDark.lean` (Part 7) uses an explicit positive, non-decomposable map
`Φ₂₄ : M₂ → M₄` with integer Choi matrix `W`. It was found and certified as follows.

1. **Search.** `cert.py` sets up a semidefinite program. It looks for a Hermitian `W` that
   minimizes `tr(ρ W)` for the PPT state `ρ` of P. Horodecki's 2 ⊗ 4 family at `b = 3/5`, subject
   to the certificate below.
   - The certificate: `‖e‖² ⟨e⊗f|W|e⊗f⟩ = Σ_t m_tᴴ G_t m_t`, with `G_t ⪰ 0`.
   - The monomial vectors are `m₁ = e_i e_j f_k`, `m₂ = ē_i e_j f_k` and `m₃ = ē_i ē_j f_k`.
   - The certified optimum is about −0.0024 for `tr W = 1`.
2. **Interior point.** `interior.py` fixes `tr(ρ W) ≤ -10⁻³` and maximizes the smallest eigenvalue
   of the `G_t`. This leaves margin for rounding.
3. **Exact rationalization.** `exactify2.py` rounds `W` to integers, solves the coefficient-matching
   system exactly for the `G_t` (the minimal-norm correction of the rounded numerical solution),
   and checks each `G_t` positive definite by exact `LDLᵀ`. The result is `tr(ρ W) = -1` exactly.
4. **Lean source.** `gen_lean.py` emits the Lean source: the map, the sum-of-squares identity with
   integer coefficients, and the rank-one decompositions of `ρ` and its partial transpose.
   `part78_template.lean` holds the hand-written proofs around it.
5. **Export.** `export_certificate.py` writes `results/dark24_certificate.json`.

Requirements: `cvxpy` (with Clarabel) and `numpy`; Python 3.12. The Lean file contains everything
needed to verify the result. These scripts only document how the certificate was found.
