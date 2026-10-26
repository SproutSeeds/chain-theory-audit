/-
ChoiDark.lean

The (3,3) pair type is dark: a positive map on M₃(ℂ) that is not decomposable.

The alpha Letter of Chain Theory calls a type (d₁, d₂) readable when every positive map between the
operator algebras of its ends is decomposable (a completely positive map plus a completely positive
map composed with the transpose), and dark otherwise. Its Lean file carries the "read cap"
(readable ⇔ d₁ d₂ ≤ 6) as a named hypothesis citing Størmer, Woronowicz and Choi. This file proves
the (3,3) instance of the dark direction from scratch, with Choi's map:

  Part 1  Choi's inequality in real form, via the cyclic AM-GM inequality and a weighted Lagrange
          identity.
  Part 2  The Choi map Φ(X)_ii = X_ii + X_{i+1,i+1}, Φ(X)_ij = -X_ij is positive: it takes every
          positive semidefinite matrix Bᴴ B to a positive semidefinite one.
  Part 3  A PPT state ρ on ℂ³ ⊗ ℂ³ (the Horodecki family at a = 7/2), written as a nonnegative sum
          of rational rank-one terms, and its partial transpose as another; checked by the kernel.
  Part 4  The witness tr(ρ C_Φ) is ≥ 0 on every map X ↦ K X Kᴴ and every map X ↦ L Xᵀ Lᴴ, but equals
          -1/14 on the Choi map. Hence the Choi map is not decomposable.
  Part 5  Corollaries: the (3,3) type is dark; ρ is PPT and entangled.

Mathematical status: classical (Choi, Linear Algebra Appl. 12, 95 (1975); Horodecki, Horodecki and
Horodecki, PRL 80, 5239 (1998) and Phys. Lett. A 223, 1 (1996)). New here is the formal check.
Not formalized: the (2,4) case (Woronowicz's map), the embedding to larger types, and the readable
direction d₁ d₂ ≤ 6 (Størmer 1963, Woronowicz 1976).

Check: from a Lake project with Mathlib v4.26.0 built, `lake env lean ChoiDark.lean`.
-/
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum

open Matrix

namespace ChoiDark

/-! ## Part 1. Choi's inequality in real form -/

theorem cyclic_amgm {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ x ^ 2 * z + x * y ^ 2 + y * z ^ 2 - 3 * x * y * z := by
  rcases le_total x y with hxy | hxy <;> rcases le_total y z with hyz | hyz <;>
    rcases le_total z x with hzx | hzx <;>
    nlinarith [mul_nonneg hz (sq_nonneg (x - y)), mul_nonneg hx (sq_nonneg (y - z)),
      mul_nonneg hy (sq_nonneg (z - x)), mul_nonneg hx hy, mul_nonneg hy hz, mul_nonneg hz hx,
      mul_nonneg (sub_nonneg.2 hxy) (sub_nonneg.2 hyz), mul_nonneg (sub_nonneg.2 hyz) (sub_nonneg.2 hzx),
      mul_nonneg (sub_nonneg.2 hzx) (sub_nonneg.2 hxy)]

/-- The identity behind Choi's inequality (a weighted Lagrange identity). -/
theorem choi_key (a0 a1 a2 b0 b1 b2 : ℝ) :
    ((2 * b0 ^ 2 + b1 ^ 2) * (2 * b1 ^ 2 + b2 ^ 2) * (2 * b2 ^ 2 + b0 ^ 2)) *
      (((2 * b0 ^ 2 + b1 ^ 2) * a0 ^ 2 + (2 * b1 ^ 2 + b2 ^ 2) * a1 ^ 2 + (2 * b2 ^ 2 + b0 ^ 2) * a2 ^ 2)
        - (a0 * b0 + a1 * b1 + a2 * b2) ^ 2)
    = ((2 * b0 ^ 2 + b1 ^ 2) * a0 ^ 2 + (2 * b1 ^ 2 + b2 ^ 2) * a1 ^ 2 + (2 * b2 ^ 2 + b0 ^ 2) * a2 ^ 2)
        * ((b0 ^ 2) ^ 2 * b2 ^ 2 + b0 ^ 2 * (b1 ^ 2) ^ 2 + b1 ^ 2 * (b2 ^ 2) ^ 2 - 3 * b0 ^ 2 * b1 ^ 2 * b2 ^ 2)
      + (2 * b2 ^ 2 + b0 ^ 2) * ((2 * b0 ^ 2 + b1 ^ 2) * a0 * b1 - (2 * b1 ^ 2 + b2 ^ 2) * a1 * b0) ^ 2
      + (2 * b1 ^ 2 + b2 ^ 2) * ((2 * b0 ^ 2 + b1 ^ 2) * a0 * b2 - (2 * b2 ^ 2 + b0 ^ 2) * a2 * b0) ^ 2
      + (2 * b0 ^ 2 + b1 ^ 2) * ((2 * b1 ^ 2 + b2 ^ 2) * a1 * b2 - (2 * b2 ^ 2 + b0 ^ 2) * a2 * b1) ^ 2 := by
  ring

theorem sq_zero_of_two_sq_add_sq {x y : ℝ} (h : 2 * x ^ 2 + y ^ 2 = 0) : x = 0 ∧ y = 0 := by
  have hx : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy : y ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg y]
  exact ⟨pow_eq_zero_iff (two_ne_zero) |>.1 hx, pow_eq_zero_iff (two_ne_zero) |>.1 hy⟩

/-- **Choi's inequality**, real form: with `d_i = 2 b_i² + b_{i+1}²`, `(∑ a_i b_i)² ≤ ∑ d_i a_i²`. -/
theorem choi_real (a0 a1 a2 b0 b1 b2 : ℝ) :
    (a0 * b0 + a1 * b1 + a2 * b2) ^ 2 ≤
      (2 * b0 ^ 2 + b1 ^ 2) * a0 ^ 2 + (2 * b1 ^ 2 + b2 ^ 2) * a1 ^ 2 + (2 * b2 ^ 2 + b0 ^ 2) * a2 ^ 2 := by
  have hP := cyclic_amgm (sq_nonneg b0) (sq_nonneg b1) (sq_nonneg b2)
  have hprod : 0 ≤ (2 * b0 ^ 2 + b1 ^ 2) * (2 * b1 ^ 2 + b2 ^ 2) * (2 * b2 ^ 2 + b0 ^ 2) := by positivity
  rcases hprod.lt_or_eq with hpos | hzero
  · have hR := choi_key a0 a1 a2 b0 b1 b2
    have hS : 0 ≤ (2 * b0 ^ 2 + b1 ^ 2) * a0 ^ 2 + (2 * b1 ^ 2 + b2 ^ 2) * a1 ^ 2
        + (2 * b2 ^ 2 + b0 ^ 2) * a2 ^ 2 := by positivity
    have hrhs : 0 ≤ ((2 * b0 ^ 2 + b1 ^ 2) * a0 ^ 2 + (2 * b1 ^ 2 + b2 ^ 2) * a1 ^ 2 + (2 * b2 ^ 2 + b0 ^ 2) * a2 ^ 2)
        * ((b0 ^ 2) ^ 2 * b2 ^ 2 + b0 ^ 2 * (b1 ^ 2) ^ 2 + b1 ^ 2 * (b2 ^ 2) ^ 2 - 3 * b0 ^ 2 * b1 ^ 2 * b2 ^ 2)
      + (2 * b2 ^ 2 + b0 ^ 2) * ((2 * b0 ^ 2 + b1 ^ 2) * a0 * b1 - (2 * b1 ^ 2 + b2 ^ 2) * a1 * b0) ^ 2
      + (2 * b1 ^ 2 + b2 ^ 2) * ((2 * b0 ^ 2 + b1 ^ 2) * a0 * b2 - (2 * b2 ^ 2 + b0 ^ 2) * a2 * b0) ^ 2
      + (2 * b0 ^ 2 + b1 ^ 2) * ((2 * b1 ^ 2 + b2 ^ 2) * a1 * b2 - (2 * b2 ^ 2 + b0 ^ 2) * a2 * b1) ^ 2 := by
      have := mul_nonneg hS hP
      positivity
    rw [← hR] at hrhs
    exact sub_nonneg.1 (nonneg_of_mul_nonneg_right (by linarith) hpos)
  · rcases mul_eq_zero.1 hzero.symm with h | h
    · rcases mul_eq_zero.1 h with h | h
      · obtain ⟨rfl, rfl⟩ := sq_zero_of_two_sq_add_sq h
        nlinarith [sq_nonneg (a1 * b2), sq_nonneg (a2 * b2)]
      · obtain ⟨rfl, rfl⟩ := sq_zero_of_two_sq_add_sq h
        nlinarith [sq_nonneg (a0 * b0), sq_nonneg (a2 * b0)]
    · obtain ⟨rfl, rfl⟩ := sq_zero_of_two_sq_add_sq h
      nlinarith [sq_nonneg (a0 * b1), sq_nonneg (a1 * b1)]


/-! ## Part 2. The Choi map is positive -/

def nxt : Fin 3 → Fin 3 := ![1, 2, 0]

/-- The Choi map on `M₃(ℂ)`: diagonal `X i i + X (i+1) (i+1)`, off-diagonal `-X i j`. -/
def choiMap (X : Matrix (Fin 3) (Fin 3) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => if i = j then X i i + X (nxt i) (nxt i) else -X i j

theorem choi_form_eq (v w : Fin 3 → ℂ) :
    star w ⬝ᵥ (choiMap (vecMulVec v (star v)) *ᵥ w)
      = (2 * (star (v 0) * v 0) + star (v 1) * v 1) * (star (w 0) * w 0)
        + (2 * (star (v 1) * v 1) + star (v 2) * v 2) * (star (w 1) * w 1)
        + (2 * (star (v 2) * v 2) + star (v 0) * v 0) * (star (w 2) * w 2)
        - (star (w 0) * v 0 + star (w 1) * v 1 + star (w 2) * v 2)
          * star (star (w 0) * v 0 + star (w 1) * v 1 + star (w 2) * v 2) := by
  simp only [dotProduct, mulVec, choiMap, vecMulVec_apply, Fin.sum_univ_three, Pi.star_apply, nxt,
    star_add, star_mul', star_star]
  simp
  ring

theorem normSq_sum3_le (z0 z1 z2 : ℂ) :
    Complex.normSq (z0 + z1 + z2) ≤ (‖z0‖ + ‖z1‖ + ‖z2‖) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have h : ‖z0 + z1 + z2‖ ≤ ‖z0‖ + ‖z1‖ + ‖z2‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

theorem star_mul_self_eq (z : ℂ) : star z * z = (Complex.normSq z : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]; rfl

/-- **The Choi map is positive** (on rank-one inputs; Part 3 extends to every PSD input):
`w† Φ(v v†) w` is real and nonnegative. -/
theorem choi_positive (v w : Fin 3 → ℂ) :
    0 ≤ (star w ⬝ᵥ (choiMap (vecMulVec v (star v)) *ᵥ w)).re ∧
      (star w ⬝ᵥ (choiMap (vecMulVec v (star v)) *ᵥ w)).im = 0 := by
  set T := star (w 0) * v 0 + star (w 1) * v 1 + star (w 2) * v 2 with hT
  have hTT : T * star T = (Complex.normSq T : ℂ) := Complex.mul_conj T
  have hE : star w ⬝ᵥ (choiMap (vecMulVec v (star v)) *ᵥ w)
      = (((2 * Complex.normSq (v 0) + Complex.normSq (v 1)) * Complex.normSq (w 0)
        + (2 * Complex.normSq (v 1) + Complex.normSq (v 2)) * Complex.normSq (w 1)
        + (2 * Complex.normSq (v 2) + Complex.normSq (v 0)) * Complex.normSq (w 2)
        - Complex.normSq T : ℝ) : ℂ) := by
    rw [choi_form_eq, ← hT, hTT]
    simp only [star_mul_self_eq]
    push_cast
    ring
  rw [hE, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  have hT2 : Complex.normSq T ≤ (‖w 0‖ * ‖v 0‖ + ‖w 1‖ * ‖v 1‖ + ‖w 2‖ * ‖v 2‖) ^ 2 := by
    have := normSq_sum3_le (star (w 0) * v 0) (star (w 1) * v 1) (star (w 2) * v 2)
    simpa [norm_mul, norm_star] using this
  have hc := choi_real ‖w 0‖ ‖w 1‖ ‖w 2‖ ‖v 0‖ ‖v 1‖ ‖v 2‖
  simp only [Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_eq_norm_sq] at hT2
  nlinarith [hT2, hc]


/-! ## Part 3. The PPT state

The PPT state rho_{7/2} of the Horodecki family, as an explicit nonnegative sum of rank-one
terms over ℚ, and its partial transpose as another. Index `(i, a)`: first factor `i`, second `a`. -/


def basisQ (p : Fin 3 × Fin 3) : Fin 3 × Fin 3 → ℚ := fun x => if x = p then 1 else 0

/-- The seven rank-one terms of rho: `Σ|ii⟩` with weight 2/21, `|i, i+1⟩` with 1/6, `|i+1, i⟩` with 1/14. -/
def rhoVec : Fin 7 → Fin 3 × Fin 3 → ℚ := ![
  fun x => if x.1 = x.2 then 1 else 0,
  basisQ (0, 1), basisQ (1, 2), basisQ (2, 0),
  basisQ (1, 0), basisQ (2, 1), basisQ (0, 2)]
def rhoWt : Fin 7 → ℚ := ![2/21, 1/6, 1/6, 1/6, 1/14, 1/14, 1/14]

def rhoQ (x y : Fin 3 × Fin 3) : ℚ := ∑ k, rhoWt k * rhoVec k x * rhoVec k y

/-- The nine rank-one terms of the partial transpose: `|ii⟩` with 2/21,
`|i+1, i⟩ + (4/3)|i, i+1⟩` with 1/14, and `|i, i+1⟩` with 5/126. -/
def ptVec : Fin 9 → Fin 3 × Fin 3 → ℚ := ![
  basisQ (0, 0), basisQ (1, 1), basisQ (2, 2),
  fun x => basisQ (1, 0) x + 4/3 * basisQ (0, 1) x,
  fun x => basisQ (2, 1) x + 4/3 * basisQ (1, 2) x,
  fun x => basisQ (0, 2) x + 4/3 * basisQ (2, 0) x,
  basisQ (0, 1), basisQ (1, 2), basisQ (2, 0)]
def ptWt : Fin 9 → ℚ := ![2/21, 2/21, 2/21, 1/14, 1/14, 1/14, 5/126, 5/126, 5/126]

/-- The partial transpose on the second factor, `ρ^Γ((j,a),(i,b)) = ρ((j,b),(i,a))`, equals the
nonnegative sum `ptQ`. -/
theorem rho_partialTranspose :
    ∀ j a i b : Fin 3, rhoQ (j, b) (i, a) = ∑ k, ptWt k * ptVec k (j, a) * ptVec k (i, b) := by
  decide +kernel

theorem rho_trace : ∑ x, rhoQ x x = 1 := by decide +kernel



/-- The entries of `ρ` as an explicit table. -/
def rhoE (x y : Fin 3 × Fin 3) : ℚ :=
  (if x.1 = x.2 ∧ y.1 = y.2 then 2 / 21 else 0) +
  (if x = y ∧ (x = (0, 1) ∨ x = (1, 2) ∨ x = (2, 0)) then 1 / 6 else 0) +
  (if x = y ∧ (x = (1, 0) ∨ x = (2, 1) ∨ x = (0, 2)) then 1 / 14 else 0)

theorem rhoQ_eq_rhoE : ∀ x y, rhoQ x y = rhoE x y := by decide +kernel

/-- The same table in `ℂ`. -/
noncomputable def rhoC (x y : Fin 3 × Fin 3) : ℂ :=
  (if x.1 = x.2 ∧ y.1 = y.2 then 2 / 21 else 0) +
  (if x = y ∧ (x = (0, 1) ∨ x = (1, 2) ∨ x = (2, 0)) then 1 / 6 else 0) +
  (if x = y ∧ (x = (1, 0) ∨ x = (2, 1) ∨ x = (0, 2)) then 1 / 14 else 0)

theorem rhoQ_cast (x y : Fin 3 × Fin 3) : (rhoQ x y : ℂ) = rhoC x y := by
  rw [rhoQ_eq_rhoE]; unfold rhoE rhoC; split_ifs <;> norm_num

/-! ## Part 4. The witness and non-decomposability -/

set_option maxHeartbeats 1000000

abbrev M3 := Matrix (Fin 3) (Fin 3) ℂ

/-- The matrix unit `E i j`. -/
def E (i j : Fin 3) : M3 := fun r c => if r = i ∧ c = j then 1 else 0

/-- The witness functional of `ρ` on a linear map `Φ` of `M₃`: `tr(ρ C_Φ)`, with the Choi matrix
`C_Φ = Σ E_ij ⊗ Φ(E_ij)`, entries `C_Φ((i,a),(j,b)) = Φ(E_ij)_ab`. -/
noncomputable def W (Φ : M3 → M3) : ℂ := ∑ i, ∑ j, ∑ a, ∑ b, (rhoQ (j, b) (i, a) : ℂ) * Φ (E i j) a b

theorem W_add (Φ Ψ : M3 → M3) : W (fun X => Φ X + Ψ X) = W Φ + W Ψ := by
  simp only [W, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem W_sum {ι : Type*} (s : Finset ι) (F : ι → M3 → M3) :
    W (fun X => ∑ k ∈ s, F k X) = ∑ k ∈ s, W (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [W]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [W_add (F a) (fun X => ∑ k ∈ s, F k X), ih]

theorem kEK (K : M3) (i j a b : Fin 3) : (K * E i j * Kᴴ) a b = K a i * star (K b j) := by
  simp [Matrix.mul_apply, E, Matrix.conjTranspose_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

theorem LEtL (L : M3) (i j a b : Fin 3) : (L * (E i j)ᵀ * Lᴴ) a b = L a j * star (L b i) := by
  simp [Matrix.mul_apply, E, Matrix.conjTranspose_apply, Matrix.transpose_apply, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

/-- On a completely positive part `X ↦ K X Kᴴ`, the witness is a nonnegative sum of squares
(one for each rank-one term of `ρ`). -/
theorem W_kraus (K : M3) :
    W (fun X => K * X * Kᴴ)
      = ((2 / 21 : ℚ) : ℂ) * ((K 0 0 + K 1 1 + K 2 2) * star (K 0 0 + K 1 1 + K 2 2))
        + ((1 / 6 : ℚ) : ℂ) * (K 1 0 * star (K 1 0) + K 2 1 * star (K 2 1) + K 0 2 * star (K 0 2))
        + ((1 / 14 : ℚ) : ℂ) * (K 0 1 * star (K 0 1) + K 1 2 * star (K 1 2) + K 2 0 * star (K 2 0)) := by
  simp only [W, kEK, rhoQ_cast, rhoC, Fin.sum_univ_three]
  simp
  ring

/-- On a part composed with the transpose, `X ↦ L Xᵀ Lᴴ`, the witness is again a nonnegative sum of
squares, now one for each rank-one term of the partial transpose of `ρ`. -/
theorem W_transpose (L : M3) :
    W (fun X => L * Xᵀ * Lᴴ)
      = ((2 / 21 : ℚ) : ℂ) * (L 0 0 * star (L 0 0) + L 1 1 * star (L 1 1) + L 2 2 * star (L 2 2))
        + ((1 / 14 : ℚ) : ℂ) * ((L 0 1 + 4 / 3 * L 1 0) * star (L 0 1 + 4 / 3 * L 1 0)
            + (L 1 2 + 4 / 3 * L 2 1) * star (L 1 2 + 4 / 3 * L 2 1)
            + (L 2 0 + 4 / 3 * L 0 2) * star (L 2 0 + 4 / 3 * L 0 2))
        + ((5 / 126 : ℚ) : ℂ) * (L 1 0 * star (L 1 0) + L 2 1 * star (L 2 1) + L 0 2 * star (L 0 2)) := by
  simp only [W, LEtL, rhoQ_cast, rhoC, Fin.sum_univ_three]
  simp [star_add, star_mul']
  ring


/-- **The witness is negative on the Choi map**: `tr(ρ C_Φ) = -1/14`. -/
theorem W_choi : W choiMap = -1 / 14 := by
  simp only [W, rhoQ_cast, rhoC, choiMap, E, nxt, Fin.sum_univ_three]
  simp
  norm_num

theorem re_wsq_nonneg (c : ℚ) (hc : 0 ≤ c) (z : ℂ) : 0 ≤ ((c : ℂ) * (z * star z)).re := by
  have hz : z * star z = (Complex.normSq z : ℂ) := Complex.mul_conj z
  have hcr : (c : ℂ) = ((c : ℝ) : ℂ) := by norm_cast
  rw [hz, hcr, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (by exact_mod_cast hc) (Complex.normSq_nonneg z)

theorem re_wsum3_nonneg (c : ℚ) (hc : 0 ≤ c) (z1 z2 z3 : ℂ) :
    0 ≤ ((c : ℂ) * (z1 * star z1 + z2 * star z2 + z3 * star z3)).re := by
  rw [mul_add, mul_add, Complex.add_re, Complex.add_re]
  exact add_nonneg (add_nonneg (re_wsq_nonneg c hc z1) (re_wsq_nonneg c hc z2)) (re_wsq_nonneg c hc z3)

/-- **The Choi map is not decomposable.** No finite families `K`, `L` give
`Φ(X) = Σ K X Kᴴ + Σ L Xᵀ Lᴴ`: it is not a completely positive map plus a completely positive map
composed with the transpose. -/
theorem choi_not_decomposable :
    ¬ ∃ (m n : ℕ) (K : Fin m → M3) (L : Fin n → M3),
      ∀ X, choiMap X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ := by
  rintro ⟨m, n, K, L, h⟩
  have hfun : choiMap = fun X => (fun X => ∑ k, K k * X * (K k)ᴴ) X
      + (fun X => ∑ l, L l * Xᵀ * (L l)ᴴ) X := funext h
  have h1 : W choiMap = ∑ k, W (fun X => K k * X * (K k)ᴴ) + ∑ l, W (fun X => L l * Xᵀ * (L l)ᴴ) := by
    rw [hfun, W_add, W_sum, W_sum]
  have h2 : 0 ≤ (W choiMap).re := by
    rw [h1, Complex.add_re, Complex.re_sum, Complex.re_sum]
    refine add_nonneg (Finset.sum_nonneg fun k _ => ?_) (Finset.sum_nonneg fun l _ => ?_)
    · rw [W_kraus, Complex.add_re, Complex.add_re]
      exact add_nonneg (add_nonneg (re_wsq_nonneg _ (by norm_num) _) (re_wsum3_nonneg _ (by norm_num) _ _ _))
        (re_wsum3_nonneg _ (by norm_num) _ _ _)
    · rw [W_transpose, Complex.add_re, Complex.add_re]
      exact add_nonneg (add_nonneg (re_wsum3_nonneg _ (by norm_num) _ _ _)
        (re_wsum3_nonneg _ (by norm_num) _ _ _)) (re_wsum3_nonneg _ (by norm_num) _ _ _)
  rw [W_choi] at h2
  norm_num at h2


/-! ### Positivity on every positive semidefinite input (completes Part 2) -/

theorem choiMap_sum {ι : Type*} (s : Finset ι) (X : ι → M3) :
    choiMap (∑ r ∈ s, X r) = ∑ r ∈ s, choiMap (X r) := by
  ext i j
  simp only [choiMap, Matrix.sum_apply]
  split_ifs <;> simp [Finset.sum_add_distrib, Finset.sum_neg_distrib]

/-- The Choi map takes every positive semidefinite matrix `Bᴴ B` to a positive semidefinite one. -/
theorem choi_positive_psd {m : ℕ} (B : Matrix (Fin m) (Fin 3) ℂ) (w : Fin 3 → ℂ) :
    0 ≤ (star w ⬝ᵥ (choiMap (Bᴴ * B) *ᵥ w)).re := by
  have hB : Bᴴ * B = ∑ r, vecMulVec (fun i => star (B r i)) (star fun i => star (B r i)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply]
  rw [hB, choiMap_sum, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  exact Finset.sum_nonneg fun r _ => (choi_positive _ w).1

/-! ### The state is PPT and entangled -/

/-- The witness pairing for a general kernel `r`. -/
noncomputable def Wr (r : Fin 3 × Fin 3 → Fin 3 × Fin 3 → ℂ) (Φ : M3 → M3) : ℂ :=
  ∑ i, ∑ j, ∑ a, ∑ b, r (j, b) (i, a) * Φ (E i j) a b

theorem Wr_sum {ι : Type*} (s : Finset ι) (p : ι → ℂ) (r : ι → Fin 3 × Fin 3 → Fin 3 × Fin 3 → ℂ)
    (Φ : M3 → M3) : Wr (fun x y => ∑ k ∈ s, p k * r k x y) Φ = ∑ k ∈ s, p k * Wr (r k) Φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Wr]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [← ih]
    simp only [Wr, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- On a product state `x ⊗ y`, the pairing is `y† Φ(x̄ x̄†) y`. -/
theorem Wr_product (x y : Fin 3 → ℂ) :
    Wr (fun s t => x s.1 * y s.2 * star (x t.1 * y t.2)) choiMap
      = star y ⬝ᵥ (choiMap (vecMulVec (star x) (star (star x))) *ᵥ y) := by
  simp only [Wr, choiMap, E, nxt, dotProduct, mulVec, vecMulVec_apply, Fin.sum_univ_three, Pi.star_apply]
  simp [star_mul']
  ring

/-- **ρ is PPT**: both `ρ` and its partial transpose are nonnegative sums of rank-one terms. -/
theorem rho_ppt : (∀ k, 0 ≤ rhoWt k) ∧ (∀ k, 0 ≤ ptWt k) ∧
    (∀ j a i b : Fin 3, rhoQ (j, b) (i, a) = ∑ k, ptWt k * ptVec k (j, a) * ptVec k (i, b)) :=
  ⟨by decide +kernel, by decide +kernel, rho_partialTranspose⟩

/-- **ρ is entangled**: it is not a nonnegative combination of product states `x ⊗ y`. Together with
`rho_ppt`, a PPT entangled state on `ℂ³ ⊗ ℂ³`. -/
theorem rho_entangled :
    ¬ ∃ (N : ℕ) (p : Fin N → ℝ) (x y : Fin N → Fin 3 → ℂ), (∀ k, 0 ≤ p k) ∧
      ∀ s t, (rhoQ s t : ℂ) = ∑ k, (p k : ℂ) * (x k s.1 * y k s.2 * star (x k t.1 * y k t.2)) := by
  rintro ⟨N, p, x, y, hp, h⟩
  have h1 : W choiMap = ∑ k, (p k : ℂ) * Wr (fun s t => x k s.1 * y k s.2 * star (x k t.1 * y k t.2)) choiMap := by
    rw [← Wr_sum]
    unfold W Wr
    simp only [h]
  have h2 : 0 ≤ (W choiMap).re := by
    rw [h1, Complex.re_sum]
    refine Finset.sum_nonneg fun k _ => ?_
    rw [Wr_product, Complex.re_ofReal_mul]
    exact mul_nonneg (hp k) (choi_positive _ _).1
  rw [W_choi] at h2
  norm_num at h2

/-! ## Part 5. The (3,3) type is dark -/

/-- **The (3,3) type is dark**: there is a positive map on `M₃(ℂ)`, taking every positive
semidefinite `Bᴴ B` to a positive semidefinite matrix, that is not decomposable. -/
theorem dark_33 : ∃ Φ : M3 → M3,
    (∀ (m : ℕ) (B : Matrix (Fin m) (Fin 3) ℂ) (w : Fin 3 → ℂ), 0 ≤ (star w ⬝ᵥ (Φ (Bᴴ * B) *ᵥ w)).re) ∧
    ¬ ∃ (m n : ℕ) (K : Fin m → M3) (L : Fin n → M3), ∀ X, Φ X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ :=
  ⟨choiMap, fun _ B w => choi_positive_psd B w, choi_not_decomposable⟩

end ChoiDark

#print axioms ChoiDark.choi_real
#print axioms ChoiDark.choi_positive
#print axioms ChoiDark.choi_positive_psd
#print axioms ChoiDark.rho_partialTranspose
#print axioms ChoiDark.W_choi
#print axioms ChoiDark.choi_not_decomposable
#print axioms ChoiDark.rho_ppt
#print axioms ChoiDark.rho_entangled
#print axioms ChoiDark.dark_33
