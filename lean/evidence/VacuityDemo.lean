/-
VacuityDemo.lean (scratch, not part of the repository's checked files).

The definitions below are copied verbatim from lean/ChoiDark.lean at commit eb2abdb (public 3b95151).
With them, no type is readable, so `readable_imp_le_six` holds vacuously. Two independent defects:
(a) `Readable` ranges over all functions, so a nonlinear map that vanishes on positive matrices counts
    as positive but cannot be decomposable;
(b) `IsPositive` only asks for a nonnegative real part, so the linear map X ↦ (1 + i) X counts as
    positive although it does not preserve Hermiticity.
-/
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic

open Matrix

namespace VacuityDemo

def IsPositive {n m : ℕ} (Φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ (r : ℕ) (B : Matrix (Fin r) (Fin n) ℂ) (w : Fin m → ℂ), 0 ≤ (star w ⬝ᵥ (Φ (Bᴴ * B) *ᵥ w)).re

def IsDecomposable {n m : ℕ} (Φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ (p q : ℕ) (K : Fin p → Matrix (Fin m) (Fin n) ℂ) (L : Fin q → Matrix (Fin m) (Fin n) ℂ),
    ∀ X, Φ X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ

def Readable (d₁ d₂ : ℕ) : Prop :=
  (∀ Φ : Matrix (Fin d₁) (Fin d₁) ℂ → Matrix (Fin d₂) (Fin d₂) ℂ, IsPositive Φ → IsDecomposable Φ) ∧
  (∀ Ψ : Matrix (Fin d₂) (Fin d₂) ℂ → Matrix (Fin d₁) (Fin d₁) ℂ, IsPositive Ψ → IsDecomposable Ψ)

/-- Defect (a): a nonlinear "positive" map. -/
noncomputable def junk (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  if X = -1 then 1 else 0

theorem gram_ne_neg_one {r : ℕ} (B : Matrix (Fin r) (Fin 2) ℂ) : Bᴴ * B ≠ -1 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have hre : 0 ≤ ((Bᴴ * B) 0 0).re := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.re_sum]
    exact Finset.sum_nonneg fun k _ => by
      rw [show star (B k 0) * B k 0 = ((Complex.normSq (B k 0) : ℝ) : ℂ) by
        rw [Complex.normSq_eq_conj_mul_self]; rfl]
      simp [Complex.normSq_nonneg]
  rw [h00] at hre
  simp at hre
  linarith

theorem junk_positive : IsPositive junk := by
  intro r B w
  simp [junk, gram_ne_neg_one B]

theorem junk_not_decomposable : ¬ IsDecomposable junk := by
  rintro ⟨p, q, K, L, h⟩
  have h1 := h 1
  have hm := h (-1)
  have hne : (1 : Matrix (Fin 2) (Fin 2) ℂ) ≠ -1 := by
    intro e
    have := congrFun (congrFun e 0) 0
    norm_num at this
  simp only [junk, hne, if_false, if_true] at h1 hm
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.transpose_neg, Matrix.transpose_one,
    Finset.sum_neg_distrib, Matrix.mul_one] at hm h1
  rw [← neg_add, ← h1] at hm
  have := congrFun (congrFun hm 0) 0
  norm_num at this

/-- Defect (b): a linear map that is "positive" in the real-part sense only. -/
def twist (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (1 + Complex.I) • X

theorem twist_positive : IsPositive twist := by
  intro r B w
  have hq : star w ⬝ᵥ ((Bᴴ * B) *ᵥ w) = ((star (B *ᵥ w) ⬝ᵥ (B *ᵥ w)).re : ℂ) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    apply Complex.ext
    · simp
    · simp only [Complex.ofReal_im]
      simp only [dotProduct, Pi.star_apply, Complex.im_sum]
      exact Finset.sum_eq_zero fun i _ => by simp [Complex.mul_im]; ring
  have hnn : 0 ≤ (star (B *ᵥ w) ⬝ᵥ (B *ᵥ w)).re := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum]
    exact Finset.sum_nonneg fun i _ => by simp [Complex.mul_re]; nlinarith [sq_nonneg ((B *ᵥ w) i).re, sq_nonneg ((B *ᵥ w) i).im]
  simp only [twist, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hq]
  simpa [Complex.mul_re] using hnn

theorem twist_not_decomposable : ¬ IsDecomposable twist := by
  rintro ⟨p, q, K, L, h⟩
  have h1 := congrFun (congrFun (h 1) 0) 0
  have him := congrArg Complex.im h1
  simp only [twist, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
    Matrix.transpose_one, Matrix.add_apply, Matrix.sum_apply, Complex.add_im, Complex.im_sum] at him
  have hK : ∀ k, ((K k * (K k)ᴴ) 0 0).im = 0 := fun k => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.im_sum]
    exact Finset.sum_eq_zero fun j _ => by simp [Complex.mul_im]; ring
  have hL : ∀ l, ((L l * (L l)ᴴ) 0 0).im = 0 := fun l => by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.im_sum]
    exact Finset.sum_eq_zero fun j _ => by simp [Complex.mul_im]; ring
  simp only [hK, hL, Finset.sum_const_zero, add_zero] at him
  norm_num at him

/-- **With the published definitions, the (2,2) type is not readable**, so the readable direction of
the read cap is false as stated and the dark direction holds vacuously. -/
theorem not_readable_22 : ¬ Readable 2 2 := fun h => junk_not_decomposable (h.1 junk junk_positive)

theorem not_readable_22' : ¬ Readable 2 2 := fun h => twist_not_decomposable (h.1 twist twist_positive)

end VacuityDemo

#print axioms VacuityDemo.not_readable_22
#print axioms VacuityDemo.not_readable_22'
