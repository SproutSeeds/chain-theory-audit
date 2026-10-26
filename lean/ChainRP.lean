/-
ChainRP.lean

Reflection positivity for mirror-symmetric networks of maximally entangled pairs.

A pure state on two mirrored halves `H ⊗ H̄`, with `H = ℂ^n` and the right half indexed in
mirror order, is written by its coefficient matrix `C`: `Ψ = ∑ C k l • e_k ⊗ e_l`. The reflection
acts on a left observable as `θ(F ⊗ 1) = 1 ⊗ F̄` (antilinear: the transpose identity
`(A ⊗ 1)|ω⟩ = (1 ⊗ Aᵀ)|ω⟩` of a maximally entangled pair, read from the far end). The
Osterwalder–Schrader form is `⟨Ψ, θ(F) F Ψ⟩ = ⟨Ψ, (F ⊗ F̄) Ψ⟩`.

Contents
  Part 1  The form, as a sum and as a trace.
  Part 2  Gram form gives reflection positivity: if `C = Bᴴ B` then the form is `∑ |(B F Bᴴ)_ab|²`.
  Part 3  Closure of Gram form under the operations of a mirror-symmetric chain web: a pair across
          the mirror (`C = 1`), a mirrored product state, a mirrored local map (`A` on the left, `Ā`
          on the right), tensoring two mirrored webs, superposition, and a distillation that
          straddles the mirror (a partial trace).
  Part 4  The operators behind Part 3: a mirrored local map and a straddling distillation act on
          the state vector exactly as Part 3 says they act on the coefficient matrix.
  Part 5  Where positivity fails: a twisted pair (the singlet) and a crossed pair of pairs.
  Part 6  The object of the alpha Letter under the exchange of its read links.

Mathematical status: the implication "positive semidefinite coefficient matrix ⇒ reflection
positive", and its preservation under partial traces, is classical (Lieb 1989, spin-reflection
positivity; Lieb–Schupp, Physica A, doi:10.1016/S0378-4371(99)00521-X). What is checked here is that formal statement and its
reading in the vocabulary of Chain Theory. Nothing here bears on the physics of Chain Theory.

Check: from a Lake project with Mathlib v4.26.0 built, `lake env lean ChainRP.lean`.
-/
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

open Matrix
open scoped Kronecker

namespace ChainRP

/-! # Part 1. The form -/

section Form
variable {n : Type} [Fintype n]

/-- The state vector of a coefficient matrix, indexed by (left index, mirrored right index). -/
def vec (C : Matrix n n ℂ) : n × n → ℂ := fun p => C p.1 p.2

/-- The two-sided operator `θ(F) F = F ⊗ F̄` of a left observable `F`. -/
def reflectedPair (F : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ := F ⊗ₖ F.map star

/-- The Osterwalder–Schrader form of the pure state `vec C` at the left observable `F`. -/
def rpForm (C F : Matrix n n ℂ) : ℂ := star (vec C) ⬝ᵥ (reflectedPair F *ᵥ vec C)

/-- The form written out: `∑ conj(C i j) C k l F i k conj(F j l)`. -/
theorem rpForm_eq_sum (C F : Matrix n n ℂ) :
    rpForm C F = ∑ i, ∑ j, ∑ k, ∑ l, star (C i j) * C k l * F i k * star (F j l) := by
  simp only [rpForm, vec, reflectedPair, dotProduct, mulVec, kroneckerMap_apply, map_apply,
    Pi.star_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

/-- The form as a trace: `tr (Cᴴ F C Fᴴ)`. -/
theorem rpForm_eq_trace (C F : Matrix n n ℂ) : rpForm C F = trace (Cᴴ * (F * C * Fᴴ)) := by
  rw [rpForm_eq_sum]
  simp only [trace, diag, mul_apply, conjTranspose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

end Form

/-! # Part 2. Gram form gives reflection positivity -/

section Gram
variable {n : Type} [Fintype n]

/-- `tr (X Xᴴ)` is the sum of the squared moduli of the entries of `X`. -/
theorem trace_mul_conjTranspose_self {m : Type} [Fintype m] (X : Matrix m n ℂ) :
    trace (X * Xᴴ) = ∑ a, ∑ b, (Complex.normSq (X a b) : ℂ) := by
  simp only [trace, diag, mul_apply, conjTranspose_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.mul_conj]
  rfl

/-- **Gram form gives reflection positivity.** If `C = Bᴴ B`, the form at every left observable
`F` is the squared Hilbert–Schmidt norm of `B F Bᴴ`. -/
theorem rpForm_of_gram {m : Type} [Fintype m] (B : Matrix m n ℂ) (F : Matrix n n ℂ) :
    rpForm (Bᴴ * B) F = ∑ a, ∑ b, (Complex.normSq ((B * F * Bᴴ) a b) : ℂ) := by
  rw [rpForm_eq_trace, ← trace_mul_conjTranspose_self]
  have hX : (B * F * Bᴴ)ᴴ = B * Fᴴ * Bᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [hX, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- `C` has Gram form, `C = Bᴴ B` for some `B`: in finite dimension, positive semidefiniteness. -/
def IsGram (C : Matrix n n ℂ) : Prop :=
  ∃ (m : Type) (_ : Fintype m) (B : Matrix m n ℂ), C = Bᴴ * B

/-- **Reflection positivity.** A state with a Gram-form coefficient matrix has a real,
nonnegative Osterwalder–Schrader form at every left observable. -/
theorem IsGram.rp {C : Matrix n n ℂ} (h : IsGram C) (F : Matrix n n ℂ) :
    0 ≤ (rpForm C F).re ∧ (rpForm C F).im = 0 := by
  obtain ⟨m, _, B, rfl⟩ := h
  rw [rpForm_of_gram]
  refine ⟨?_, ?_⟩
  · rw [Complex.re_sum]
    refine Finset.sum_nonneg fun a _ => ?_
    rw [Complex.re_sum]
    exact Finset.sum_nonneg fun b _ => by rw [Complex.ofReal_re]; exact Complex.normSq_nonneg _
  · rw [Complex.im_sum]
    exact Finset.sum_eq_zero fun a _ => by
      rw [Complex.im_sum]
      exact Finset.sum_eq_zero fun b _ => Complex.ofReal_im _

/-- **The flat double.** A maximally entangled pair straight across the mirror has coefficient
matrix `1` (up to the positive factor `1/√n`); its form is `∑ |F a b|²`, the Hilbert–Schmidt norm. -/
theorem rpForm_one [DecidableEq n] (F : Matrix n n ℂ) :
    rpForm (1 : Matrix n n ℂ) F = ∑ a, ∑ b, (Complex.normSq (F a b) : ℂ) := by
  have h := rpForm_of_gram (1 : Matrix n n ℂ) F
  simp only [conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h
  exact h

end Gram

/-! # Part 3. Closure of Gram form under the operations of a mirror-symmetric web -/

section Closure
variable {n : Type} [Fintype n]

/-- A maximally entangled pair, or a family of them, straight across the mirror: `C = 1`. -/
theorem isGram_one [DecidableEq n] : IsGram (1 : Matrix n n ℂ) :=
  ⟨n, inferInstance, 1, by simp⟩

omit [Fintype n] in
/-- A mirrored product state `φ ⊗ φ̄`: coefficient matrix `C k l = φ k · conj (φ l)`. -/
theorem isGram_mirrorProduct (φ : n → ℂ) : IsGram (Matrix.of fun k l => φ k * star (φ l)) := by
  refine ⟨Unit, inferInstance, Matrix.of fun _ l => star (φ l), ?_⟩
  ext k l
  simp [mul_apply, conjTranspose_apply]

/-- A mirrored local map: `A` on the left half and `Ā` on the right takes `C` to `A C Aᴴ`
(Part 4, `mirrorMap_vec`). Matchings `U ⊗ Ū` are the unitary case. -/
theorem IsGram.mirrorMap {n' : Type} [Fintype n'] {C : Matrix n n ℂ} (h : IsGram C)
    (A : Matrix n' n ℂ) : IsGram (A * C * Aᴴ) := by
  obtain ⟨m, _, B, rfl⟩ := h
  exact ⟨m, inferInstance, B * Aᴴ, by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]⟩

omit [Fintype n] in
/-- Two mirrored webs side by side: the coefficient matrix of the joint state is the Kronecker
product, with left and right indices grouped half by half. -/
theorem IsGram.kronecker {p : Type} [Fintype p] {C : Matrix n n ℂ} {D : Matrix p p ℂ}
    (hC : IsGram C) (hD : IsGram D) : IsGram (C ⊗ₖ D) := by
  obtain ⟨m, _, B, rfl⟩ := hC
  obtain ⟨m', _, B', rfl⟩ := hD
  exact ⟨m × m', inferInstance, B ⊗ₖ B', by rw [conjTranspose_kronecker, mul_kronecker_mul]⟩

omit [Fintype n] in
/-- A superposition of two Gram-form states (sum of coefficient matrices) has Gram form. -/
theorem IsGram.add {C D : Matrix n n ℂ} (hC : IsGram C) (hD : IsGram D) : IsGram (C + D) := by
  obtain ⟨m, _, B, rfl⟩ := hC
  obtain ⟨m', _, B', rfl⟩ := hD
  refine ⟨m ⊕ m', inferInstance, Matrix.of fun s l => Sum.elim (fun a => B a l) (fun a => B' a l) s, ?_⟩
  ext k l
  simp [mul_apply, conjTranspose_apply, Fintype.sum_sum_type]

/-- The partial trace over a qudit and its mirror image. -/
def ptrace {d : Type} [Fintype d] (C : Matrix (d × n) (d × n) ℂ) : Matrix n n ℂ :=
  fun l r => ∑ i, C (i, l) (i, r)

omit [Fintype n] in
/-- Partial trace over a mirrored qudit pair preserves Gram form. -/
theorem IsGram.ptrace {d : Type} [Fintype d] {C : Matrix (d × n) (d × n) ℂ} (h : IsGram C) :
    IsGram (ChainRP.ptrace C) := by
  obtain ⟨m, _, B, rfl⟩ := h
  refine ⟨m × d, inferInstance, Matrix.of fun q l => B q.1 (q.2, l), ?_⟩
  ext l r
  simp only [ChainRP.ptrace, mul_apply, conjTranspose_apply, of_apply, Fintype.sum_prod_type]
  rw [Finset.sum_comm]

/-- **A distillation that straddles the mirror.** Projecting a left qudit and its mirror image onto
their (unnormalized) maximally entangled pair leaves the coefficient matrix `1 ⊗ ptrace C`
(Part 4, `distill_vec`), which has Gram form. -/
theorem IsGram.distill {d : Type} [Fintype d] [DecidableEq d] {C : Matrix (d × n) (d × n) ℂ}
    (h : IsGram C) : IsGram ((1 : Matrix d d ℂ) ⊗ₖ ChainRP.ptrace C) :=
  isGram_one.kronecker h.ptrace

end Closure

/-! # Part 4. The operators behind Part 3 -/

section Operators
variable {n : Type} [Fintype n]

/-- A mirrored local map `A ⊗ Ā` acts on the state vector as `C ↦ A C Aᴴ`. -/
theorem mirrorMap_vec {n' : Type} [Fintype n'] (A : Matrix n' n ℂ) (C : Matrix n n ℂ) :
    (A ⊗ₖ A.map star) *ᵥ vec C = vec (A * C * Aᴴ) := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [mulVec, dotProduct, kroneckerMap_apply, map_apply, vec, mul_apply,
    conjTranspose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The (unnormalized) projection onto the maximally entangled pair of the first left qudit and
its mirror image, identity elsewhere: `|ω⟩⟨ω| ⊗ 1` in mirror order. -/
def distillOp (d : Type) [Fintype d] [DecidableEq d] (n : Type) [DecidableEq n] :
    Matrix ((d × n) × (d × n)) ((d × n) × (d × n)) ℂ :=
  fun x y => if x.1.1 = x.2.1 ∧ y.1.1 = y.2.1 ∧ x.1.2 = y.1.2 ∧ x.2.2 = y.2.2 then 1 else 0

/-- The straddling distillation acts on the state vector as `C ↦ 1 ⊗ ptrace C`. -/
theorem distill_vec {d : Type} [Fintype d] [DecidableEq d] [DecidableEq n]
    (C : Matrix (d × n) (d × n) ℂ) :
    distillOp d n *ᵥ vec C = vec ((1 : Matrix d d ℂ) ⊗ₖ ChainRP.ptrace C) := by
  funext x
  obtain ⟨⟨i, l⟩, ⟨i', r⟩⟩ := x
  simp only [mulVec, dotProduct, distillOp, vec, kroneckerMap_apply, one_apply, ChainRP.ptrace,
    Fintype.sum_prod_type]
  by_cases hii : i = i'
  · subst hii
    simp only [true_and, if_true, one_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_eq_single l (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    rw [Finset.sum_eq_single j (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    rw [Finset.sum_eq_single r (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  · simp [hii]

end Operators

/-! # Part 5. Where positivity fails -/

section Failures

/-- The singlet, a maximally entangled qubit pair twisted by `iσ_y` at one end:
coefficient matrix `!![0, 1; -1, 0]`. -/
def singlet : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- `σ_z` on the left qubit gives the form `-2`: the twisted pair is not reflection positive for
this reflection. (Composed with `σ_y` the reflection makes it positive; that is checked numerically
in the report, not here.) -/
theorem singlet_not_rp : rpForm singlet !![1, 0; 0, -1] = -2 := by
  rw [rpForm_eq_sum]
  simp [singlet, Fin.sum_univ_two]
  norm_num

/-- Two pairs crossed over the mirror: left qudit `a` paired with the mirror image of `b`, and `b`
with the mirror image of `a`. In mirror order the coefficient matrix is the swap. -/
def crossed : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0

/-- The left observable `|0⟩⟨0| ⊗ |1⟩⟨1| - |1⟩⟨1| ⊗ |0⟩⟨0|`, odd under the swap. -/
def oddObservable : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun x y => if x = y then (if x = (0, 1) then 1 else if x = (1, 0) then -1 else 0) else 0

/-- The crossed pairs are mirror-symmetric as a set of links, yet not reflection positive:
the odd observable gives the form `-2`. Positivity needs each pair straight across. -/
theorem crossed_not_rp : rpForm crossed oddObservable = -2 := by
  rw [rpForm_eq_sum]
  simp [crossed, oddObservable, Fintype.sum_prod_type, Fin.sum_univ_two]
  norm_num

end Failures

/-! # Part 6. The object of the alpha Letter

The object is a qutrit shared by three links to qubits. Its shared qutrit is carried as one copy per
link (`Q₁, Q₂, Q₃`); the read links are `Q₁q₁` and `Q₂q₂`, and `Q₃f` is unread. The exchange of the
two read links is a mirror: `Q₁ ↔ Q₂`, `q₁ ↔ q₂`, left half `Q₁ ⊗ q₁ = ℂ³ ⊗ ℂ²`. The unread link is
a tensor factor on neither half. -/

section AlphaObject

/-- The qutrit–qubit pair ket on its common support, unnormalized: coefficient one at the matched
directions `(i, i)`, `i < 2`. -/
def pairKet32 : Fin 3 × Fin 2 → ℂ := fun x => if (x.1 : ℕ) = (x.2 : ℕ) then 1 else 0

/-- Before the join, the left half holds the read link `Q₁q₁` and the right half its mirror image
`Q₂q₂`: a mirrored product state, reflection positive. -/
theorem alpha_object_before_join_rp (F : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    0 ≤ (rpForm (Matrix.of fun k l => pairKet32 k * star (pairKet32 l)) F).re ∧
    (rpForm (Matrix.of fun k l => pairKet32 k * star (pairKet32 l)) F).im = 0 :=
  (isGram_mirrorProduct pairKet32).rp F

/-- After the join, `Q₁Q₂` hold the qutrit pair and `q₁q₂` the qubit pair, both straight across the
mirror: coefficient matrix `1` on `ℂ³ ⊗ ℂ²`, the flat double. -/
theorem alpha_object_after_join_rp (F : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) :
    rpForm (1 : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) F
      = ∑ a, ∑ b, (Complex.normSq (F a b) : ℂ) :=
  rpForm_one F

end AlphaObject

end ChainRP

#print axioms ChainRP.IsGram.rp
#print axioms ChainRP.rpForm_of_gram
#print axioms ChainRP.IsGram.distill
#print axioms ChainRP.mirrorMap_vec
#print axioms ChainRP.distill_vec
#print axioms ChainRP.singlet_not_rp
#print axioms ChainRP.crossed_not_rp
#print axioms ChainRP.alpha_object_after_join_rp
