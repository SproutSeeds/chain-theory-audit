
/-! ## Part 7. The (2,4) type is dark

A positive map `Φ₂₄ : M₂(ℂ) → M₄(ℂ)` with integer coefficients. Positivity is certified by a
sum-of-squares identity with the multiplier `‖v‖²` (`phi24_certificate`). Non-decomposability is shown
by the PPT state of P. Horodecki's 2 ⊗ 4 family at `b = 3/5`, on which the witness value is `-1`. The map
and its certificate were found by semidefinite programming and rationalized exactly; everything below
is checked by the kernel. -/

@@GENERATED@@

theorem phi24_quad (v : Fin 2 → ℂ) (w : Fin 4 → ℂ) :
    star w ⬝ᵥ (phi24 (vecMulVec v (star v)) *ᵥ w) = @@INNER@@ := by
  simp only [dotProduct, mulVec, phi24, vecMulVec_apply, Fin.sum_univ_four, Pi.star_apply]
  simp
  ring

/-- `Φ₂₄` is positive on rank-one inputs. -/
theorem phi24_positive (v : Fin 2 → ℂ) (w : Fin 4 → ℂ) :
    0 ≤ (star w ⬝ᵥ (phi24 (vecMulVec v (star v)) *ᵥ w)).re := by
  have hc := phi24_certificate v w
  rw [← phi24_quad] at hc
  have h0 : v 0 * star (v 0) = (Complex.normSq (v 0) : ℂ) := Complex.mul_conj (v 0)
  have h1 : v 1 * star (v 1) = (Complex.normSq (v 1) : ℂ) := Complex.mul_conj (v 1)
  have hR : 0 ≤ (((Complex.normSq (v 0) + Complex.normSq (v 1) : ℝ) : ℂ)
      * (star w ⬝ᵥ (phi24 (vecMulVec v (star v)) *ᵥ w))).re := by
    rw [Complex.ofReal_add, ← h0, ← h1, hc]
    simp only [Complex.add_re]
    repeat' (first | (apply re_wsq_nonneg; norm_num) | apply add_nonneg)
  rw [Complex.re_ofReal_mul] at hR
  rcases (add_nonneg (Complex.normSq_nonneg (v 0)) (Complex.normSq_nonneg (v 1))).lt_or_eq with hpos | hzero
  · exact (mul_nonneg_iff_of_pos_left hpos).1 hR
  · have hv0 : v 0 = 0 := by
      have := Complex.normSq_nonneg (v 1)
      exact Complex.normSq_eq_zero.1 (by linarith [Complex.normSq_nonneg (v 0)])
    have hv1 : v 1 = 0 := by
      exact Complex.normSq_eq_zero.1 (by linarith [Complex.normSq_nonneg (v 0), Complex.normSq_nonneg (v 1)])
    rw [phi24_quad, hv0, hv1]
    simp

theorem phi24_sum {ι : Type*} (s : Finset ι) (X : ι → Matrix (Fin 2) (Fin 2) ℂ) :
    phi24 (∑ r ∈ s, X r) = ∑ r ∈ s, phi24 (X r) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [phi24, Matrix.sum_apply, Finset.mul_sum, Finset.sum_add_distrib]

/-- `Φ₂₄` takes every positive semidefinite matrix `Bᴴ B` to a positive semidefinite one. -/
theorem phi24_positive_psd {m : ℕ} (B : Matrix (Fin m) (Fin 2) ℂ) (w : Fin 4 → ℂ) :
    0 ≤ (star w ⬝ᵥ (phi24 (Bᴴ * B) *ᵥ w)).re := by
  have hB : Bᴴ * B = ∑ r, vecMulVec (fun i => star (B r i)) (star fun i => star (B r i)) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply, vecMulVec_apply]
  rw [hB, phi24_sum, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  exact Finset.sum_nonneg fun r _ => phi24_positive _ w

/-! ### The witness state and non-decomposability -/

def ix (a : Fin 2) (k : Fin 4) : Fin 8 := ⟨4 * a.val + k.val, by omega⟩

/-- The witness state `ρ((a,k),(b,l))`, a nonnegative sum of rational rank-one terms. -/
def rho24 (a : Fin 2) (k : Fin 4) (b : Fin 2) (l : Fin 4) : ℚ :=
  ∑ j, rho24Wt j * rho24Vec j (ix a k) * rho24Vec j (ix b l)

theorem rho24_weights_nonneg : (∀ j, 0 ≤ rho24Wt j) ∧ (∀ j, 0 ≤ pt24Wt j) := by decide +kernel

theorem rho24_trace : ∑ a, ∑ k, rho24 a k a k = 1 := by decide +kernel

/-- The partial transpose of `ρ` (on the second factor) is the nonnegative sum `pt24`. -/
theorem rho24_pt : ∀ a k b l, rho24 b l a k = ∑ j, pt24Wt j * pt24Vec j (ix b k) * pt24Vec j (ix a l) := by
  decide +kernel

theorem rho24_witness_value :
    ∑ a, ∑ k, ∑ b, ∑ l, rho24 b l a k * W24 (ix a k) (ix b l) = -1 := by decide +kernel

def E2 (a b : Fin 2) : Matrix (Fin 2) (Fin 2) ℂ := fun r c => if r = a ∧ c = b then 1 else 0

/-- The witness pairing `tr(ρ C_Φ)` of a map `M₂ → M₄`. -/
noncomputable def W2 (Φ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  ∑ a, ∑ k, ∑ b, ∑ l, (rho24 b l a k : ℂ) * Φ (E2 a b) k l

theorem W2_add (Φ Ψ : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 4) (Fin 4) ℂ) :
    W2 (fun X => Φ X + Ψ X) = W2 Φ + W2 Ψ := by
  simp only [W2, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem W2_sum {ι : Type*} (s : Finset ι) (F : ι → Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 4) (Fin 4) ℂ) :
    W2 (fun X => ∑ k ∈ s, F k X) = ∑ k ∈ s, W2 (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [W2]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [W2_add (F a) (fun X => ∑ k ∈ s, F k X), ih]

theorem phi24_E (a b : Fin 2) (k l : Fin 4) : phi24 (E2 a b) k l = (W24 (ix a k) (ix b l) : ℂ) := by
  fin_cases a <;> fin_cases b <;> fin_cases k <;> fin_cases l <;>
    simp [phi24, E2, W24, ix]

/-- **The witness is negative on `Φ₂₄`**: `tr(ρ C_Φ) = -1`. -/
theorem W2_phi24 : W2 phi24 = -1 := by
  have h := congrArg (fun q : ℚ => (q : ℂ)) rho24_witness_value
  push_cast at h
  simpa [W2, phi24_E] using h

theorem kEK24 (K : Matrix (Fin 4) (Fin 2) ℂ) (a b : Fin 2) (k l : Fin 4) :
    (K * E2 a b * Kᴴ) k l = K k a * star (K l b) := by
  simp [Matrix.mul_apply, E2, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> simp

theorem LEtL24 (L : Matrix (Fin 4) (Fin 2) ℂ) (a b : Fin 2) (k l : Fin 4) :
    (L * (E2 a b)ᵀ * Lᴴ) k l = L k b * star (L l a) := by
  simp [Matrix.mul_apply, E2, Matrix.conjTranspose_apply, Matrix.transpose_apply, Fin.sum_univ_two]
  fin_cases a <;> fin_cases b <;> simp

theorem star_ratC (q : ℚ) : star (q : ℂ) = q := by
  rw [show (q : ℂ) = ((q : ℝ) : ℂ) by norm_cast]
  exact Complex.conj_ofReal _

/-- On a completely positive part, the witness is a nonnegative sum of squares. -/
theorem W2_kraus (K : Matrix (Fin 4) (Fin 2) ℂ) :
    W2 (fun X => K * X * Kᴴ) = ∑ j, (rho24Wt j : ℂ) *
      ((∑ a, ∑ k, (rho24Vec j (ix a k) : ℂ) * K k a) * star (∑ a, ∑ k, (rho24Vec j (ix a k) : ℂ) * K k a)) := by
  simp only [W2, kEK24, rho24, Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_five,
    star_add, star_mul', star_ratC]
  push_cast
  ring

/-- On a part composed with the transpose, the witness is again a nonnegative sum of squares, from the
rank-one terms of the partial transpose. -/
theorem W2_transpose (L : Matrix (Fin 4) (Fin 2) ℂ) :
    W2 (fun X => L * Xᵀ * Lᴴ) = ∑ j, (pt24Wt j : ℂ) *
      ((∑ b, ∑ k, (pt24Vec j (ix b k) : ℂ) * L k b) * star (∑ b, ∑ k, (pt24Vec j (ix b k) : ℂ) * L k b)) := by
  simp only [W2, LEtL24, rho24_pt, Fin.sum_univ_two, Fin.sum_univ_four, Fin.sum_univ_five,
    star_add, star_mul', star_ratC]
  push_cast
  ring

theorem re_wsum_nonneg {n : ℕ} (c : Fin n → ℚ) (hc : ∀ j, 0 ≤ c j) (z : Fin n → ℂ) :
    0 ≤ (∑ j, (c j : ℂ) * (z j * star (z j))).re := by
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => re_wsq_nonneg (c j) (hc j) (z j)

/-- **`Φ₂₄` is not decomposable.** -/
theorem phi24_not_decomposable :
    ¬ ∃ (m n : ℕ) (K : Fin m → Matrix (Fin 4) (Fin 2) ℂ) (L : Fin n → Matrix (Fin 4) (Fin 2) ℂ),
      ∀ X, phi24 X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ := by
  rintro ⟨m, n, K, L, h⟩
  have hfun : phi24 = fun X => (fun X => ∑ k, K k * X * (K k)ᴴ) X
      + (fun X => ∑ l, L l * Xᵀ * (L l)ᴴ) X := funext h
  have h1 : W2 phi24 = ∑ k, W2 (fun X => K k * X * (K k)ᴴ) + ∑ l, W2 (fun X => L l * Xᵀ * (L l)ᴴ) := by
    rw [hfun, W2_add, W2_sum, W2_sum]
  have h2 : 0 ≤ (W2 phi24).re := by
    rw [h1, Complex.add_re, Complex.re_sum, Complex.re_sum]
    refine add_nonneg (Finset.sum_nonneg fun k _ => ?_) (Finset.sum_nonneg fun l _ => ?_)
    · rw [W2_kraus]; exact re_wsum_nonneg _ rho24_weights_nonneg.1 _
    · rw [W2_transpose]; exact re_wsum_nonneg _ rho24_weights_nonneg.2 _
  rw [W2_phi24] at h2
  norm_num at h2

/-! ## Part 8. Every type with `d₁ d₂ ≥ 8` is dark: the dark direction of the read cap -/

/-- The inclusion of `ℂⁿ` into `ℂᵈ` as the first `n` coordinates. -/
def inclN (n d : ℕ) : Matrix (Fin d) (Fin n) ℂ := fun i j => if (i : ℕ) = (j : ℕ) then 1 else 0

theorem inclN_conjTranspose_mul {n d : ℕ} (h : n ≤ d) : (inclN n d)ᴴ * inclN n d = 1 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, inclN, Matrix.one_apply]
  rw [Finset.sum_eq_single ⟨a, by omega⟩]
  · by_cases hab : a = b
    · subst hab; simp
    · have : (a : ℕ) ≠ (b : ℕ) := fun h' => hab (Fin.ext h')
      simp [hab, this]
  · intro i _ hi
    have : (i : ℕ) ≠ (a : ℕ) := fun h' => hi (Fin.ext h')
    simp [this]
  · simp

/-- The extension of `Φ₂₄` to `M₂ → M_d`. -/
noncomputable def extend24 (d : ℕ) (X : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  inclN 4 d * phi24 X * (inclN 4 d)ᴴ

theorem extend24_positive (d : ℕ) {m : ℕ} (B : Matrix (Fin m) (Fin 2) ℂ) (w : Fin d → ℂ) :
    0 ≤ (star w ⬝ᵥ (extend24 d (Bᴴ * B) *ᵥ w)).re := by
  unfold extend24
  rw [quad_conj]
  exact phi24_positive_psd _ _

theorem extend24_not_decomposable {d : ℕ} (h : 4 ≤ d) :
    ¬ ∃ (m n : ℕ) (K : Fin m → Matrix (Fin d) (Fin 2) ℂ) (L : Fin n → Matrix (Fin d) (Fin 2) ℂ),
      ∀ X, extend24 d X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ := by
  rintro ⟨m, n, K, L, hK⟩
  apply phi24_not_decomposable
  refine ⟨m, n, fun k => (inclN 4 d)ᴴ * K k, fun l => (inclN 4 d)ᴴ * L l, fun X => ?_⟩
  have hc : phi24 X = (inclN 4 d)ᴴ * extend24 d X * inclN 4 d := by
    unfold extend24
    rw [show (inclN 4 d)ᴴ * (inclN 4 d * phi24 X * (inclN 4 d)ᴴ) * inclN 4 d
        = ((inclN 4 d)ᴴ * inclN 4 d) * phi24 X * ((inclN 4 d)ᴴ * inclN 4 d) by simp only [Matrix.mul_assoc],
      inclN_conjTranspose_mul h, Matrix.one_mul, Matrix.mul_one]
  rw [hc, hK, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.sum_mul]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

/-- A map `M_n(ℂ) → M_m(ℂ)` is positive: it takes every positive semidefinite `Bᴴ B` to a positive
semidefinite matrix. -/
def IsPositive {n m : ℕ} (Φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ (r : ℕ) (B : Matrix (Fin r) (Fin n) ℂ) (w : Fin m → ℂ), 0 ≤ (star w ⬝ᵥ (Φ (Bᴴ * B) *ᵥ w)).re

/-- A map is decomposable: a completely positive map plus a completely positive map after the
transpose, both in Kraus form. -/
def IsDecomposable {n m : ℕ} (Φ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∃ (p q : ℕ) (K : Fin p → Matrix (Fin m) (Fin n) ℂ) (L : Fin q → Matrix (Fin m) (Fin n) ℂ),
    ∀ X, Φ X = ∑ k, K k * X * (K k)ᴴ + ∑ l, L l * Xᵀ * (L l)ᴴ

/-- The Letter's readability of a type `(d₁, d₂)`: every positive map between the operator algebras of
its two ends, in either direction, is decomposable. -/
def Readable (d₁ d₂ : ℕ) : Prop :=
  (∀ Φ : Matrix (Fin d₁) (Fin d₁) ℂ → Matrix (Fin d₂) (Fin d₂) ℂ, IsPositive Φ → IsDecomposable Φ) ∧
  (∀ Ψ : Matrix (Fin d₂) (Fin d₂) ℂ → Matrix (Fin d₁) (Fin d₁) ℂ, IsPositive Ψ → IsDecomposable Ψ)

/-- **The dark direction of the read cap.** A readable type with both ends of dimension at least two has
`d₁ d₂ ≤ 6`. Equivalently, every type with `d₁ d₂ ≥ 8` (no product of two integers `≥ 2` is 7) has a
positive, non-decomposable map between its ends. -/
theorem readable_imp_le_six {d₁ d₂ : ℕ} (h₁ : 2 ≤ d₁) (h₂ : 2 ≤ d₂) (hr : Readable d₁ d₂) :
    d₁ * d₂ ≤ 6 := by
  by_contra hlt
  push_neg at hlt
  by_cases h33 : 3 ≤ d₁ ∧ 3 ≤ d₂
  · obtain ⟨Φ, hpos, hnd⟩ := dark_of_three_le h33.1 h33.2
    exact hnd (hr.1 Φ fun r B w => hpos r B w)
  · rcases Nat.lt_or_ge d₁ 3 with hd₁ | hd₁
    · obtain rfl : d₁ = 2 := by omega
      have h4 : 4 ≤ d₂ := by omega
      exact extend24_not_decomposable h4
        (hr.1 (extend24 d₂) fun r B w => extend24_positive d₂ B w)
    · obtain rfl : d₂ = 2 := by omega
      have h4 : 4 ≤ d₁ := by omega
      exact extend24_not_decomposable h4
        (hr.2 (extend24 d₁) fun r B w => extend24_positive d₁ B w)
