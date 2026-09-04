import Ols.Defs

/-!
# The linear projection: orthogonality and the exact OLS identity

* `E_score_eq_zero`: **(1)** `E[X e] = 0`, forced by the definition of `β₀`. Uses only
  linearity of `E` over finite sums — postulates (E1)–(E9) — and `Q Q⁻¹ = I`.
* `olsHat_sub_beta0`: **(6)** `β̂ₙ - β₀ = Q̂ₙ⁻¹ ḡₙ - 1{det Q̂ₙ = 0} β₀`, for every `n` and `ω`.
  Pure algebra.
-/

open Matrix Finset Simple

namespace Ols

variable {Ω : Type*} {K : Kernel Ω} {k : ℕ}

section Orthogonality

variable {Y : Ω → ℝ} {X : Ω → Fin k → ℝ}

lemma hasMoment_mul_X (hX : ∀ a, K.HasMoment (fun ω => X ω a) 2) (a b : Fin k) :
    K.HasMoment (fun ω => X ω a * X ω b) 1 :=
  K.hasMoment_mul _ _ (hX a) (hX b)

lemma hasMoment_X_mul_Y (hY : K.HasMoment Y 2) (hX : ∀ a, K.HasMoment (fun ω => X ω a) 2)
    (a : Fin k) : K.HasMoment (fun ω => X ω a * Y ω) 1 :=
  K.hasMoment_mul _ _ (hX a) hY

/-- `(X ⬝ b) X_a = ∑ c, b_c (X_a X_c)`. -/
lemma dotProduct_mul_eq_sum (b : Fin k → ℝ) (a : Fin k) :
    (fun ω => (X ω ⬝ᵥ b) * X ω a) = fun ω => ∑ c, b c * (X ω a * X ω c) := by
  funext ω
  simp only [dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

lemma hasMoment_dotProduct_mul (hX : ∀ a, K.HasMoment (fun ω => X ω a) 2) (b : Fin k → ℝ)
    (a : Fin k) : K.HasMoment (fun ω => (X ω ⬝ᵥ b) * X ω a) 1 := by
  rw [dotProduct_mul_eq_sum]
  exact K.hasMoment_sum univ _ 1 fun c _ => K.hasMoment_smul _ _ 1 (hasMoment_mul_X hX a c)

/-- `E[(X ⬝ b) X_a] = (Q b)_a`. -/
lemma E_dotProduct_mul (hX : ∀ a, K.HasMoment (fun ω => X ω a) 2) (b : Fin k → ℝ) (a : Fin k) :
    K.E (fun ω => (X ω ⬝ᵥ b) * X ω a) = (gram K X *ᵥ b) a := by
  rw [dotProduct_mul_eq_sum,
    K.E_sum univ _ fun c _ => K.hasMoment_smul _ _ 1 (hasMoment_mul_X hX a c)]
  simp only [gram, mulVec, dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [K.E_smul (b c) _ (hasMoment_mul_X hX a c), mul_comm]

/-- **(1) Orthogonality**: `E[e X_a] = 0` for every coordinate `a`. Uses only the definition
of `β₀` and `Q Q⁻¹ = I`, valid because `det Q > 0` by (A3). -/
theorem E_score_eq_zero (hY : K.HasMoment Y 2) (hX : ∀ a, K.HasMoment (fun ω => X ω a) 2)
    (hQ : (gram K X).PosDef) (a : Fin k) :
    K.E (fun ω => projError Y X (beta0 K Y X) ω * X ω a) = 0 := by
  have hdet : IsUnit (gram K X).det := isUnit_iff_ne_zero.mpr hQ.det_pos.ne'
  have h1 : (fun ω => projError Y X (beta0 K Y X) ω * X ω a) =
      fun ω => X ω a * Y ω - (X ω ⬝ᵥ beta0 K Y X) * X ω a := by
    funext ω
    simp only [projError]
    ring
  rw [h1, K.E_sub (hasMoment_X_mul_Y hY hX a) (hasMoment_dotProduct_mul hX _ a),
    E_dotProduct_mul hX]
  simp only [beta0, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec, crossMoment, sub_self]

end Orthogonality

section Identity

variable {Y : ℕ → Ω → ℝ} {X : ℕ → Ω → Fin k → ℝ}

/-- `m̂ₙ = Q̂ₙ b + ḡₙ(b)` for any coefficient `b`: substitute `Yᵢ = Xᵢ ⬝ b + eᵢ(b)`. -/
lemma sampleCross_eq (b : Fin k → ℝ) (n : ℕ) (ω : Ω) :
    sampleCross Y X n ω = sampleGram X n ω *ᵥ b + scoreAvg Y X b n ω := by
  simp only [sampleCross, sampleGram, scoreAvg]
  rw [smul_mulVec, sum_mulVec, ← smul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  funext a
  simp only [vecMulVec_mulVec, projError, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [op_smul_eq_mul]
  ring

open scoped Classical in
/-- **(6) The exact identity**: for every `n` and `ω`,
`β̂ₙ - β₀ = Q̂ₙ⁻¹ ḡₙ - 1{det Q̂ₙ not a unit} β₀`. -/
theorem olsHat_sub_beta0 (b : Fin k → ℝ) (n : ℕ) (ω : Ω) :
    olsHat Y X n ω - b =
      (sampleGram X n ω)⁻¹ *ᵥ scoreAvg Y X b n ω -
        (if IsUnit (sampleGram X n ω).det then 0 else b) := by
  simp only [olsHat, sampleCross_eq b, mulVec_add, mulVec_mulVec]
  split_ifs with h
  · rw [nonsing_inv_mul _ h, one_mulVec]; abel
  · rw [nonsing_inv_apply_not_isUnit _ h]
    simp

end Identity

end Ols
