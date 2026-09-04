import Ols.GramInverse

/-!
# Theorem 1: asymptotic normality of OLS for the linear projection coefficient

Under `Setting` — (A1)–(A4) — `√n (β̂ₙ - β₀) →d N(0, Q⁻¹ Ω Q⁻¹)`. Neither
linearity of `E[Y ∣ X]` nor any distributional assumption on the projection error is used.

The proof is the paper's: the scores `Xᵢ eᵢ` are iid (T0), centered by (1), so the CLT (T2)
applies to `√n ḡₙ`; the Gram inverse converges by (T1)+(T3); the exact identity (6) plus
Slutsky (T4) finish, and `Q⁻¹ᵀ = Q⁻¹` since `Q` is symmetric.
-/

open Matrix Finset Simple

namespace Ols

variable {Ω : Type*} {K : Kernel Ω} {k : ℕ} {Y : ℕ → Ω → ℝ} {X : ℕ → Ω → Fin k → ℝ}

/-- The score `Xᵢ eᵢ` at the true coefficient. -/
noncomputable def score (K : Kernel Ω) (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (i : ℕ)
    (ω : Ω) : Fin k → ℝ :=
  projError (Y i) (X i) (beta0 K (Y 0) (X 0)) ω • X i ω

section Score

/-- The scores form an iid sequence, by (T0). -/
lemma iid_score (h : Setting K Y X) : K.IID (score K Y X) :=
  K.iid_comp _ (fun p : ℝ × (Fin k → ℝ) => (p.1 - p.2 ⬝ᵥ beta0 K (Y 0) (X 0)) • p.2) h.iid

lemma hasMoment_score_coord (h : Setting K Y X) (a : Fin k) :
    K.HasMoment (fun ω => score K Y X 0 ω a) 2 := by
  simpa only [score, Pi.smul_apply, smul_eq_mul] using h.mom_score a

lemma E_score_coord (h : Setting K Y X) (a : Fin k) : K.E (fun ω => score K Y X 0 ω a) = 0 := by
  simp only [score, Pi.smul_apply, smul_eq_mul]
  exact E_score_eq_zero h.mom_Y h.mom_X h.posDef a

lemma secondMoment_score :
    K.secondMoment (score K Y X 0) = scoreVar K (Y 0) (X 0) (beta0 K (Y 0) (X 0)) := by
  funext a b
  simp [Kernel.secondMoment, scoreVar, score]

lemma gram_transpose (X : Ω → Fin k → ℝ) : (gram K X)ᵀ = gram K X := by
  funext a b
  simp [gram, transpose_apply, mul_comm]

/-- `√n ḡₙ` is the CLT's normalized sum. -/
lemma sqrt_smul_scoreAvg (n : ℕ) (ω : Ω) :
    Real.sqrt n • scoreAvg Y X (beta0 K (Y 0) (X 0)) n ω = normSum (score K Y X) n ω := by
  simp only [normSum, scoreAvg, score, smul_smul]
  congr 1
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  · have hpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    have : ((n : ℝ))⁻¹ = (Real.sqrt n * Real.sqrt n)⁻¹ := by rw [Real.mul_self_sqrt hpos.le]
    rw [this, mul_inv, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]

end Score

section Main

open scoped Classical in
/-- **(6)** rescaled: `√n (β̂ₙ - β₀) = Q̂ₙ⁻¹ (√n ḡₙ) + (-√n · 1{det Q̂ₙ = 0} β₀)`. -/
lemma normError_eq (n : ℕ) (ω : Ω) :
    Real.sqrt n • (olsHat Y X n ω - beta0 K (Y 0) (X 0)) =
      (sampleGram X n ω)⁻¹ *ᵥ normSum (score K Y X) n ω +
        -(Real.sqrt n • (if IsUnit (sampleGram X n ω).det then (0 : Fin k → ℝ)
          else beta0 K (Y 0) (X 0))) := by
  rw [olsHat_sub_beta0 (beta0 K (Y 0) (X 0)) n ω, smul_sub, ← mulVec_smul,
    sqrt_smul_scoreAvg, sub_eq_add_neg]

/-- **Theorem 1 (Asymptotic normality of OLS).** Under (A1)–(A4),
`√n (β̂ₙ - β₀) →d N(0, Q⁻¹ Ω Q⁻¹)`. -/
theorem ols_asymptotic_normality (h : Setting K Y X) :
    K.TendstoInDist (fun (n : ℕ) ω => Real.sqrt n • (olsHat Y X n ω - beta0 K (Y 0) (X 0)))
      0 (asympVar K (Y 0) (X 0)) := by
  classical
  set β₀ := beta0 K (Y 0) (X 0) with hβ₀
  have hclt := K.clt' (score K Y X) (iid_score h) (hasMoment_score_coord h) (E_score_coord h)
  rw [secondMoment_score] at hclt
  have hslut := K.slutsky (normSum (score K Y X)) _ (fun n ω => (sampleGram X n ω)⁻¹)
    (gram K (X 0))⁻¹ _ hclt (tendstoInProb_sampleGram_inv h) (tendstoInProb_remainder h β₀)
  have e : (fun (n : ℕ) ω => Real.sqrt n • (olsHat Y X n ω - β₀)) =
      fun n ω => (sampleGram X n ω)⁻¹ *ᵥ normSum (score K Y X) n ω +
        -(Real.sqrt n • (if IsUnit (sampleGram X n ω).det then (0 : Fin k → ℝ) else β₀)) := by
    funext n ω
    exact normError_eq n ω
  rw [e]
  convert hslut using 2
  simp only [asympVar, transpose_nonsing_inv, gram_transpose]

end Main

end Ols
