import Ols.Consistency

/-!
# Theorem 3: asymptotic normality of the t-statistic

Postulates used, beyond Theorems 1–2: (T3), (T4) in its `1 × k` form, (T6).

The paper's proof, step by step: `V_jj > 0` from (A6); a continuous surrogate for
`(z, W) ↦ z_j / √W_jj` that agrees with `t_{n,j}` where `V̂_{n,jj} ≥ V_jj / 2`, an event
whose complement vanishes; Slutsky for the linear functional `aₙ ⬝ (√n δₙ)`; and the
variance `a₀ᵀ V a₀ = 1`.
-/

open Matrix Finset Simple

namespace Ols

variable {Ω : Type*} {K : Kernel Ω} {k : ℕ} {Y : ℕ → Ω → ℝ} {X : ℕ → Ω → Fin k → ℝ}

/-- (A1)–(A6). -/
structure Setting₆ (K : Kernel Ω) (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) : Prop
    extends Setting₅ K Y X where
  /-- (A6) `Ω = E[e² X Xᵀ]` positive definite. -/
  posDefOmega : (scoreVar K (Y 0) (X 0) (beta0 K (Y 0) (X 0))).PosDef

/-- (D6) `t_{n,j} = √n δ_{n,j} / √V̂_{n,jj}`, with `x / 0 = 0`. -/
noncomputable def tStat (K : Kernel Ω) (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (n : ℕ)
    (j : Fin k) (ω : Ω) : ℝ :=
  Real.sqrt n * delta K Y X n ω j / Real.sqrt (vHat Y X n ω j j)

/-! ### Step 1: `V_jj > 0` -/

lemma mul_mul_transpose_apply (A S : Matrix (Fin k) (Fin k) ℝ) (i : Fin k) :
    (A * S * Aᵀ) i i = A i ⬝ᵥ S *ᵥ A i := by
  simp only [Matrix.mul_apply, dotProduct, mulVec, transpose_apply, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- `V_jj = wᵀ Ω w` with `w` the `j`-th row of `Q⁻¹` (`Q⁻¹` is symmetric). -/
lemma asympVar_apply_eq (j : Fin k) :
    asympVar K (Y 0) (X 0) j j =
      (gram K (X 0))⁻¹ j ⬝ᵥ scoreVar K (Y 0) (X 0) (beta0 K (Y 0) (X 0)) *ᵥ (gram K (X 0))⁻¹ j := by
  have e : asympVar K (Y 0) (X 0) =
      (gram K (X 0))⁻¹ * scoreVar K (Y 0) (X 0) (beta0 K (Y 0) (X 0)) * ((gram K (X 0))⁻¹)ᵀ := by
    rw [transpose_nonsing_inv, gram_transpose]
    rfl
  rw [e, mul_mul_transpose_apply]

/-- The rows of `Q⁻¹` are nonzero, since `Q⁻¹ Q = I`. -/
lemma inv_gram_row_ne_zero (h : Setting K Y X) (j : Fin k) : (gram K (X 0))⁻¹ j ≠ 0 := by
  intro hrow
  have h1 : ((gram K (X 0))⁻¹ * gram K (X 0)) j j = 1 := by
    rw [nonsing_inv_mul _ (isUnit_det_gram h), one_apply_eq]
  rw [Matrix.mul_apply] at h1
  simp [hrow] at h1

/-- **Step 1.** `V_jj > 0` under (A6). -/
theorem asympVar_diag_pos (h : Setting₆ K Y X) (j : Fin k) : 0 < asympVar K (Y 0) (X 0) j j := by
  rw [asympVar_apply_eq]
  have := h.posDefOmega.dotProduct_mulVec_pos (inv_gram_row_ne_zero h.toSetting₅.toSetting j)
  simpa using this

/-! ### Steps 2–3: the surrogate, Slutsky, and the limit variance -/

/-- **Theorem 3 (Asymptotic normality of the t-statistic).** Under (A1)–(A6), for every
coordinate `j`, `t_{n,j} →d N(0, 1)`. -/
theorem tStat_asymptotic_normality (h : Setting₆ K Y X) (j : Fin k) :
    K.TendstoInDistReal (fun n ω => tStat K Y X n j ω) 1 := by
  classical
  set V := asympVar K (Y 0) (X 0) with hV
  have hVpos : 0 < V j j := asympVar_diag_pos h j
  set c := V j j / 2 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  have hcV : c < V j j := by rw [hc]; linarith
  -- `V̂ₙ →p V`, and its `(j, j)` entry.
  have hVhat := vHat_tendstoInProb h.toSetting₅
  have hjj : K.TendstoInProb (fun n ω => vHat Y X n ω j j) (V j j) :=
    K.cmt (fun n ω => vHat Y X n ω) V (fun W : Matrix (Fin k) (Fin k) ℝ => W j j)
      (continuous_id.matrix_elem j j).continuousAt hVhat
  -- The coefficient of the surrogate: `a(W) = ι_j / √(max(W_jj, c))`, continuous.
  set g : Matrix (Fin k) (Fin k) ℝ → Fin k → ℝ :=
    fun W => (Real.sqrt (max (W j j) c))⁻¹ • Pi.single j (1 : ℝ) with hg
  have hinv : Continuous fun W : Matrix (Fin k) (Fin k) ℝ => (Real.sqrt (max (W j j) c))⁻¹ := by
    refine Continuous.inv₀ (f := fun W : Matrix (Fin k) (Fin k) ℝ => Real.sqrt (max (W j j) c))
      ((continuous_id.matrix_elem j j).max continuous_const).sqrt ?_
    intro W
    exact (Real.sqrt_pos.mpr (lt_of_lt_of_le hcpos (le_max_right _ _))).ne'
  have hgcont : Continuous g := by
    rw [hg]
    exact hinv.smul continuous_const
  have ha : K.TendstoInProb (fun n ω => g (vHat Y X n ω)) (g V) :=
    K.cmt (fun n ω => vHat Y X n ω) V g hgcont.continuousAt hVhat
  have hgV : g V = (Real.sqrt (V j j))⁻¹ • Pi.single j (1 : ℝ) := by
    simp [hg, max_eq_left hcV.le]
  -- The remainder `Rₙ = t_{n,j} − a(V̂ₙ) ⬝ (√n δₙ)` vanishes where `V̂_{n,jj} ≥ c`.
  set R : ℕ → Ω → ℝ := fun n ω =>
    tStat K Y X n j ω - g (vHat Y X n ω) ⬝ᵥ (Real.sqrt n • delta K Y X n ω) with hR
  have hR0 : K.TendstoInProb R 0 := by
    refine K.tendstoInProb_of_vanishing R (fun n ω => vHat Y X n ω j j) (V j j) c hjj hcV ?_
    intro n ω hne
    by_contra hlt
    have hge : c ≤ vHat Y X n ω j j := not_lt.mp hlt
    apply hne
    simp only [hR, hg, tStat, smul_dotProduct, single_dotProduct, Pi.smul_apply, smul_eq_mul,
      max_eq_left hge, one_mul]
    rw [div_eq_mul_inv]
    ring
  -- Slutsky for the linear functional, then identify the statistic and the variance.
  have hslut := K.slutsky_dotProduct (fun n ω => Real.sqrt n • delta K Y X n ω) V
    (fun n ω => g (vHat Y X n ω)) (g V) R (ols_asymptotic_normality h.toSetting₅.toSetting)
    ha hR0
  have e1 : (fun n ω => g (vHat Y X n ω) ⬝ᵥ (Real.sqrt n • delta K Y X n ω) + R n ω) =
      fun n ω => tStat K Y X n j ω := by
    funext n ω
    simp [hR]
  have e2 : g V ⬝ᵥ V *ᵥ g V = 1 := by
    rw [hgV]
    have hsq : Real.sqrt (V j j) * Real.sqrt (V j j) = V j j := Real.mul_self_sqrt hVpos.le
    simp only [smul_dotProduct, mulVec_smul, dotProduct_smul, single_dotProduct, Matrix.mulVec,
      dotProduct_single, smul_eq_mul, one_mul, mul_one]
    have e : (Real.sqrt (V j j))⁻¹ * ((Real.sqrt (V j j))⁻¹ * V j j) =
        V j j / (Real.sqrt (V j j) * Real.sqrt (V j j)) := by ring
    rw [e, hsq, div_self hVpos.ne']
  rw [e1, e2] at hslut
  exact hslut

end Ols
