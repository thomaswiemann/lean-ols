import Ols.Projection
import Mathlib.Analysis.Normed.Ring.Units

/-!
# The sample Gram matrix: (3), (4), (5), (7)

* `tendstoInProb_sampleGram`: **(3)** `Q̂ₙ →p Q`, by (T1) in matrix form.
* `tendstoInProb_sampleGram_inv`: **(4)** `Q̂ₙ⁻¹ →p Q⁻¹`, by (T3); `Matrix.inv` is
  continuous at the invertible `Q` (topology only, no measure).
* `tendstoInProb_remainder`: **(5)+(7)** `-√n · 1{det Q̂ₙ = 0} b →p 0`, by (T3) for `det`
  and (T6): the remainder is nonzero only where `det Q̂ₙ = 0 < det Q / 2`.
-/

open Matrix Finset Simple

namespace Ols

variable {Ω : Type*} {K : Kernel Ω} {k : ℕ} {Y : ℕ → Ω → ℝ} {X : ℕ → Ω → Fin k → ℝ}

/-- The Gram summand `Xᵢ Xᵢᵀ`. -/
noncomputable def gramTerm (X : ℕ → Ω → Fin k → ℝ) (i : ℕ) (ω : Ω) :
    Matrix (Fin k) (Fin k) ℝ :=
  vecMulVec (X i ω) (X i ω)

/-- The Gram summands are iid: a function of the iid observations, by (T0). -/
lemma iid_gramTerm (h : Setting K Y X) : K.IID (gramTerm X) :=
  K.iid_comp _ (fun p : ℝ × (Fin k → ℝ) => vecMulVec p.2 p.2) h.iid

lemma hasMoment_gramTerm (h : Setting K Y X) (a b : Fin k) :
    K.HasMoment (fun ω => gramTerm X 0 ω a b) 1 := by
  simp only [gramTerm, vecMulVec_apply]
  exact K.hasMoment_mul _ _ (h.mom_X a) (h.mom_X b)

lemma sampleGram_eq_avg (n : ℕ) (ω : Ω) : sampleGram X n ω = sampleAvg (gramTerm X) n ω :=
  rfl

lemma gram_eq_E_gramTerm : gram K (X 0) = fun a b => K.E (fun ω => gramTerm X 0 ω a b) := by
  funext a b
  simp [gram, gramTerm, vecMulVec_apply]

/-- **(3)** `Q̂ₙ →p Q`. -/
theorem tendstoInProb_sampleGram (h : Setting K Y X) :
    K.TendstoInProb (fun n ω => sampleGram X n ω) (gram K (X 0)) := by
  rw [gram_eq_E_gramTerm]
  exact K.wlln_matrix (gramTerm X) (iid_gramTerm h) (hasMoment_gramTerm h)

lemma isUnit_det_gram (h : Setting K Y X) : IsUnit (gram K (X 0)).det :=
  isUnit_iff_ne_zero.mpr h.posDef.det_pos.ne'

lemma continuousAt_inv_gram (h : Setting K Y X) :
    ContinuousAt (Inv.inv : Matrix (Fin k) (Fin k) ℝ → Matrix (Fin k) (Fin k) ℝ)
      (gram K (X 0)) := by
  refine continuousAt_matrix_inv _ ?_
  have := NormedRing.inverse_continuousAt (isUnit_det_gram h).unit
  rwa [IsUnit.unit_spec] at this

/-- **(4)** `Q̂ₙ⁻¹ →p Q⁻¹`. -/
theorem tendstoInProb_sampleGram_inv (h : Setting K Y X) :
    K.TendstoInProb (fun n ω => (sampleGram X n ω)⁻¹) (gram K (X 0))⁻¹ :=
  K.cmt _ _ Inv.inv (continuousAt_inv_gram h) (tendstoInProb_sampleGram h)

/-- `det Q̂ₙ →p det Q`. -/
theorem tendstoInProb_det_sampleGram (h : Setting K Y X) :
    K.TendstoInProb (fun n ω => (sampleGram X n ω).det) (gram K (X 0)).det :=
  K.cmt _ _ Matrix.det continuous_id.matrix_det.continuousAt (tendstoInProb_sampleGram h)

open scoped Classical in
/-- **(5)+(7)** The remainder `-√n · 1{det Q̂ₙ = 0} b` vanishes in probability, for any fixed
vector `b`: it is nonzero only where `det Q̂ₙ = 0 < det Q / 2`, and `det Q̂ₙ →p det Q`. -/
theorem tendstoInProb_remainder (h : Setting K Y X) (b : Fin k → ℝ) :
    K.TendstoInProb
      (fun (n : ℕ) ω =>
        -(Real.sqrt n • (if IsUnit (sampleGram X n ω).det then (0 : Fin k → ℝ) else b)))
      0 := by
  have hpos := h.posDef.det_pos
  refine K.tendstoInProb_of_vanishing _ (fun n ω => (sampleGram X n ω).det)
    (gram K (X 0)).det ((gram K (X 0)).det / 2) (tendstoInProb_det_sampleGram h)
    (by linarith) ?_
  intro n ω hne
  split_ifs at hne with hu
  · exact absurd (by simp) hne
  · have h0 : (sampleGram X n ω).det = 0 := by simpa [isUnit_iff_ne_zero] using hu
    rw [h0]
    linarith

end Ols
