import Ols.Main

/-!
# Theorem 2: consistency of `β̂ₙ`, `Ω̂ₙ`, and `V̂ₙ`

Postulates used: (E1)–(E9), (T0), (T1), (T3), (T5), (T5'), (T6).

* `olsHat_tendstoInProb` — (a) `β̂ₙ →p β₀`, from (8) `δₙ = Q̂ₙ⁻¹ ḡₙ − 1{Aₙᶜ} β₀`.
* `omegaHat_tendstoInProb` — (b) `Ω̂ₙ →p Ω`, from the exact identity (9)
  `Ω̂ₙ = Sₙ − 2 Mₙ[δₙ] + Kₙ[δₙ, δₙ]`, the laws of large numbers for `Sₙ, Mₙ, Kₙ`, and
  continuity of the polynomial map `F`.
* `vHat_tendstoInProb` — (c) `V̂ₙ →p V`.
-/

open Matrix Finset Simple

namespace Ols

variable {Ω : Type*} {K : Kernel Ω} {k : ℕ} {Y : ℕ → Ω → ℝ} {X : ℕ → Ω → Fin k → ℝ}

/-- (A1)–(A5). -/
structure Setting₅ (K : Kernel Ω) (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) : Prop
    extends Setting K Y X where
  /-- (A5) `E[|e| ‖X‖³] < ∞`, coordinatewise. -/
  mom_eXXX : ∀ c a b, K.HasMoment
    (fun ω => projError (Y 0) (X 0) (beta0 K (Y 0) (X 0)) ω * X 0 ω c * X 0 ω a * X 0 ω b) 1
  /-- (A5) `E[‖X‖⁴] < ∞`, coordinatewise. -/
  mom_XXXX : ∀ c d a b, K.HasMoment (fun ω => X 0 ω c * X 0 ω d * X 0 ω a * X 0 ω b) 1

/-! ### Definitions (D5), (D7) -/

/-- (D5) `δₙ = β̂ₙ − β₀`. -/
noncomputable def delta (K : Kernel Ω) (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (n : ℕ)
    (ω : Ω) : Fin k → ℝ :=
  olsHat Y X n ω - beta0 K (Y 0) (X 0)

/-- (D5) residual `êᵢ = Yᵢ − Xᵢᵀ β̂ₙ`. -/
noncomputable def residual (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (n i : ℕ) (ω : Ω) : ℝ :=
  projError (Y i) (X i) (olsHat Y X n ω) ω

/-- (D5) `Ω̂ₙ = n⁻¹ ∑ êᵢ² Xᵢ Xᵢᵀ`. -/
noncomputable def omegaHat (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (n : ℕ) (ω : Ω) :
    Matrix (Fin k) (Fin k) ℝ :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, residual Y X n i ω ^ 2 • vecMulVec (X i ω) (X i ω)

/-- (D5) `V̂ₙ = Q̂ₙ⁻¹ Ω̂ₙ Q̂ₙ⁻¹`. -/
noncomputable def vHat (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (n : ℕ) (ω : Ω) :
    Matrix (Fin k) (Fin k) ℝ :=
  (sampleGram X n ω)⁻¹ * omegaHat Y X n ω * (sampleGram X n ω)⁻¹

/-- The arrays of (D7), as one observation's contribution: `(eᵢ² Xᵢ Xᵢᵀ, eᵢ Xᵢ⊗Xᵢ⊗Xᵢ,
Xᵢ⊗Xᵢ⊗Xᵢ⊗Xᵢ)`. -/
abbrev Tensors (k : ℕ) : Type :=
  Matrix (Fin k) (Fin k) ℝ × (Fin k × Fin k × Fin k → ℝ) × (Fin k × Fin k × Fin k × Fin k → ℝ)

/-- (D7) summand `eᵢ² Xᵢ Xᵢᵀ`. -/
noncomputable def scoreSq (K : Kernel Ω) (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (i : ℕ)
    (ω : Ω) : Matrix (Fin k) (Fin k) ℝ :=
  projError (Y i) (X i) (beta0 K (Y 0) (X 0)) ω ^ 2 • vecMulVec (X i ω) (X i ω)

/-- (D7) summand `eᵢ Xᵢ ⊗ Xᵢ ⊗ Xᵢ`. -/
noncomputable def cubic (K : Kernel Ω) (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (i : ℕ)
    (ω : Ω) : Fin k × Fin k × Fin k → ℝ :=
  fun p => projError (Y i) (X i) (beta0 K (Y 0) (X 0)) ω * X i ω p.1 * X i ω p.2.1 * X i ω p.2.2

/-- (D7) summand `Xᵢ ⊗ Xᵢ ⊗ Xᵢ ⊗ Xᵢ`. -/
noncomputable def quartic (X : ℕ → Ω → Fin k → ℝ) (i : ℕ) (ω : Ω) :
    Fin k × Fin k × Fin k × Fin k → ℝ :=
  fun p => X i ω p.1 * X i ω p.2.1 * X i ω p.2.2.1 * X i ω p.2.2.2

/-- The three summands together. -/
noncomputable def tensors (K : Kernel Ω) (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (i : ℕ)
    (ω : Ω) : Tensors k :=
  (scoreSq K Y X i ω, cubic K Y X i ω, quartic X i ω)

/-- Contraction `M[δ]_{ab} = ∑_c δ_c M_{cab}`, linear in `M`. -/
noncomputable def contract₁ (δ : Fin k → ℝ) :
    (Fin k × Fin k × Fin k → ℝ) →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ where
  toFun M := Matrix.of fun a b => ∑ c, δ c * M (c, a, b)
  map_add' M N := by
    ext a b
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' r M := by
    ext a b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Matrix.smul_apply, Matrix.of_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring

/-- Contraction `K[δ, δ]_{ab} = ∑_{c,d} δ_c δ_d K_{cdab}`, linear in `K`. -/
noncomputable def contract₂ (δ : Fin k → ℝ) :
    (Fin k × Fin k × Fin k × Fin k → ℝ) →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ where
  toFun Kt := Matrix.of fun a b => ∑ c, ∑ d, δ c * δ d * Kt (c, d, a, b)
  map_add' M N := by
    ext a b
    simp [Finset.sum_add_distrib, mul_add]
  map_smul' r M := by
    ext a b
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Matrix.smul_apply, Matrix.of_apply,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

/-- `F(S, M, K, δ) = S − 2 M[δ] + K[δ, δ]`, linear in `(S, M, K)` for fixed `δ`. -/
noncomputable def polyF (δ : Fin k → ℝ) : Tensors k →ₗ[ℝ] Matrix (Fin k) (Fin k) ℝ :=
  LinearMap.fst ℝ _ _ - (2 : ℝ) • (contract₁ δ ∘ₗ LinearMap.fst ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _)
    + contract₂ δ ∘ₗ LinearMap.snd ℝ _ _ ∘ₗ LinearMap.snd ℝ _ _

lemma polyF_apply (δ : Fin k → ℝ) (T : Tensors k) (a b : Fin k) :
    polyF δ T a b =
      T.1 a b - 2 * ∑ c, δ c * T.2.1 (c, a, b) + ∑ c, ∑ d, δ c * δ d * T.2.2 (c, d, a, b) := by
  simp [polyF, contract₁, contract₂]

/-! ### The exact identity (9) -/

lemma residual_eq (n i : ℕ) (ω : Ω) :
    residual Y X n i ω =
      projError (Y i) (X i) (beta0 K (Y 0) (X 0)) ω - X i ω ⬝ᵥ delta K Y X n ω := by
  simp only [residual, projError, delta, dotProduct_sub]
  ring

/-- One observation: `(e − x⬝δ)² x_a x_b = e² x_a x_b − 2 ∑_c δ_c e x_c x_a x_b +
∑_{c,d} δ_c δ_d x_c x_d x_a x_b`. -/
lemma sq_mul_expand (e : ℝ) (x δ : Fin k → ℝ) (a b : Fin k) :
    (e - x ⬝ᵥ δ) ^ 2 * (x a * x b) =
      e ^ 2 * (x a * x b) - 2 * ∑ c, δ c * (e * x c * x a * x b)
        + ∑ c, ∑ d, δ c * δ d * (x c * x d * x a * x b) := by
  have h1 : ∑ c, δ c * (e * x c * x a * x b) = e * (x ⬝ᵥ δ) * (x a * x b) := by
    simp only [dotProduct, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  have h2 : ∑ c, ∑ d, δ c * δ d * (x c * x d * x a * x b) = (x ⬝ᵥ δ) ^ 2 * (x a * x b) := by
    simp only [dotProduct, sq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [h1, h2]
  ring

/-- One observation, in matrix form: `êᵢ² Xᵢ Xᵢᵀ = F(eᵢ² Xᵢ Xᵢᵀ, eᵢ Xᵢ⊗Xᵢ⊗Xᵢ, Xᵢ⊗⁴, δₙ)`. -/
lemma residual_term_eq (n i : ℕ) (ω : Ω) :
    residual Y X n i ω ^ 2 • vecMulVec (X i ω) (X i ω) =
      polyF (delta K Y X n ω) (tensors K Y X i ω) := by
  ext a b
  rw [polyF_apply, residual_eq (K := K)]
  simp only [tensors, scoreSq, cubic, quartic, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  exact sq_mul_expand _ _ _ a b

/-- **(9)** `Ω̂ₙ = F(Sₙ, Mₙ, Kₙ, δₙ)`, for every `n` and `ω`. -/
lemma omegaHat_eq (n : ℕ) (ω : Ω) :
    omegaHat Y X n ω = polyF (delta K Y X n ω) (sampleAvg (tensors K Y X) n ω) := by
  rw [omegaHat, sampleAvg, map_smul, map_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => residual_term_eq n i ω

/-- The average of the triple is the triple of averages. -/
lemma sampleAvg_tensors (n : ℕ) (ω : Ω) :
    sampleAvg (tensors K Y X) n ω =
      (sampleAvg (scoreSq K Y X) n ω, sampleAvg (cubic K Y X) n ω, sampleAvg (quartic X) n ω) := by
  simp [sampleAvg, tensors, Prod.ext_iff, Prod.fst_sum, Prod.snd_sum]

/-- `F` is continuous in all four arguments (a polynomial in the entries). -/
lemma continuous_polyF :
    Continuous fun p : Tensors k × (Fin k → ℝ) => polyF p.2 p.1 := by
  refine continuous_matrix fun a b => ?_
  simp only [polyF_apply]
  have hS : Continuous fun p : Tensors k × (Fin k → ℝ) => p.1.1 a b :=
    (continuous_fst.comp continuous_fst).matrix_elem a b
  have hM : ∀ q, Continuous fun p : Tensors k × (Fin k → ℝ) => p.1.2.1 q := fun q =>
    (continuous_apply q).comp (continuous_fst.comp (continuous_snd.comp continuous_fst))
  have hK : ∀ q, Continuous fun p : Tensors k × (Fin k → ℝ) => p.1.2.2 q := fun q =>
    (continuous_apply q).comp (continuous_snd.comp (continuous_snd.comp continuous_fst))
  have hδ : ∀ c, Continuous fun p : Tensors k × (Fin k → ℝ) => p.2 c := fun c =>
    (continuous_apply c).comp continuous_snd
  refine (hS.sub (continuous_const.mul (continuous_finsetSum _ fun c _ =>
    (hδ c).mul (hM _)))).add ?_
  exact continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ =>
    ((hδ c).mul (hδ d)).mul (hK _)

/-! ### (a) `β̂ₙ →p β₀` -/

lemma scoreAvg_eq_sampleAvg (n : ℕ) (ω : Ω) :
    scoreAvg Y X (beta0 K (Y 0) (X 0)) n ω = sampleAvg (score K Y X) n ω :=
  rfl

/-- `ḡₙ →p 0`, by (T1) on the centered scores. -/
theorem scoreAvg_tendstoInProb (h : Setting K Y X) :
    K.TendstoInProb (fun n ω => scoreAvg Y X (beta0 K (Y 0) (X 0)) n ω) 0 := by
  have hw := K.wlln_pi (score K Y X) (iid_score h)
    fun a => K.hasMoment_one_of_two (hasMoment_score_coord h a)
  have e : (fun a => K.E (fun ω => score K Y X 0 ω a)) = (0 : Fin k → ℝ) := by
    funext a
    exact E_score_coord h a
  rw [e] at hw
  exact hw

open scoped Classical in
/-- `1{det Q̂ₙ = 0} b →p 0`, by (T6). -/
theorem tendstoInProb_indicator (h : Setting K Y X) (b : Fin k → ℝ) :
    K.TendstoInProb
      (fun (n : ℕ) ω => if IsUnit (sampleGram X n ω).det then (0 : Fin k → ℝ) else b) 0 := by
  have hpos := h.posDef.det_pos
  refine K.tendstoInProb_of_vanishing _ (fun n ω => (sampleGram X n ω).det)
    (gram K (X 0)).det ((gram K (X 0)).det / 2) (tendstoInProb_det_sampleGram h)
    (by linarith) ?_
  intro n ω hne
  split_ifs at hne with hu
  · exact absurd rfl hne
  · have h0 : (sampleGram X n ω).det = 0 := by simpa [isUnit_iff_ne_zero] using hu
    rw [h0]
    linarith

/-- `δₙ →p 0`: (8) with (4), `ḡₙ →p 0`, (T5') and (T3) for `(B, g) ↦ B g` and subtraction. -/
theorem delta_tendstoInProb (h : Setting K Y X) : K.TendstoInProb (delta K Y X) 0 := by
  classical
  have h1 := K.cmt₂ _ _ _ _ (fun B g => B *ᵥ g)
    (continuous_fst.matrix_mulVec continuous_snd).continuousAt
    (tendstoInProb_sampleGram_inv h) (scoreAvg_tendstoInProb h)
  have h2 := K.cmt₂ _ _ _ _ (fun u v => u - v) (continuous_fst.sub continuous_snd).continuousAt
    h1 (tendstoInProb_indicator h (beta0 K (Y 0) (X 0)))
  rw [mulVec_zero, sub_zero] at h2
  have e : delta K Y X = fun n ω =>
      (sampleGram X n ω)⁻¹ *ᵥ scoreAvg Y X (beta0 K (Y 0) (X 0)) n ω -
        (if IsUnit (sampleGram X n ω).det then 0 else beta0 K (Y 0) (X 0)) := by
    funext n ω
    exact olsHat_sub_beta0 (beta0 K (Y 0) (X 0)) n ω
  rw [e]
  exact h2

/-- **Theorem 2(a).** `β̂ₙ →p β₀`. -/
theorem olsHat_tendstoInProb (h : Setting K Y X) :
    K.TendstoInProb (fun n ω => olsHat Y X n ω) (beta0 K (Y 0) (X 0)) := by
  have := K.cmt (delta K Y X) 0 (fun u => u + beta0 K (Y 0) (X 0))
    (continuous_id.add continuous_const).continuousAt (delta_tendstoInProb h)
  simpa [delta] using this

/-! ### (b) `Ω̂ₙ →p Ω` -/

lemma iid_scoreSq (h : Setting K Y X) : K.IID (scoreSq K Y X) :=
  K.iid_comp _ (fun p : ℝ × (Fin k → ℝ) =>
    (p.1 - p.2 ⬝ᵥ beta0 K (Y 0) (X 0)) ^ 2 • vecMulVec p.2 p.2) h.iid

lemma iid_cubic (h : Setting K Y X) : K.IID (cubic K Y X) :=
  K.iid_comp _ (fun p : ℝ × (Fin k → ℝ) => fun q : Fin k × Fin k × Fin k =>
    (p.1 - p.2 ⬝ᵥ beta0 K (Y 0) (X 0)) * p.2 q.1 * p.2 q.2.1 * p.2 q.2.2) h.iid

lemma iid_quartic (h : Setting K Y X) : K.IID (quartic X) :=
  K.iid_comp _ (fun p : ℝ × (Fin k → ℝ) => fun q : Fin k × Fin k × Fin k × Fin k =>
    p.2 q.1 * p.2 q.2.1 * p.2 q.2.2.1 * p.2 q.2.2.2) h.iid

lemma scoreSq_apply (i : ℕ) (ω : Ω) (a b : Fin k) :
    scoreSq K Y X i ω a b =
      (projError (Y i) (X i) (beta0 K (Y 0) (X 0)) ω * X i ω a) *
        (projError (Y i) (X i) (beta0 K (Y 0) (X 0)) ω * X i ω b) := by
  simp only [scoreSq, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
  ring

/-- `Sₙ →p Ω`, by (T1) in matrix form; the entries are `L¹` by (A4). -/
theorem scoreSq_tendstoInProb (h : Setting K Y X) :
    K.TendstoInProb (fun n ω => sampleAvg (scoreSq K Y X) n ω)
      (scoreVar K (Y 0) (X 0) (beta0 K (Y 0) (X 0))) := by
  have hw := K.wlln_matrix (scoreSq K Y X) (iid_scoreSq h) fun a b => by
    simp only [scoreSq_apply]
    exact K.hasMoment_mul _ _ (h.mom_score a) (h.mom_score b)
  have e : (fun a b => K.E (fun ω => scoreSq K Y X 0 ω a b)) =
      scoreVar K (Y 0) (X 0) (beta0 K (Y 0) (X 0)) := by
    funext a b
    simp only [scoreVar, scoreSq_apply]
  rw [e] at hw
  exact hw

/-- `Mₙ →p M`, by (T1); the entries are `L¹` by (A5). -/
theorem cubic_tendstoInProb (h : Setting₅ K Y X) :
    K.TendstoInProb (fun n ω => sampleAvg (cubic K Y X) n ω)
      (fun q => K.E (fun ω => cubic K Y X 0 ω q)) :=
  K.wlln_pi (cubic K Y X) (iid_cubic h.toSetting) fun q => h.mom_eXXX q.1 q.2.1 q.2.2

/-- `Kₙ →p K`, by (T1); the entries are `L¹` by (A5). -/
theorem quartic_tendstoInProb (h : Setting₅ K Y X) :
    K.TendstoInProb (fun n ω => sampleAvg (quartic X) n ω)
      (fun q => K.E (fun ω => quartic X 0 ω q)) :=
  K.wlln_pi (quartic X) (iid_quartic h.toSetting) fun q => h.mom_XXXX q.1 q.2.1 q.2.2.1 q.2.2.2

/-- **Theorem 2(b).** `Ω̂ₙ →p Ω`. -/
theorem omegaHat_tendstoInProb (h : Setting₅ K Y X) :
    K.TendstoInProb (fun n ω => omegaHat Y X n ω)
      (scoreVar K (Y 0) (X 0) (beta0 K (Y 0) (X 0))) := by
  have hT : K.TendstoInProb (fun n ω => sampleAvg (tensors K Y X) n ω)
      (scoreVar K (Y 0) (X 0) (beta0 K (Y 0) (X 0)),
        fun q => K.E (fun ω => cubic K Y X 0 ω q), fun q => K.E (fun ω => quartic X 0 ω q)) := by
    have := K.tendstoInProb_prod _ _ _ _ (scoreSq_tendstoInProb h.toSetting)
      (K.tendstoInProb_prod _ _ _ _ (cubic_tendstoInProb h) (quartic_tendstoInProb h))
    have e : (fun n ω => sampleAvg (tensors K Y X) n ω) = fun n ω =>
        (sampleAvg (scoreSq K Y X) n ω, sampleAvg (cubic K Y X) n ω,
          sampleAvg (quartic X) n ω) := by
      funext n ω
      exact sampleAvg_tensors n ω
    rw [e]
    exact this
  have hF := K.cmt₂ _ _ _ _ (fun T δ => polyF δ T) continuous_polyF.continuousAt hT
    (delta_tendstoInProb h.toSetting)
  have e : (fun n ω => omegaHat Y X n ω) =
      fun n ω => polyF (delta K Y X n ω) (sampleAvg (tensors K Y X) n ω) := by
    funext n ω
    exact omegaHat_eq n ω
  rw [e]
  convert hF using 1
  ext a b
  simp [polyF_apply]

/-! ### (c) `V̂ₙ →p V` -/

/-- **Theorem 2(c).** `V̂ₙ →p V = Q⁻¹ Ω Q⁻¹`. -/
theorem vHat_tendstoInProb (h : Setting₅ K Y X) :
    K.TendstoInProb (fun n ω => vHat Y X n ω) (asympVar K (Y 0) (X 0)) :=
  K.cmt₂ _ _ _ _ (fun B W => B * W * B)
    ((continuous_fst.matrix_mul continuous_snd).matrix_mul continuous_fst).continuousAt
    (tendstoInProb_sampleGram_inv h.toSetting) (omegaHat_tendstoInProb h)

end Ols
