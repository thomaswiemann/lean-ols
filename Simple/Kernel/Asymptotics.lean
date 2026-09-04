import Simple.Kernel.Convergence
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Real.Sqrt

/-!
# Postulates (T): sampling and limit theorems under one law

`Kernel Ω` adds to `Expectation Ω` the primitives `IID` and `→d N(μ, Σ)` and the
named postulates:

* (T0) functions of iid observations are iid;
* (T1) weak law of large numbers, (T2) multivariate Lindeberg–Lévy CLT,
  (T4) Slutsky `Bₙ Zₙ + Rₙ →d N(0, B Σ Bᵀ)`.

Convergence in probability is *not* a primitive: it is `Expectation.TendstoInProb`,
defined from `Pr` in `Kernel.Convergence`, and continuous mapping, joint
convergence and the vanishing-event rule are theorems there.
-/

open Finset Matrix

namespace Simple

variable {Ω : Type*}

/-- The sample average `n⁻¹ ∑_{i<n} Wᵢ`. Finite-sum algebra. -/
noncomputable def sampleAvg {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (W : ℕ → Ω → V) (n : ℕ) (ω : Ω) : V :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, W i ω

/-- The normalized sum `n^{-1/2} ∑_{i<n} Wᵢ`, the argument of a CLT. -/
noncomputable def normSum {k : ℕ} (W : ℕ → Ω → Fin k → ℝ) (n : ℕ) (ω : Ω) :
    Fin k → ℝ :=
  (Real.sqrt n)⁻¹ • ∑ i ∈ range n, W i ω

/-- **Postulates (T0)–(T2), (T4)** on top of (E1)–(E11), for one law. -/
structure Kernel (Ω : Type*) extends Expectation Ω where
  /-- `IID W` : the observations `W 0, W 1, …` are iid under the law. -/
  IID : {β : Type} → (ℕ → Ω → β) → Prop
  /-- `TendstoInDist X μ Σ` : `Xₙ →d N(μ, Σ)`. -/
  TendstoInDist : {k : ℕ} → (ℕ → Ω → Fin k → ℝ) → (Fin k → ℝ) →
    Matrix (Fin k) (Fin k) ℝ → Prop
  /-- (T0) Functions of iid observations are iid. -/
  iid_comp : ∀ {β γ : Type} (W : ℕ → Ω → β) (g : β → γ),
    IID W → IID (fun i ω => g (W i ω))
  /-- (T1) Weak law of large numbers: for an iid `L¹` sequence,
  `n⁻¹ ∑ Wᵢ →p E[W₀]`. -/
  wlln : ∀ (W : ℕ → Ω → ℝ), IID W → HasMoment (W 0) 1 →
    toExpectation.TendstoInProb (fun n => sampleAvg W n) (E (W 0))
  /-- (T2) Multivariate Lindeberg–Lévy CLT: for an iid, centered sequence
  with `L²` coordinates, `n^{-1/2} ∑ Wᵢ →d N(0, E[W₀ W₀ᵀ])`. -/
  clt : ∀ {k : ℕ} (W : ℕ → Ω → Fin k → ℝ), IID W →
    (∀ a, HasMoment (fun ω => W 0 ω a) 2) → (∀ a, E (fun ω => W 0 ω a) = 0) →
    TendstoInDist (normSum W) 0 (fun a b => E (fun ω => W 0 ω a * W 0 ω b))
  /-- (T4) Slutsky, estimator form: `Zₙ →d N(0, Σ)` in `ℝᵏ`, random `m × k`
  matrices `Bₙ →p B`, and `Rₙ →p 0` in `ℝᵐ` give
  `Bₙ Zₙ + Rₙ →d N(0, B Σ Bᵀ)`. -/
  slutsky : ∀ {m k : ℕ} (Z : ℕ → Ω → Fin k → ℝ) (cov : Matrix (Fin k) (Fin k) ℝ)
    (B : ℕ → Ω → Matrix (Fin m) (Fin k) ℝ) (B₀ : Matrix (Fin m) (Fin k) ℝ)
    (R : ℕ → Ω → Fin m → ℝ),
    TendstoInDist Z 0 cov → toExpectation.TendstoInProb B B₀ →
    toExpectation.TendstoInProb R 0 →
    TendstoInDist (fun n ω => B n ω *ᵥ Z n ω + R n ω) 0 (B₀ * cov * B₀ᵀ)

namespace Kernel

variable (K : Kernel Ω)

/-- Second-moment matrix `E[W Wᵀ]`. -/
noncomputable def secondMoment {k : ℕ} (W : Ω → Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun a b => K.E (fun ω => W ω a * W ω b)

/-- (T2) restated with `secondMoment`. -/
theorem clt' {k : ℕ} (W : ℕ → Ω → Fin k → ℝ) (hIID : K.IID W)
    (hMom : ∀ a, K.HasMoment (fun ω => W 0 ω a) 2)
    (hmean : ∀ a, K.E (fun ω => W 0 ω a) = 0) :
    K.TendstoInDist (normSum W) 0 (K.secondMoment (W 0)) :=
  K.clt W hIID hMom hmean

/-! ### Derived: vector and matrix laws of large numbers -/

lemma sampleAvg_apply {ι : Type*} (W : ℕ → Ω → ι → ℝ) (n : ℕ) (ω : Ω) (i : ι) :
    sampleAvg W n ω i = sampleAvg (fun j ω => W j ω i) n ω := by
  simp [sampleAvg, Finset.sum_apply]

/-- Row `a` of a matrix sample average is the sample average of row `a`. -/
lemma sampleAvg_matrix_row {k : ℕ} (W : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ)
    (n : ℕ) (ω : Ω) (a : Fin k) :
    sampleAvg W n ω a = sampleAvg (fun j ω => W j ω a) n ω := by
  funext b
  simp [sampleAvg, Matrix.smul_apply, Matrix.sum_apply, Finset.sum_apply]

/-- (T1), vector form: from the scalar law and joint convergence. -/
theorem wlln_pi {ι : Type} (W : ℕ → Ω → ι → ℝ) (hIID : K.IID W)
    (hMom : ∀ i, K.HasMoment (fun ω => W 0 ω i) 1) :
    K.TendstoInProb (fun n => sampleAvg W n) (fun i => K.E (fun ω => W 0 ω i)) := by
  refine K.tendstoInProb_pi (π := fun _ => ℝ) _ _ fun i => ?_
  have h := K.wlln (fun j ω => W j ω i) (K.iid_comp W (fun v => v i) hIID) (hMom i)
  convert h using 1
  funext n ω
  exact sampleAvg_apply W n ω i

/-- (T1), matrix form: `Matrix` carries the product topology, so this is the vector form
applied row by row. -/
theorem wlln_matrix {k : ℕ} (W : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hIID : K.IID W)
    (hMom : ∀ a b, K.HasMoment (fun ω => W 0 ω a b) 1) :
    K.TendstoInProb (fun n => sampleAvg W n) (fun a b => K.E (fun ω => W 0 ω a b)) := by
  refine K.tendstoInProb_pi (π := fun _ => Fin k → ℝ) _ _ fun a => ?_
  have hrow := K.wlln_pi (fun j ω => W j ω a) (K.iid_comp W (fun M => M a) hIID) (hMom a)
  convert hrow using 1
  funext n ω
  exact sampleAvg_matrix_row W n ω a

/-! ### Derived: scalar statistics -/

/-- `Xₙ →d N(0, σ²)` for a real statistic: the vector primitive in dimension one. -/
def TendstoInDistReal (X : ℕ → Ω → ℝ) (σsq : ℝ) : Prop :=
  K.TendstoInDist (fun n ω (_ : Fin 1) => X n ω) 0 (fun _ _ => σsq)

/-- (T4) for a random linear functional: `Zₙ →d N(0, Σ)`, `aₙ →p a₀`, `Rₙ →p 0` give
`aₙ ⬝ Zₙ + Rₙ →d N(0, a₀ᵀ Σ a₀)`. The `1 × k` case of Slutsky. -/
theorem slutsky_dotProduct {k : ℕ} (Z : ℕ → Ω → Fin k → ℝ) (cov : Matrix (Fin k) (Fin k) ℝ)
    (a : ℕ → Ω → Fin k → ℝ) (a₀ : Fin k → ℝ) (R : ℕ → Ω → ℝ)
    (hZ : K.TendstoInDist Z 0 cov) (ha : K.TendstoInProb a a₀) (hR : K.TendstoInProb R 0) :
    K.TendstoInDistReal (fun n ω => a n ω ⬝ᵥ Z n ω + R n ω) (a₀ ⬝ᵥ cov *ᵥ a₀) := by
  have hB : K.TendstoInProb
      (fun n ω => (Matrix.of fun (_ : Fin 1) b => a n ω b : Matrix (Fin 1) (Fin k) ℝ))
      (Matrix.of fun _ b => a₀ b) :=
    K.cmt a a₀ (fun v => Matrix.of fun _ b => v b)
      (continuous_matrix fun _ b => continuous_apply b).continuousAt ha
  have hR' : K.TendstoInProb (fun n ω (_ : Fin 1) => R n ω) (fun _ => 0) :=
    K.cmt R 0 (fun r (_ : Fin 1) => r) (continuous_pi fun _ => continuous_id).continuousAt hR
  have h := K.slutsky Z cov _ _ _ hZ hB hR'
  have e1 : (fun n ω (_ : Fin 1) => a n ω ⬝ᵥ Z n ω + R n ω) =
      fun n ω => (Matrix.of fun (_ : Fin 1) b => a n ω b) *ᵥ Z n ω + fun _ => R n ω := by
    funext n ω i
    simp [Matrix.mulVec, dotProduct]
  have e2 : (fun (_ _ : Fin 1) => a₀ ⬝ᵥ cov *ᵥ a₀) =
      (Matrix.of fun (_ : Fin 1) b => a₀ b) * cov * (Matrix.of fun (_ : Fin 1) b => a₀ b)ᵀ := by
    funext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct,
      Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  unfold TendstoInDistReal
  rw [e1, e2]
  exact h

end Kernel

end Simple
