import Simple.Kernel
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# OLS for the linear projection coefficient: definitions

Everything is stated over a `Simple.Kernel K` — an expectation operator with a
moment-regularity class plus the named limit theorems. No measure appears.
Data: `Y : ℕ → Ω → ℝ`, `X : ℕ → Ω → Fin k → ℝ`. All matrix inverses use Mathlib's
`Matrix.inv`, which is `0` on singular matrices.
-/

open Matrix Finset Simple

namespace Ols

variable {Ω : Type*} (K : Kernel Ω) {k : ℕ}

/-- Population Gram matrix `Q = E[X Xᵀ]`. -/
noncomputable def gram (X : Ω → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun a b => K.E (fun ω => X ω a * X ω b)

/-- Population cross moment `E[X Y]`. -/
noncomputable def crossMoment (Y : Ω → ℝ) (X : Ω → Fin k → ℝ) : Fin k → ℝ :=
  fun a => K.E (fun ω => X ω a * Y ω)

/-- (D1) Linear projection coefficient `β₀ = Q⁻¹ E[X Y]`. -/
noncomputable def beta0 (Y : Ω → ℝ) (X : Ω → Fin k → ℝ) : Fin k → ℝ :=
  (gram K X)⁻¹ *ᵥ crossMoment K Y X

/-- (D2) Projection error `e = Y - Xᵀ β₀`, as a function of one observation. -/
noncomputable def projError (Y : Ω → ℝ) (X : Ω → Fin k → ℝ) (b : Fin k → ℝ) (ω : Ω) : ℝ :=
  Y ω - X ω ⬝ᵥ b

/-- Sample Gram matrix `Q̂ₙ = n⁻¹ ∑ Xᵢ Xᵢᵀ`. -/
noncomputable def sampleGram (X : ℕ → Ω → Fin k → ℝ) (n : ℕ) (ω : Ω) :
    Matrix (Fin k) (Fin k) ℝ :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, vecMulVec (X i ω) (X i ω)

/-- Sample cross moment `m̂ₙ = n⁻¹ ∑ Xᵢ Yᵢ`. -/
noncomputable def sampleCross (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (n : ℕ) (ω : Ω) :
    Fin k → ℝ :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, Y i ω • X i ω

/-- (D3) OLS estimator `β̂ₙ = Q̂ₙ⁻¹ m̂ₙ`, defined for every `ω` via `Matrix.inv`. -/
noncomputable def olsHat (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (n : ℕ) (ω : Ω) :
    Fin k → ℝ :=
  (sampleGram X n ω)⁻¹ *ᵥ sampleCross Y X n ω

/-- Score average `ḡₙ = n⁻¹ ∑ Xᵢ eᵢ` for a given coefficient `b`. -/
noncomputable def scoreAvg (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) (b : Fin k → ℝ) (n : ℕ)
    (ω : Ω) : Fin k → ℝ :=
  (n : ℝ)⁻¹ • ∑ i ∈ range n, projError (Y i) (X i) b ω • X i ω

/-- (D4) `Ω = E[e² X Xᵀ]` for a given coefficient `b`. -/
noncomputable def scoreVar (Y : Ω → ℝ) (X : Ω → Fin k → ℝ) (b : Fin k → ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  fun a c => K.E (fun ω => (projError Y X b ω * X ω a) * (projError Y X b ω * X ω c))

/-- Asymptotic variance `V = Q⁻¹ Ω Q⁻¹`. -/
noncomputable def asympVar (Y : Ω → ℝ) (X : Ω → Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  (gram K X)⁻¹ * scoreVar K Y X (beta0 K Y X) * (gram K X)⁻¹

/-- Assumptions (A1)–(A4): iid observations `(Yᵢ, Xᵢ)`, second moments, and a
positive definite Gram matrix. Regularity is `HasMoment`, nothing else. -/
structure Setting (Y : ℕ → Ω → ℝ) (X : ℕ → Ω → Fin k → ℝ) : Prop where
  /-- (A1) the observations `(Yᵢ, Xᵢ)` form an iid sequence. -/
  iid : K.IID (fun i ω => (Y i ω, X i ω))
  /-- (A2) `E[Y²] < ∞`. -/
  mom_Y : K.HasMoment (Y 0) 2
  /-- (A2) `E[‖X‖²] < ∞`, coordinatewise. -/
  mom_X : ∀ a, K.HasMoment (fun ω => X 0 ω a) 2
  /-- (A3) `Q = E[X Xᵀ]` positive definite. -/
  posDef : (gram K (X 0)).PosDef
  /-- (A4) `E[e² ‖X‖²] < ∞`, coordinatewise. -/
  mom_score : ∀ a,
    K.HasMoment (fun ω => projError (Y 0) (X 0) (beta0 K (Y 0) (X 0)) ω * X 0 ω a) 2

end Ols
