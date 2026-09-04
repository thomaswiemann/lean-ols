import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Postulates (E): expectation as an operator

A law on a sample space `Ω` is given as an expectation operator `E` together
with a regularity class `HasMoment f p` ("`E|f|^p < ∞`"). These are the
objects the papers write `E[·]` and "assume finite `p`-th moments" for; here
they are primitives, and the eleven postulates (E1)–(E11) are the rules the
papers use without comment. Nothing here is a `Measure`, a σ-algebra, or an
integral: `Ω` is a bare type and `E` a function on `Ω → ℝ`.

Everything else in this file is *derived* from (E1)–(E11): negation,
subtraction, finite sums, constants, monotonicity.
-/

open Finset

namespace Simple

/-- **Postulates (E1)–(E11).** A law on `Ω`, as an expectation operator `E`
and a moment-regularity class `HasMoment`. -/
structure Expectation (Ω : Type*) where
  /-- The expectation `E[f]` of a real random variable `f`. -/
  E : (Ω → ℝ) → ℝ
  /-- `HasMoment f p` : the `p`-th absolute moment of `f` is finite.
  This is the regularity the papers assume ("`E[Y²] < ∞`"). -/
  HasMoment : (Ω → ℝ) → ℕ → Prop
  /-- (E1) Lower moments are finite when higher ones are. -/
  hasMoment_mono : ∀ (f : Ω → ℝ) {p q : ℕ}, p ≤ q → HasMoment f q → HasMoment f p
  /-- (E2) Sums of `L^p` variables are `L^p`. -/
  hasMoment_add : ∀ (f g : Ω → ℝ) (p : ℕ),
    HasMoment f p → HasMoment g p → HasMoment (fun ω => f ω + g ω) p
  /-- (E3) Scalar multiples of `L^p` variables are `L^p`. -/
  hasMoment_smul : ∀ (c : ℝ) (f : Ω → ℝ) (p : ℕ),
    HasMoment f p → HasMoment (fun ω => c * f ω) p
  /-- (E4) The product of two `L²` variables is `L¹` (Cauchy–Schwarz). -/
  hasMoment_mul : ∀ (f g : Ω → ℝ),
    HasMoment f 2 → HasMoment g 2 → HasMoment (fun ω => f ω * g ω) 1
  /-- (E5) Constants have all moments. -/
  hasMoment_const : ∀ (c : ℝ) (p : ℕ), HasMoment (fun _ => c) p
  /-- (E6) `E` is additive on `L¹`. -/
  E_add : ∀ (f g : Ω → ℝ), HasMoment f 1 → HasMoment g 1 →
    E (fun ω => f ω + g ω) = E f + E g
  /-- (E7) `E` is homogeneous on `L¹`. -/
  E_smul : ∀ (c : ℝ) (f : Ω → ℝ), HasMoment f 1 → E (fun ω => c * f ω) = c * E f
  /-- (E8) `E` of a constant is that constant (the law has total mass one). -/
  E_const : ∀ c : ℝ, E (fun _ => c) = c
  /-- (E9) `E` is monotone: a nonnegative `L¹` variable has nonnegative mean. -/
  E_nonneg : ∀ f : Ω → ℝ, HasMoment f 1 → (∀ ω, 0 ≤ f ω) → 0 ≤ E f
  /-- (E10) Bounded variables have every moment. Indicators of events in particular. -/
  hasMoment_of_bounded : ∀ (f : Ω → ℝ) (M : ℝ) (p : ℕ), (∀ ω, |f ω| ≤ M) → HasMoment f p
  /-- (E11) `|f|` is as regular as `f`. -/
  hasMoment_abs : ∀ (f : Ω → ℝ) (p : ℕ), HasMoment f p → HasMoment (fun ω => |f ω|) p

namespace Expectation

variable {Ω : Type*} (ℰ : Expectation Ω)

/-! ### Derived: moments -/

lemma hasMoment_one_of_two {f : Ω → ℝ} (h : ℰ.HasMoment f 2) : ℰ.HasMoment f 1 :=
  ℰ.hasMoment_mono f (by decide : 1 ≤ 2) h

lemma hasMoment_zero (p : ℕ) : ℰ.HasMoment (fun _ => (0 : ℝ)) p :=
  ℰ.hasMoment_const 0 p

lemma hasMoment_neg {f : Ω → ℝ} {p : ℕ} (h : ℰ.HasMoment f p) :
    ℰ.HasMoment (fun ω => -f ω) p := by
  have := ℰ.hasMoment_smul (-1) f p h
  simpa only [neg_one_mul] using this

lemma hasMoment_sub {f g : Ω → ℝ} {p : ℕ} (hf : ℰ.HasMoment f p)
    (hg : ℰ.HasMoment g p) : ℰ.HasMoment (fun ω => f ω - g ω) p := by
  have := ℰ.hasMoment_add f (fun ω => -g ω) p hf (ℰ.hasMoment_neg hg)
  simpa only [sub_eq_add_neg] using this

lemma hasMoment_mul_const {f : Ω → ℝ} {p : ℕ} (c : ℝ) (h : ℰ.HasMoment f p) :
    ℰ.HasMoment (fun ω => f ω * c) p := by
  have := ℰ.hasMoment_smul c f p h
  simpa only [mul_comm] using this

/-- Finite sums of `L^p` variables are `L^p`. -/
lemma hasMoment_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) (p : ℕ)
    (h : ∀ i ∈ s, ℰ.HasMoment (f i) p) :
    ℰ.HasMoment (fun ω => ∑ i ∈ s, f i ω) p := by
  induction s using Finset.cons_induction with
  | empty => simpa using ℰ.hasMoment_zero p
  | cons a s ha ih =>
    have hs : ℰ.HasMoment (fun ω => ∑ i ∈ s, f i ω) p :=
      ih fun i hi => h i (Finset.mem_cons_of_mem hi)
    have := ℰ.hasMoment_add (f a) _ p (h a (Finset.mem_cons_self a s)) hs
    simpa only [Finset.sum_cons] using this

/-! ### Derived: linearity -/

lemma E_zero : ℰ.E (fun _ => (0 : ℝ)) = 0 :=
  ℰ.E_const 0

lemma E_neg {f : Ω → ℝ} (hf : ℰ.HasMoment f 1) :
    ℰ.E (fun ω => -f ω) = -ℰ.E f := by
  have := ℰ.E_smul (-1) f hf
  simpa only [neg_one_mul] using this

lemma E_sub {f g : Ω → ℝ} (hf : ℰ.HasMoment f 1) (hg : ℰ.HasMoment g 1) :
    ℰ.E (fun ω => f ω - g ω) = ℰ.E f - ℰ.E g := by
  have := ℰ.E_add f (fun ω => -g ω) hf (ℰ.hasMoment_neg hg)
  simpa only [sub_eq_add_neg, ℰ.E_neg hg] using this

lemma E_mul_const {f : Ω → ℝ} (c : ℝ) (hf : ℰ.HasMoment f 1) :
    ℰ.E (fun ω => f ω * c) = ℰ.E f * c := by
  have := ℰ.E_smul c f hf
  simpa only [mul_comm] using this

lemma E_add₃ {f g h : Ω → ℝ}
    (hf : ℰ.HasMoment f 1) (hg : ℰ.HasMoment g 1) (hh : ℰ.HasMoment h 1) :
    ℰ.E (fun ω => f ω + g ω + h ω) = ℰ.E f + ℰ.E g + ℰ.E h := by
  rw [ℰ.E_add _ h (ℰ.hasMoment_add f g 1 hf hg) hh, ℰ.E_add f g hf hg]

/-- `E` commutes with finite sums of `L¹` variables. -/
lemma E_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ)
    (h : ∀ i ∈ s, ℰ.HasMoment (f i) 1) :
    ℰ.E (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, ℰ.E (f i) := by
  induction s using Finset.cons_induction with
  | empty => simpa using ℰ.E_zero
  | cons a s ha ih =>
    have hs : ℰ.HasMoment (fun ω => ∑ i ∈ s, f i ω) 1 :=
      ℰ.hasMoment_sum s f 1 fun i hi => h i (Finset.mem_cons_of_mem hi)
    have := ℰ.E_add (f a) _ (h a (Finset.mem_cons_self a s)) hs
    simp only [Finset.sum_cons] at this ⊢
    rw [this, ih fun i hi => h i (Finset.mem_cons_of_mem hi)]

/-! ### Derived: order -/

/-- `E` is monotone on `L¹`. -/
lemma E_mono {f g : Ω → ℝ} (hf : ℰ.HasMoment f 1) (hg : ℰ.HasMoment g 1)
    (h : ∀ ω, f ω ≤ g ω) : ℰ.E f ≤ ℰ.E g := by
  have := ℰ.E_nonneg (fun ω => g ω - f ω) (ℰ.hasMoment_sub hg hf)
    fun ω => sub_nonneg.mpr (h ω)
  rw [ℰ.E_sub hg hf] at this
  linarith

/-- `|E f| ≤ E |f|`. -/
lemma abs_E_le_E_abs {f : Ω → ℝ} (hf : ℰ.HasMoment f 1) :
    |ℰ.E f| ≤ ℰ.E (fun ω => |f ω|) := by
  have ha := ℰ.hasMoment_abs f 1 hf
  refine abs_le.mpr ⟨?_, ℰ.E_mono hf ha fun ω => le_abs_self (f ω)⟩
  have := ℰ.E_mono (ℰ.hasMoment_neg hf) ha fun ω => neg_le_abs (f ω)
  rw [ℰ.E_neg hf] at this
  linarith

end Expectation

end Simple
