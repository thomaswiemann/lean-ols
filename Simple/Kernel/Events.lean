import Simple.Kernel.Expectation
import Mathlib.Algebra.Group.Indicator
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Tactic.Linarith

/-!
# Events: probability as the expectation of an indicator

`Pr A := E[𝟙_A]`. Nothing new is postulated: (E10) puts indicators in the
regularity class, and `0 ≤ P ≤ 1`, monotonicity, the union bound,
`P(A) ≤ P(A ∩ B) + P(Bᶜ)`, and Markov are derived from (E1)–(E11).
-/

open Finset

namespace Simple.Expectation

variable {Ω : Type*} (ℰ : Expectation Ω)

/-- The indicator of an event, as a real random variable. -/
noncomputable abbrev ind (A : Set Ω) : Ω → ℝ := A.indicator fun _ => (1 : ℝ)

open Classical in
lemma ind_apply (A : Set Ω) (ω : Ω) : ind A ω = if ω ∈ A then 1 else 0 :=
  Set.indicator_apply A (fun _ => (1 : ℝ)) ω

lemma ind_nonneg (A : Set Ω) (ω : Ω) : 0 ≤ ind A ω := by
  rw [ind_apply]; split_ifs <;> norm_num

lemma ind_le_one (A : Set Ω) (ω : Ω) : ind A ω ≤ 1 := by
  rw [ind_apply]; split_ifs <;> norm_num

lemma abs_ind_le_one (A : Set Ω) (ω : Ω) : |ind A ω| ≤ 1 := by
  rw [abs_of_nonneg (ind_nonneg A ω)]; exact ind_le_one A ω

lemma hasMoment_ind (A : Set Ω) (p : ℕ) : ℰ.HasMoment (ind A) p :=
  ℰ.hasMoment_of_bounded _ 1 p (abs_ind_le_one A)

/-- The probability of an event: `P(A) = E[𝟙_A]`. -/
noncomputable def Pr (A : Set Ω) : ℝ := ℰ.E (ind A)

lemma Pr_nonneg (A : Set Ω) : 0 ≤ ℰ.Pr A :=
  ℰ.E_nonneg _ (ℰ.hasMoment_ind A 1) (ind_nonneg A)

lemma Pr_le_one (A : Set Ω) : ℰ.Pr A ≤ 1 := by
  have := ℰ.E_mono (ℰ.hasMoment_ind A 1) (ℰ.hasMoment_const 1 1) (ind_le_one A)
  rwa [ℰ.E_const] at this

lemma Pr_univ : ℰ.Pr Set.univ = 1 := by
  have : ind (Set.univ : Set Ω) = fun _ => (1 : ℝ) := by
    funext ω; simp
  rw [Pr, this, ℰ.E_const]

lemma Pr_empty : ℰ.Pr (∅ : Set Ω) = 0 := by
  have : ind (∅ : Set Ω) = fun _ => (0 : ℝ) := by
    funext ω; simp
  rw [Pr, this, ℰ.E_zero]

lemma Pr_mono {A B : Set Ω} (h : A ⊆ B) : ℰ.Pr A ≤ ℰ.Pr B := by
  refine ℰ.E_mono (ℰ.hasMoment_ind A 1) (ℰ.hasMoment_ind B 1) fun ω => ?_
  rw [ind_apply, ind_apply]
  split_ifs with hA hB hB
  · exact le_rfl
  · exact absurd (h hA) hB
  · norm_num
  · exact le_rfl

/-- The union bound for two events. -/
lemma Pr_union_le (A B : Set Ω) : ℰ.Pr (A ∪ B) ≤ ℰ.Pr A + ℰ.Pr B := by
  unfold Pr
  rw [← ℰ.E_add _ _ (ℰ.hasMoment_ind A 1) (ℰ.hasMoment_ind B 1)]
  refine ℰ.E_mono (ℰ.hasMoment_ind _ 1)
    (ℰ.hasMoment_add _ _ 1 (ℰ.hasMoment_ind A 1) (ℰ.hasMoment_ind B 1)) fun ω => ?_
  simp only [ind_apply, Set.mem_union]
  by_cases hA : ω ∈ A <;> by_cases hB : ω ∈ B <;> simp [hA, hB]

/-- The union bound for finitely many events. -/
lemma Pr_biUnion_le {ι : Type*} (s : Finset ι) (A : ι → Set Ω) :
    ℰ.Pr (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, ℰ.Pr (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ℰ.Pr_empty]
  | insert a s ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (ℰ.Pr_union_le _ _).trans (add_le_add le_rfl ih)

lemma Pr_compl (A : Set Ω) : ℰ.Pr Aᶜ = 1 - ℰ.Pr A := by
  have : ind Aᶜ = fun ω => (1 : ℝ) - ind A ω := by
    funext ω
    simp only [ind_apply, Set.mem_compl_iff]
    by_cases h : ω ∈ A <;> simp [h]
  rw [Pr, this, ℰ.E_sub (ℰ.hasMoment_const 1 1) (ℰ.hasMoment_ind A 1), ℰ.E_const]
  rfl

/-- Total probability, in the form the papers use: `P(A) ≤ P(A ∩ B) + P(Bᶜ)`. -/
lemma Pr_le_Pr_inter_add_Pr_compl (A B : Set Ω) : ℰ.Pr A ≤ ℰ.Pr (A ∩ B) + ℰ.Pr Bᶜ := by
  refine (ℰ.Pr_mono ?_).trans (ℰ.Pr_union_le (A ∩ B) Bᶜ)
  intro ω hA
  by_cases hB : ω ∈ B
  · exact Or.inl ⟨hA, hB⟩
  · exact Or.inr hB

lemma Pr_inter_le_left (A B : Set Ω) : ℰ.Pr (A ∩ B) ≤ ℰ.Pr A :=
  ℰ.Pr_mono Set.inter_subset_left

lemma Pr_inter_le_right (A B : Set Ω) : ℰ.Pr (A ∩ B) ≤ ℰ.Pr B :=
  ℰ.Pr_mono Set.inter_subset_right

/-- Events that never happen have probability zero. -/
lemma Pr_eq_zero_of_forall_not {A : Set Ω} (h : ∀ ω, ω ∉ A) : ℰ.Pr A = 0 := by
  have : A = ∅ := Set.eq_empty_iff_forall_notMem.mpr h
  rw [this, ℰ.Pr_empty]

/-! ### Markov -/

/-- **Markov's inequality**: `P(|f| ≥ t) ≤ E|f| / t`. -/
theorem markov {f : Ω → ℝ} (hf : ℰ.HasMoment f 1) {t : ℝ} (ht : 0 < t) :
    ℰ.Pr {ω | t ≤ |f ω|} ≤ ℰ.E (fun ω => |f ω|) / t := by
  have key : ∀ ω, t * ind {ω | t ≤ |f ω|} ω ≤ |f ω| := by
    intro ω
    rw [ind_apply]
    split_ifs with h
    · simpa using h
    · simp [abs_nonneg]
  have := ℰ.E_mono (ℰ.hasMoment_smul t _ 1 (ℰ.hasMoment_ind _ 1)) (ℰ.hasMoment_abs f 1 hf) key
  rw [ℰ.E_smul t _ (ℰ.hasMoment_ind _ 1)] at this
  rw [le_div_iff₀ ht, Pr]
  linarith

end Simple.Expectation
