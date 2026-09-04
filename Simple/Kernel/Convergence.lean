import Simple.Kernel.Events
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Convergence in probability, defined

`TendstoInProb ℰ X c` — `Xₙ →p c` when the `n`-th observation is drawn under
the law `ℰ n` — is *defined*: for every neighbourhood `U` of `c`,
`Pr_n {Xₙ ∉ U} → 0`. A fixed law is the constant sequence. With the definition
in place, continuous mapping (T3), joint convergence (T5), (T5'), the
vanishing-event rule (T6), and Markov's route to `→p` are theorems, proved from
the union bound and monotonicity of `Pr`.

Neighbourhoods rather than a metric, so that `Matrix` (which carries the product
topology but no norm instance) is covered; the metric form is
`tendstoInProb_iff_dist`.
-/

open Filter Topology Set

namespace Simple

variable {Ω : Type*}

/-- `Xₙ →p c` under the law sequence `ℰ`. -/
def TendstoInProb (ℰ : ℕ → Expectation Ω) {β : Type*} [TopologicalSpace β]
    (X : ℕ → Ω → β) (c : β) : Prop :=
  ∀ U ∈ 𝓝 c, Tendsto (fun n => (ℰ n).Pr {ω | X n ω ∉ U}) atTop (𝓝 0)

/-- A nonnegative sequence dominated by one tending to zero tends to zero. -/
lemma tendsto_zero_of_le {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hle : ∀ n, f n ≤ g n)
    (hg : Tendsto g atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hg hf hle

/-- Same, with eventual domination. -/
lemma tendsto_zero_of_eventually_le {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (hle : ∀ᶠ n in atTop, f n ≤ g n) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg
    (Eventually.of_forall hf) hle

/-- A nonnegative sequence that is eventually below every positive level tends to zero. -/
lemma tendsto_zero_of_forall_eventually_le {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : ∀ η > 0, ∀ᶠ n in atTop, f n ≤ η) : Tendsto f atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := (h (ε / 2) (by positivity)).exists_forall_of_atTop
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hf n)]
  linarith [hN n hn]

section Basic

variable (ℰ : ℕ → Expectation Ω) {β : Type*} [TopologicalSpace β]

/-- Constants converge in probability to themselves. -/
theorem tendstoInProb_const (c : β) : TendstoInProb ℰ (fun _ _ => c) c := by
  intro U hU
  have : ∀ n, (ℰ n).Pr {ω : Ω | c ∉ U} = 0 := fun n =>
    (ℰ n).Pr_eq_zero_of_forall_not fun ω h => h (mem_of_mem_nhds hU)
  simp only [this]
  exact tendsto_const_nhds

/-- Convergence in probability depends only on the sequence pointwise. -/
theorem TendstoInProb.congr {X Y : ℕ → Ω → β} {c : β} (h : TendstoInProb ℰ X c)
    (e : ∀ n ω, X n ω = Y n ω) : TendstoInProb ℰ Y c := by
  have : Y = X := by funext n ω; exact (e n ω).symm
  rw [this]; exact h

/-- **(T3) Continuous mapping**, now a theorem: `Xₙ →p c` and `h` continuous at `c` give
`h(Xₙ) →p h(c)`. -/
theorem cmt {γ : Type*} [TopologicalSpace γ] (X : ℕ → Ω → β) (c : β) (h : β → γ)
    (hh : ContinuousAt h c) (hX : TendstoInProb ℰ X c) :
    TendstoInProb ℰ (fun n ω => h (X n ω)) (h c) := by
  intro U hU
  exact hX _ (hh.preimage_mem_nhds hU)

/-- **(T5) Joint convergence in a product of types**, now a theorem, and for any index
type: a neighbourhood of `c` in the product topology contains a finite cylinder, and the union
bound over its finitely many coordinates finishes. -/
theorem tendstoInProb_pi {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    (X : ℕ → Ω → ∀ i, π i) (c : ∀ i, π i)
    (h : ∀ i, TendstoInProb ℰ (fun n ω => X n ω i) (c i)) : TendstoInProb ℰ X c := by
  intro U hU
  rw [nhds_pi] at hU
  obtain ⟨I, t, ht, hIU⟩ := Filter.mem_pi'.mp hU
  refine tendsto_zero_of_le (g := fun n => ∑ i ∈ I, (ℰ n).Pr {ω | X n ω i ∉ t i})
    (fun n => (ℰ n).Pr_nonneg _) (fun n => ?_) ?_
  · refine ((ℰ n).Pr_mono fun ω hω => ?_).trans
      ((ℰ n).Pr_biUnion_le I fun i => {ω | X n ω i ∉ t i})
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hω ⊢
    by_contra hcon
    push Not at hcon
    exact hω (hIU fun i hi => hcon i hi)
  · have : Tendsto (fun n => ∑ i ∈ I, (ℰ n).Pr {ω | X n ω i ∉ t i}) atTop
        (𝓝 (∑ i ∈ I, (0 : ℝ))) :=
      tendsto_finsetSum I fun i _ => h i (t i) (ht i)
    simpa using this

/-- **(T5') Joint convergence of a pair**, now a theorem. -/
theorem tendstoInProb_prod {γ : Type*} [TopologicalSpace γ] (X : ℕ → Ω → β) (c : β)
    (X' : ℕ → Ω → γ) (c' : γ) (hX : TendstoInProb ℰ X c) (hX' : TendstoInProb ℰ X' c') :
    TendstoInProb ℰ (fun n ω => (X n ω, X' n ω)) (c, c') := by
  intro U hU
  rw [nhds_prod_eq] at hU
  obtain ⟨t₁, ht₁, t₂, ht₂, hU⟩ := Filter.mem_prod_iff.mp hU
  refine tendsto_zero_of_le
    (g := fun n => (ℰ n).Pr {ω | X n ω ∉ t₁} + (ℰ n).Pr {ω | X' n ω ∉ t₂})
    (fun n => (ℰ n).Pr_nonneg _) (fun n => ?_) ?_
  · refine ((ℰ n).Pr_mono fun ω hω => ?_).trans ((ℰ n).Pr_union_le _ _)
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
    by_contra hcon
    push Not at hcon
    exact hω (hU ⟨hcon.1, hcon.2⟩)
  · simpa using (hX t₁ ht₁).add (hX' t₂ ht₂)

/-- (T3) in two arguments. -/
theorem cmt₂ {γ δ : Type*} [TopologicalSpace γ] [TopologicalSpace δ]
    (X : ℕ → Ω → β) (c : β) (X' : ℕ → Ω → γ) (c' : γ) (h : β → γ → δ)
    (hh : ContinuousAt (fun p : β × γ => h p.1 p.2) (c, c'))
    (hX : TendstoInProb ℰ X c) (hX' : TendstoInProb ℰ X' c') :
    TendstoInProb ℰ (fun n ω => h (X n ω) (X' n ω)) (h c c') :=
  cmt ℰ (fun n ω => (X n ω, X' n ω)) (c, c') (fun p => h p.1 p.2) hh
    (tendstoInProb_prod ℰ X c X' c' hX hX')

/-- **(T6) Vanishing events**, now a theorem: if `Dₙ →p d` and `c < d`, a sequence that is
nonzero only where `Dₙ < c` tends to `0` in probability. -/
theorem tendstoInProb_of_vanishing [Zero β] (R : ℕ → Ω → β) (D : ℕ → Ω → ℝ) (d c : ℝ)
    (hD : TendstoInProb ℰ D d) (hcd : c < d) (h : ∀ n ω, R n ω ≠ 0 → D n ω < c) :
    TendstoInProb ℰ R 0 := by
  intro U hU
  have hIoi : Set.Ioi c ∈ 𝓝 d := Ioi_mem_nhds hcd
  refine tendsto_zero_of_le (fun n => (ℰ n).Pr_nonneg _) (fun n => (ℰ n).Pr_mono ?_) (hD _ hIoi)
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  intro hlt
  rw [Set.mem_Ioi] at hlt
  by_cases hR : R n ω = 0
  · exact hω (by rw [hR]; exact mem_of_mem_nhds hU)
  · exact absurd (h n ω hR) (not_lt.mpr hlt.le)

/-- Sequences that agree on events of probability approaching one have the same limits
in probability. -/
theorem tendstoInProb_of_eventuallyEq {X Y : ℕ → Ω → β} {c : β} (A : ℕ → Set Ω)
    (hA : Tendsto (fun n => (ℰ n).Pr (A n)ᶜ) atTop (𝓝 0))
    (heq : ∀ n ω, ω ∈ A n → X n ω = Y n ω) (hX : TendstoInProb ℰ X c) :
    TendstoInProb ℰ Y c := by
  intro U hU
  have hsum := (hX U hU).add hA
  rw [add_zero] at hsum
  refine tendsto_zero_of_le
    (g := fun n => (ℰ n).Pr {ω | X n ω ∉ U} + (ℰ n).Pr (A n)ᶜ)
    (fun n => (ℰ n).Pr_nonneg _) (fun n => ?_) hsum
  refine ((ℰ n).Pr_le_Pr_inter_add_Pr_compl _ (A n)).trans
    (add_le_add ((ℰ n).Pr_mono ?_) le_rfl)
  rintro ω ⟨hω, hωA⟩
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rwa [heq n ω hωA]

end Basic

section Metric

variable (ℰ : ℕ → Expectation Ω) {β : Type*} [PseudoMetricSpace β]

/-- The metric form of the definition. -/
theorem tendstoInProb_iff_dist (X : ℕ → Ω → β) (c : β) :
    TendstoInProb ℰ X c ↔
      ∀ ε > 0, Tendsto (fun n => (ℰ n).Pr {ω | ε ≤ dist (X n ω) c}) atTop (𝓝 0) := by
  constructor
  · intro h ε hε
    have hb := h (Metric.ball c ε) (Metric.ball_mem_nhds c hε)
    refine tendsto_zero_of_le (fun n => (ℰ n).Pr_nonneg _) (fun n => (ℰ n).Pr_mono ?_) hb
    intro ω hω
    simpa [Metric.mem_ball, not_lt] using hω
  · intro h U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
    refine tendsto_zero_of_le (fun n => (ℰ n).Pr_nonneg _) (fun n => (ℰ n).Pr_mono ?_) (h ε hε)
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    by_contra hlt
    exact hω (hball (Metric.mem_ball.mpr (not_le.mp hlt)))

/-- **Markov's route to `→p`**: `E|Xₙ| → 0` implies `Xₙ →p 0`. -/
theorem tendstoInProb_zero_of_E_abs (X : ℕ → Ω → ℝ) (hX : ∀ n, (ℰ n).HasMoment (X n) 1)
    (h : Tendsto (fun n => (ℰ n).E (fun ω => |X n ω|)) atTop (𝓝 0)) :
    TendstoInProb ℰ X 0 := by
  rw [tendstoInProb_iff_dist]
  intro ε hε
  have hd := h.div_const ε
  rw [zero_div] at hd
  refine tendsto_zero_of_le (fun n => (ℰ n).Pr_nonneg _) (fun n => ?_) hd
  have := (ℰ n).markov (hX n) hε
  simpa [Real.dist_eq] using this

end Metric

/-! ### The fixed-law case -/

namespace Expectation

variable (ℰ : Expectation Ω) {β : Type*} [TopologicalSpace β]

/-- `Xₙ →p c` under one law. -/
abbrev TendstoInProb (X : ℕ → Ω → β) (c : β) : Prop := Simple.TendstoInProb (fun _ => ℰ) X c

theorem tendstoInProb_const (c : β) : ℰ.TendstoInProb (fun _ _ => c) c :=
  Simple.tendstoInProb_const _ c

theorem cmt {γ : Type*} [TopologicalSpace γ] (X : ℕ → Ω → β) (c : β) (h : β → γ)
    (hh : ContinuousAt h c) (hX : ℰ.TendstoInProb X c) :
    ℰ.TendstoInProb (fun n ω => h (X n ω)) (h c) :=
  Simple.cmt _ X c h hh hX

theorem tendstoInProb_pi {ι : Type*} {π : ι → Type*} [∀ i, TopologicalSpace (π i)]
    (X : ℕ → Ω → ∀ i, π i) (c : ∀ i, π i)
    (h : ∀ i, ℰ.TendstoInProb (fun n ω => X n ω i) (c i)) : ℰ.TendstoInProb X c :=
  Simple.tendstoInProb_pi _ X c h

theorem tendstoInProb_prod {γ : Type*} [TopologicalSpace γ] (X : ℕ → Ω → β) (c : β)
    (X' : ℕ → Ω → γ) (c' : γ) (hX : ℰ.TendstoInProb X c) (hX' : ℰ.TendstoInProb X' c') :
    ℰ.TendstoInProb (fun n ω => (X n ω, X' n ω)) (c, c') :=
  Simple.tendstoInProb_prod _ X c X' c' hX hX'

theorem cmt₂ {γ δ : Type*} [TopologicalSpace γ] [TopologicalSpace δ]
    (X : ℕ → Ω → β) (c : β) (X' : ℕ → Ω → γ) (c' : γ) (h : β → γ → δ)
    (hh : ContinuousAt (fun p : β × γ => h p.1 p.2) (c, c'))
    (hX : ℰ.TendstoInProb X c) (hX' : ℰ.TendstoInProb X' c') :
    ℰ.TendstoInProb (fun n ω => h (X n ω) (X' n ω)) (h c c') :=
  Simple.cmt₂ _ X c X' c' h hh hX hX'

theorem tendstoInProb_of_vanishing [Zero β] (R : ℕ → Ω → β) (D : ℕ → Ω → ℝ) (d c : ℝ)
    (hD : ℰ.TendstoInProb D d) (hcd : c < d) (h : ∀ n ω, R n ω ≠ 0 → D n ω < c) :
    ℰ.TendstoInProb R 0 :=
  Simple.tendstoInProb_of_vanishing _ R D d c hD hcd h

theorem tendstoInProb_zero_of_E_abs (X : ℕ → Ω → ℝ) (hX : ∀ n, ℰ.HasMoment (X n) 1)
    (h : Tendsto (fun n => ℰ.E (fun ω => |X n ω|)) atTop (𝓝 0)) : ℰ.TendstoInProb X 0 :=
  Simple.tendstoInProb_zero_of_E_abs _ X hX h

end Expectation

end Simple
