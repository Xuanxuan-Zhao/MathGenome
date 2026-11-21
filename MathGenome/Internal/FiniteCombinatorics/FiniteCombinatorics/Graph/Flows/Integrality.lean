import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.ResidualOptimality
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Graph.Flows.Integrality
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! Integral augmentation and W48. The termination argument uses the integer
increase in value and a finite cut-capacity bound, never termination for real
capacities. All original arc identities are retained. -/

open scoped BigOperators Classical
universe u v
namespace FiniteCombinatorics.Graph.Flows
open FiniteCombinatorics.Directed
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

namespace Integrality

variable (N : Network V A)

/-- Each residual capacity is an integer when capacities and loads are. -/
theorem residual_capacity_integer
    (hc : ∀ a, ∃ c : ℕ, N.capacity a = (c : ℝ))
    {f : A → ℝ} (hf : ∀ a, ∃ z : ℤ, f a = (z : ℝ))
    (b : N.ResidualArc f) : ∃ z : ℤ, ResidualSpec.capacity N f b.val = (z : ℝ) := by
  obtain ⟨c, hc⟩ := hc b.original
  obtain ⟨z, hz⟩ := hf b.original
  change ∃ k : ℤ, (if b.forward then N.capacity b.original - f b.original
    else f b.original) = (k : ℝ)
  cases hb : b.forward
  · exact ⟨z, by simp [hz]⟩
  · exact ⟨(c : ℤ) - z, by simp [hc, hz]⟩

/-- Signed adjustments are integers, also for backward copies. -/
theorem adjustment_integer {f : A → ℝ} (e : ℤ)
    (l : List (N.ResidualArc f)) (a : A) :
    ∃ z : ℤ, ResidualSpec.adjustment (e : ℝ) l a = (z : ℝ) := by
  induction l with
  | nil => exact ⟨0, by simp [ResidualSpec.adjustment]⟩
  | cons b l ih =>
    obtain ⟨z, hz⟩ := ih
    have hstep : ∃ k : ℤ, ResidualSpec.step (e : ℝ) b a = (k : ℝ) := by
      by_cases ha : a = b.original
      · cases hb : b.forward
        · exact ⟨-e, by simp [ResidualSpec.step, ha, hb]⟩
        · exact ⟨e, by simp [ResidualSpec.step, ha, hb]⟩
      · exact ⟨0, by simp [ResidualSpec.step, ha]⟩
    obtain ⟨k, hk⟩ := hstep
    refine ⟨k + z, ?_⟩
    change ResidualSpec.step (e : ℝ) b a + ResidualSpec.adjustment (e : ℝ) l a = _
    simp [hk, hz]

/-- Every positive integral bottleneck is at least one, and augmentation
preserves integral loads. Feasibility is supplied by the augmentation theorem. -/
theorem augment_integer
    (hc : ∀ a, ∃ c : ℕ, N.capacity a = (c : ℝ))
    {f : A → ℝ} (hf : ∀ a, ∃ z : ℤ, f a = (z : ℝ))
    {x y : V} (p : Walk (N.residualGraph f) x y) {ε : ℝ}
    (hε : ResidualSpec.bottleneck N f p ε) :
    1 ≤ ε ∧ ∀ a, ∃ z : ℤ, N.augment f p ε a = (z : ℝ) := by
  obtain ⟨b, _, hb⟩ := hε.2.2
  obtain ⟨e, he⟩ := residual_capacity_integer N hc hf b
  have he' : ε = (e : ℝ) := hb.trans he
  have hepos : (0 : ℤ) < e := by exact_mod_cast (he' ▸ hε.1)
  constructor
  · rw [he']
    exact_mod_cast (show (1 : ℤ) ≤ e from hepos)
  · intro a
    obtain ⟨z, hz⟩ := hf a
    obtain ⟨k, hk⟩ := adjustment_integer N e p.arcs a
    refine ⟨z + k, ?_⟩
    change f a + ResidualSpec.adjustment ε p.arcs a = _
    rw [he', hz, hk, Int.cast_add]

/-- Integral augmentations cannot continue indefinitely: starting at zero,
absence of an integral optimum would yield value at least n for every natural
n, contradicting weak duality for the fixed finite cut {source}. -/
theorem exists_integral_maximum
    (hc : ∀ a, ∃ c : ℕ, N.capacity a = (c : ℝ)) :
    ∃ f : A → ℝ, N.IsMaximum f ∧ (∀ a, ∃ z : ℤ, f a = (z : ℝ)) := by
  by_contra h
  have improve (f : A → ℝ) (hf : N.Feasible f)
      (hi : ∀ a, ∃ z : ℤ, f a = (z : ℝ)) :
      ∃ g : A → ℝ, N.Feasible g ∧ (∀ a, ∃ z : ℤ, g a = (z : ℝ)) ∧
        N.value f + 1 ≤ N.value g := by
    have hn : ¬ N.IsMaximum f := fun hm => h ⟨f, hm, hi⟩
    have hw : Nonempty (Walk (N.residualGraph f) N.source N.sink) := by
      by_contra hw
      exact hn ((N.maximum_iff_no_residual_walk f hf).mpr hw)
    obtain ⟨p, _, _, _, ε, hε, hg, hv⟩ := Network.residual_augmentation N f hf hw
    obtain ⟨he, hi'⟩ := augment_integer N hc hi p hε
    refine ⟨N.augment f p ε, hg, hi', ?_⟩
    change N.value (N.augment f p ε) = N.value f + ε at hv
    rw [hv]
    exact add_le_add_right he _
  have unbounded (n : ℕ) : ∃ f : A → ℝ, N.Feasible f ∧
      (∀ a, ∃ z : ℤ, f a = (z : ℝ)) ∧ (n : ℝ) ≤ N.value f := by
    induction n with
    | zero => exact ⟨fun _ => 0, N.zero_feasible, fun _ => ⟨0, by simp⟩,
        by simpa only [Nat.cast_zero, N.value_zero] using (le_refl (0 : ℝ))⟩
    | succ n ih =>
      obtain ⟨f, hf, hi, hv⟩ := ih
      obtain ⟨g, hg, hi', hv'⟩ := improve f hf hi
      refine ⟨g, hg, hi', ?_⟩
      push_cast
      linarith
  have hcut : N.IsCut {N.source} := by
    exact ⟨Set.mem_singleton _, fun ht => N.source_ne_sink (Set.mem_singleton_iff.mp ht).symm⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (N.cutCapacity {N.source})
  obtain ⟨f, hf, _, hv⟩ := unbounded n
  have hub := N.weak_duality f {N.source} hf hcut
  exact (not_lt_of_ge (hv.trans hub)) hn

end Integrality

/-- W48: an integral maximum among real flows and an equal minimum cut. -/
theorem Network.integral_max_flow_min_cut : IntegralitySpec.integral_max_flow_min_cut.{u,v} := by
  intro V A _ _ N hc
  obtain ⟨f, hm, hi⟩ := Integrality.exists_integral_maximum N hc
  have hnat (a : A) : ∃ n : ℕ, f a = (n : ℝ) := by
    obtain ⟨z, hz⟩ := hi a
    have hnonneg : (0 : ℤ) ≤ z := by exact_mod_cast (hz ▸ (hm.1.1 a).1)
    refine ⟨z.toNat, ?_⟩
    rw [hz]
    exact_mod_cast (Int.toNat_of_nonneg hnonneg).symm
  choose g hg using hnat
  have hfg : f = fun a => (g a : ℝ) := funext hg
  have hw := (N.maximum_iff_no_residual_walk f hm.1).mp hm
  obtain ⟨hS, _, _, heq⟩ := N.residual_reachable_cut f hm.1 hw
  refine ⟨g, N.residualReachableSet f, ?_, hS, ?_, ?_, ?_⟩
  · exact hfg ▸ hm.1
  · intro k hk
    exact hfg ▸ hm.2 k hk
  · intro T hT
    exact heq.trans_le (N.weak_duality f T hm.1 hT)
  · exact hfg ▸ heq.symm

end FiniteCombinatorics.Graph.Flows
