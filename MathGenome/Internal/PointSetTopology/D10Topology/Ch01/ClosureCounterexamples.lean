import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch01.ClosureCounterexamples
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ClosureCalculus
import MathGenome.Internal.PointSetTopology.D10Topology.Ch01.ElementaryTopologies
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.DenselyOrdered

/-! The counterexamples and the T1 accumulation test of
paper.tex, d10:01:closure-cautions. -/

open Set
open scoped Topology
universe u

namespace D10Topology.Ch01

theorem reciprocal_singletons_counterexample :
    (⋃ (n : ℕ) (_ : 1 ≤ n), closure ({1 / (n : ℝ)} : Set ℝ)) =
        {r : ℝ | ∃ n : ℕ, 1 ≤ n ∧ r = 1 / (n : ℝ)} ∧
      (0 : ℝ) ∈ closure (⋃ (n : ℕ) (_ : 1 ≤ n), ({1 / (n : ℝ)} : Set ℝ)) ∧
      (0 : ℝ) ∉ (⋃ (n : ℕ) (_ : 1 ≤ n), ({1 / (n : ℝ)} : Set ℝ)) ∧
      closure (⋃ (n : ℕ) (_ : 1 ≤ n), ({1 / (n : ℝ)} : Set ℝ)) ≠
        (⋃ (n : ℕ) (_ : 1 ≤ n), closure ({1 / (n : ℝ)} : Set ℝ)) := by
  have hclosed :
      (⋃ (n : ℕ) (_ : 1 ≤ n), closure ({1 / (n : ℝ)} : Set ℝ)) =
        (⋃ (n : ℕ) (_ : 1 ≤ n), ({1 / (n : ℝ)} : Set ℝ)) := by
    simp only [closure_singleton]
  have hz : (0 : ℝ) ∈ closure
      (⋃ (n : ℕ) (_ : 1 ≤ n), ({1 / (n : ℝ)} : Set ℝ)) := by
    apply mem_closure_of_tendsto
      (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ))
    exact (Filter.eventually_ge_atTop 1).mono fun n hn =>
      mem_iUnion.mpr ⟨n, mem_iUnion.mpr ⟨hn, mem_singleton _⟩⟩
  have hnz : (0 : ℝ) ∉
      (⋃ (n : ℕ) (_ : 1 ≤ n), ({1 / (n : ℝ)} : Set ℝ)) := by
    simp only [mem_iUnion, mem_singleton_iff, not_exists, one_div]
    intro n hn
    exact (inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))) ∘ Eq.symm
  refine ⟨?_, hz, hnz, ?_⟩
  · rw [hclosed]
    ext r
    simp only [mem_iUnion, mem_singleton_iff, mem_ofPred_eq, exists_prop]
  · intro heq
    exact hnz (hclosed ▸ heq ▸ hz)

theorem interval_intersection_counterexample :
    Ioo (-1 : ℝ) 0 ∩ Ioo 0 1 = ∅ ∧
      (0 : ℝ) ∈ closure (Ioo (-1 : ℝ) 0) ∩ closure (Ioo (0 : ℝ) 1) ∧
      closure (Ioo (-1 : ℝ) 0 ∩ Ioo 0 1) ≠
        closure (Ioo (-1 : ℝ) 0) ∩ closure (Ioo (0 : ℝ) 1) := by
  have he : Ioo (-1 : ℝ) 0 ∩ Ioo 0 1 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact (not_lt_of_gt hx.1.2) hx.2.1
  have hz : (0 : ℝ) ∈ closure (Ioo (-1 : ℝ) 0) ∩ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0),
      closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    norm_num
  refine ⟨he, hz, ?_⟩
  intro h
  rw [he, closure_empty] at h
  exact (h.symm ▸ hz : (0 : ℝ) ∈ (∅ : Set ℝ))

theorem indiscrete_accumulation_counterexample (a b : Bool) (hab : a ≠ b) :
    a ∈ @derivedSet Bool ⊤ {b} ∧
      (∀ N : Set Bool, Neighborhood ⊤ a N → (N ∩ ({b} \ {a})).Finite) ∧
      ¬ (∀ N : Set Bool, Neighborhood ⊤ a N → (N ∩ {b}).Infinite) := by
  have hbN : ∀ N : Set Bool, Neighborhood ⊤ a N → b ∈ N := by
    rintro N ⟨U, hU, haU, hUN⟩
    rcases (TopologicalSpace.isOpen_top_iff U).mp hU with h | h
    · exact (h ▸ haU : a ∈ (∅ : Set Bool)).elim
    · exact hUN (h ▸ mem_univ b)
  refine ⟨?_, fun N _ => N.toFinite.subset inter_subset_left, ?_⟩
  · rw [derivedSet_eq_neighborhood_test (t := (⊤ : TopologicalSpace Bool))]
    intro N hN
    exact ⟨b, hbN N hN, mem_singleton b, by simpa using hab.symm⟩
  · intro h
    exact (h univ (neighborhood_univ ⊤ a)) (univ ∩ {b}).toFinite

variable {X : Type u} [t : TopologicalSpace X]

theorem accumulation_of_infinite_punctured_neighborhoods (A : Set X) (x : X)
    (h : ∀ N : Set X, Neighborhood t x N → (N ∩ (A \ {x})).Infinite) :
    x ∈ derivedSet A := by
  rw [derivedSet_eq_neighborhood_test]
  exact fun N hN => (h N hN).nonempty

theorem accumulation_of_infinite_neighborhoods (A : Set X) (x : X)
    (h : ∀ N : Set X, Neighborhood t x N → (N ∩ A).Infinite) :
    x ∈ derivedSet A := by
  apply accumulation_of_infinite_punctured_neighborhoods
  intro N hN
  simpa only [inter_sdiff_assoc] using (h N hN).sdiff (finite_singleton x)

theorem accumulation_iff_infinite_punctured_neighborhoods [T1Space X]
    (A : Set X) (x : X) :
    x ∈ derivedSet A ↔
      ∀ N : Set X, Neighborhood t x N → (N ∩ (A \ {x})).Infinite := by
  constructor
  · intro hx N hN hfinite
    -- This is the sole separation-dependent step: finite unions of closed singletons.
    have finite_closed : ∀ F : Set X, F.Finite → IsClosed F := by
      intro F hF
      induction F, hF using Set.Finite.induction_on with
      | empty => exact isClosed_empty
      | @insert y F hy hF ih => exact (isClosed_singleton : IsClosed ({y} : Set X)).union ih
    have hclosed : IsClosed (N ∩ (A \ {x})) := finite_closed _ hfinite
    obtain ⟨U, hU, hxU, hUN⟩ := hN
    have hxnot : x ∉ N ∩ (A \ {x}) := fun h => h.2.2 (mem_singleton x)
    have hV : Neighborhood t x (U \ (N ∩ (A \ {x}))) :=
      ⟨_, hU.sdiff hclosed, ⟨hxU, hxnot⟩, Subset.rfl⟩
    rw [derivedSet_eq_neighborhood_test] at hx
    obtain ⟨y, hyV, hyA⟩ := hx _ hV
    exact hyV.2 ⟨hUN hyV.1, hyA⟩
  · exact accumulation_of_infinite_punctured_neighborhoods A x

theorem accumulation_iff_infinite_neighborhoods [T1Space X] (A : Set X) (x : X) :
    x ∈ derivedSet A ↔
      ∀ N : Set X, Neighborhood t x N → (N ∩ A).Infinite := by
  constructor
  · intro hx N hN
    exact ((accumulation_iff_infinite_punctured_neighborhoods A x).mp hx N hN).mono
      (inter_subset_inter_right N sdiff_subset)
  · exact accumulation_of_infinite_neighborhoods A x

end D10Topology.Ch01
