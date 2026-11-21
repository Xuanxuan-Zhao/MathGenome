import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.PartitionConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.ClosureSums

/-!
The source's interval-valued, closed-support definition of a partition of
unity and its exact bridge to Mathlib's real-valued partitions on `univ`.
All declarations allow arbitrary index types and non-Hausdorff or empty spaces.
The neighborhood sum theorem verifies the intended meaning of the sum.
-/

open Set
universe u v

namespace D10Topology.Ch15

abbrev SubordinatePartitionOfUnity {X : Type u} {I : Type v} [TopologicalSpace X]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1) : Prop :=
  Specs.D10Topology.Ch15.PartitionConventions.SubordinatePartitionOfUnity U φ

variable {X : Type u} {I : Type v} [TopologicalSpace X]

theorem partition_iff_mathlib (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1) :
    SubordinatePartitionOfUnity U φ ↔
      ∃ f : _root_.PartitionOfUnity I X, f.IsSubordinate U ∧
        ∀ i x, f i x = (φ i x : ℝ) := by
  constructor
  · intro h
    let f : _root_.PartitionOfUnity I X := {
      toFun := fun i => ⟨fun x => (φ i x : ℝ), (h.1 i).subtype_val⟩
      locallyFinite' := h.2.2.1.subset (fun _ => subset_closure)
      nonneg' := fun i x => (φ i x).property.1
      sum_eq_one' := fun x _ => h.2.2.2 x
      sum_le_one' := fun x => (h.2.2.2 x).le }
    exact ⟨f, h.2.1, fun _ _ => rfl⟩
  · rintro ⟨f, hsub, heq⟩
    have hφ : ∀ i, (fun x => (φ i x : ℝ)) = fun x => f i x :=
      fun i => funext (fun x => (heq i x).symm)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i
      apply continuous_induced_rng.mpr
      change Continuous (fun x => (φ i x : ℝ))
      rw [hφ i]
      exact (f i).continuous
    · intro i
      change tsupport (fun x => (φ i x : ℝ)) ⊆ U i
      rw [hφ i]
      exact hsub i
    · change LocallyFinite (fun i => tsupport (fun x => (φ i x : ℝ)))
      simp_rw [hφ]
      exact f.locallyFinite_tsupport
    · intro x
      simpa only [pointwiseSum, Specs.D10Topology.Ch15.ClosureSums.pointwiseSum, ← heq]
        using f.sum_eq_one (mem_univ x)

theorem mathlib_partition_properties (f : _root_.PartitionOfUnity I X) :
    (∀ i x, f i x ∈ Icc (0 : ℝ) 1) ∧
    (∀ i, tsupport (f i) = closure {x | f i x ≠ 0}) ∧
    LocallyFiniteFamily (fun i => closure {x | f i x ≠ 0}) ∧
    ∀ U : I → Set X,
      f.IsSubordinate U ↔ ∀ i, closure {x | f i x ≠ 0} ⊆ U i :=
  ⟨fun i x => ⟨f.nonneg i x, f.le_one i x⟩, fun _ => rfl,
    f.locallyFinite_tsupport, fun _ => Iff.rfl⟩

theorem partition_locally_sum (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1)
    (h : SubordinatePartitionOfUnity U φ) :
    ∀ x, ∃ N : Set X, IsOpen N ∧ x ∈ N ∧ ∃ s : Finset I,
      ∀ y ∈ N, (∀ i, i ∉ s → (φ i y : ℝ) = 0) ∧
        (∑ i ∈ s, (φ i y : ℝ)) = 1 := by
  intro x
  obtain ⟨N, hN, hx, s, hs⟩ := pointwiseSum_locally_eq_sum
    (fun i x => (φ i x : ℝ)) h.2.2.1 x
  refine ⟨N, hN, hx, s, fun y hy => ?_⟩
  exact ⟨(hs y hy).1, (hs y hy).2.symm.trans (h.2.2.2 y)⟩

theorem partition_sum_finset (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1)
    (h : SubordinatePartitionOfUnity U φ) (x : X) (s : Finset I)
    (hs : ∀ i, i ∉ s → (φ i x : ℝ) = 0) :
    (∑ i ∈ s, (φ i x : ℝ)) = 1 :=
  (pointwiseSum_eq_sum (fun i x => (φ i x : ℝ)) x s hs).symm.trans (h.2.2.2 x)

theorem partition_on_empty [IsEmpty X]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1) :
    SubordinatePartitionOfUnity U φ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact continuous_of_discreteTopology
  · intro i x
    exact isEmptyElim x
  · intro x
    exact isEmptyElim x
  · intro x
    exact isEmptyElim x

theorem partition_empty_index_iff [IsEmpty I]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1) :
    SubordinatePartitionOfUnity U φ ↔ IsEmpty X := by
  constructor
  · intro h
    refine ⟨fun x => ?_⟩
    obtain ⟨f, _, _⟩ := (partition_iff_mathlib U φ).mp h
    obtain ⟨i, _⟩ := f.exists_pos (mem_univ x)
    exact isEmptyElim i
  · intro h
    let := h
    exact partition_on_empty U φ

end D10Topology.Ch15
