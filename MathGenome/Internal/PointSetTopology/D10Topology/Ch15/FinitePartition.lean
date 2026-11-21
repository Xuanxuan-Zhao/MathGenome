import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.FinitePartition
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.PartitionConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions

/-!
Finite partitions of unity on normal spaces, without T1 or paracompactness.
A finite indexed cover is locally finite. Mathlib's normal-space construction
on the closed set `univ` therefore applies; the accepted coefficient-preserving
bridge gives the source's interval-valued maps and closed-support condition.
-/

open Set
universe u v

namespace D10Topology.Ch15

theorem finite_subordinate_partition {X : Type u} {I : Type v}
    [TopologicalSpace X] [Finite I] (hN : Ch07.Normal X)
    (U : I → Set X) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ φ : I → X → Icc (0 : ℝ) 1, SubordinatePartitionOfUnity U φ := by
  let : NormalSpace X := hN
  have hcov : (univ : Set X) ⊆ ⋃ i, U i := fun x _ => mem_iUnion.mpr (hcover x)
  obtain ⟨f, hf⟩ := _root_.PartitionOfUnity.exists_isSubordinate_of_locallyFinite
    isClosed_univ U hU (locallyFinite_of_finite U) hcov
  let φ : I → X → Icc (0 : ℝ) 1 :=
    fun i x => ⟨f i x, f.nonneg i x, f.le_one i x⟩
  exact ⟨φ, (partition_iff_mathlib U φ).mpr ⟨f, hf, fun _ _ => rfl⟩⟩

theorem empty_index_partition {X : Type u} {I : Type v}
    [TopologicalSpace X] [IsEmpty I] (U : I → Set X)
    (hcover : ∀ x, ∃ i, x ∈ U i) :
    IsEmpty X ∧ ∃ φ : I → X → Icc (0 : ℝ) 1,
      SubordinatePartitionOfUnity U φ := by
  have hempty : IsEmpty X := ⟨fun x => by
    obtain ⟨i, _⟩ := hcover x
    exact isEmptyElim i⟩
  let := hempty
  let φ : I → X → Icc (0 : ℝ) 1 := fun i => isEmptyElim i
  exact ⟨hempty, φ, partition_on_empty U φ⟩

end D10Topology.Ch15
