import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.PartitionUnity
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.PartitionConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.ParacompactNormal

/-!
Partitions of unity for paper.tex, d10:15:partition.
Normality supplies Mathlib's subordinate partition on the whole space, and
the accepted coefficient-preserving bridge gives the source's [0,1]-valued
partition with locally finite closed supports. In the converse, positive
loci form a locally finite open refinement; no separation hypothesis enters.
-/

open Set
universe u v

namespace D10Topology.Ch15

theorem exists_subordinate_partition {X : Type u} {I : Type v} [TopologicalSpace X]
    (hP : Paracompact X) (hH : Ch07.T2 X) (U : I → Set X)
    (ho : ∀ i, IsOpen (U i)) (hU : (⋃ i, U i) = univ) :
    ∃ φ : I → X → Icc (0 : ℝ) 1, SubordinatePartitionOfUnity U φ := by
  let : ParacompactSpace X := hP
  let : NormalSpace X := paracompact_hausdorff_normal X hP hH
  obtain ⟨f, hf⟩ := _root_.PartitionOfUnity.exists_isSubordinate isClosed_univ U ho
    (by rw [hU])
  let φ : I → X → Icc (0 : ℝ) 1 :=
    fun i x => ⟨f i x, f.nonneg i x, f.le_one i x⟩
  exact ⟨φ, (partition_iff_mathlib U φ).mpr ⟨f, hf, fun _ _ => rfl⟩⟩

/-- Positive loci of any source partition give an open refinement on exactly
the same indices, without assuming Hausdorffness. -/
theorem partition_positive_refinement {X : Type u} {I : Type v} [TopologicalSpace X]
    (U : I → Set X) (φ : I → X → Icc (0 : ℝ) 1)
    (h : SubordinatePartitionOfUnity U φ) :
    (∀ i, IsOpen {x | 0 < (φ i x : ℝ)}) ∧
    LocallyFiniteFamily (fun i => {x | 0 < (φ i x : ℝ)}) ∧
    (⋃ i, {x | 0 < (φ i x : ℝ)}) = univ ∧
    ∀ i, {x | 0 < (φ i x : ℝ)} ⊆ U i := by
  have hsupport : ∀ i, {x | 0 < (φ i x : ℝ)} ⊆
      closure {x | (φ i x : ℝ) ≠ 0} :=
    fun _ _ hx => subset_closure (ne_of_gt hx)
  refine ⟨fun i => isOpen_lt continuous_const (h.1 i).subtype_val,
    h.2.2.1.subset hsupport, ?_, fun i => (hsupport i).trans (h.2.1 i)⟩
  apply iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨f, _, heq⟩ := (partition_iff_mathlib U φ).mp h
  obtain ⟨i, hi⟩ := f.exists_pos (mem_univ x)
  refine ⟨i, ?_⟩
  change 0 < (φ i x : ℝ)
  rw [← heq i x]
  exact hi

/-- The converse of Theorem 15.10 applies to arbitrary topological spaces. -/
theorem paracompact_of_partitions (X : Type u) [TopologicalSpace X]
    (h : ∀ (I : Type u) (U : I → Set X),
      (∀ i, IsOpen (U i)) → (⋃ i, U i) = univ →
        ∃ φ : I → X → Icc (0 : ℝ) 1, SubordinatePartitionOfUnity U φ) :
    Paracompact X := by
  apply (paracompact_iff_open_cover_refinement X).mpr
  intro I U ho hU
  obtain ⟨φ, hφ⟩ := h I U ho hU
  obtain ⟨hVo, hVf, hVc, hVU⟩ := partition_positive_refinement U φ hφ
  exact ⟨I, fun i => {x | 0 < (φ i x : ℝ)}, hVo, hVf,
    hVc, fun i => ⟨i, hVU i⟩⟩

end D10Topology.Ch15
