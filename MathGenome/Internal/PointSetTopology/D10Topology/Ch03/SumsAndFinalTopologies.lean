import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.SumsAndFinalTopologies
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.EmbeddingsAndCharacteristicMaps

/-!
Disjoint sums and final topologies (paper.tex, d10:03:sum and d10:03:final).
`Sigma X` is the dependent sum of tagged points. The open characterizations
verify the source definitions before using the canonical library APIs.
All results allow empty spaces and empty families, and impose no separation
or surjectivity assumptions. Topology order is the reverse of open-family
inclusion, so the finest final topology is a supremum of coinduced ones.
-/

open Set Topology
universe u v w z

namespace D10Topology.Ch03

@[instance_reducible] def sumTopology {I : Type u} (X : I → Type v)
    [∀ i, TopologicalSpace (X i)] : TopologicalSpace (Sigma X) :=
  SumFinalData.sumTopology X

@[instance_reducible] def finalTopology {I : Type u} {X : I → Type v}
    [∀ i, TopologicalSpace (X i)] {Y : Type w}
    (q : ∀ i, X i → Y) : TopologicalSpace Y :=
  SumFinalData.finalTopology q

section Sums
variable {I : Type u} (X : I → Type v) [t : ∀ i, TopologicalSpace (X i)]

theorem sum_isOpen_iff (U : Set (Sigma X)) :
    IsOpen[sumTopology X] U ↔ ∀ i, IsOpen[t i] (Sigma.mk i ⁻¹' U) :=
  isOpen_sigma_iff

theorem sum_open_axioms : Ch01.OpenFamilyAxioms (Ch01.openSets (sumTopology X)) :=
  Ch01.open_axioms _

theorem sum_inclusion_embedding (i : I) :
    @IsEmbedding (X i) (Sigma X) (t i) (sumTopology X) (Sigma.mk i) :=
  IsEmbedding.sigmaMk

theorem sum_inclusion_clopen (i : I) :
    @IsClopen (Sigma X) (sumTopology X) (range (Sigma.mk i)) :=
  ⟨isClosed_range_sigmaMk, isOpen_range_sigmaMk⟩

theorem sum_continuous_iff {Y : Type w} [tY : TopologicalSpace Y] (f : Sigma X → Y) :
    Continuous[sumTopology X, tY] f ↔ ∀ i, Continuous (f ∘ Sigma.mk i) :=
  continuous_sigma_iff

end Sums

theorem sum_empty {I : Type u} [IsEmpty I] (X : I → Type v) : IsEmpty (Sigma X) :=
  ⟨fun x => isEmptyElim x.1⟩

section Final
variable {I : Type u} {X : I → Type v} [t : ∀ i, TopologicalSpace (X i)]
  {Y : Type w} (q : ∀ i, X i → Y)

theorem final_isOpen_iff (V : Set Y) :
    IsOpen[finalTopology q] V ↔ ∀ i, IsOpen[t i] (q i ⁻¹' V) := by
  unfold finalTopology SumFinalData.finalTopology
  rw [isOpen_iSup_iff]
  rfl

theorem final_open_axioms : Ch01.OpenFamilyAxioms (Ch01.openSets (finalTopology q)) :=
  Ch01.open_axioms _

theorem final_maps_continuous (i : I) : Continuous[t i, finalTopology q] (q i) := by
  apply continuous_def.mpr
  intro V hV
  exact (final_isOpen_iff q V).mp hV i

theorem final_le_iff (s : TopologicalSpace Y) :
    finalTopology q ≤ s ↔ ∀ i, Continuous[t i, s] (q i) := by
  unfold finalTopology SumFinalData.finalTopology
  simp only [iSup_le_iff, continuous_iff_coinduced_le]

theorem final_finest (s : TopologicalSpace Y) :
    (∀ i, Continuous[t i, s] (q i)) ↔
      Ch01.openSets s ⊆ Ch01.openSets (finalTopology q) :=
  (final_le_iff q s).symm

theorem final_continuous_iff {Z : Type z} [tZ : TopologicalSpace Z] (h : Y → Z) :
    Continuous[finalTopology q, tZ] h ↔ ∀ i, Continuous (h ∘ q i) := by
  unfold finalTopology SumFinalData.finalTopology
  rw [continuous_iSup_dom]
  exact forall_congr' fun _ => continuous_coinduced_dom

theorem final_empty_eq_discrete [IsEmpty I] : finalTopology q = ⊥ := by
  unfold finalTopology SumFinalData.finalTopology
  exact iSup_of_empty _

theorem final_empty_continuous [IsEmpty I] {Z : Type z} [tZ : TopologicalSpace Z]
    (h : Y → Z) : Continuous[finalTopology q, tZ] h := by
  rw [final_empty_eq_discrete q]
  exact continuous_bot

end Final

theorem sum_eq_final {I : Type u} (X : I → Type v) [∀ i, TopologicalSpace (X i)] :
    sumTopology X = finalTopology (fun i => (Sigma.mk i : X i → Sigma X)) := rfl

end D10Topology.Ch03
