import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.StoneCechConstruction
import MathGenome.Internal.PointSetTopology.D10Topology.Ch10.TychonoffCube
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.LocalCompactConventions

/-!
Stone--Cech as the closure of the canonical evaluation image, rather than
an alternative compactification model. Compactness is closed-subspace
compactness in the product of compact unit intervals. Restriction of the
Chapter 10 embedding to this closure retains its induced topology, and
its image is dense by the definition of closure. For the converse criterion,
a compact Hausdorff target is Tychonoff and its cube embedding composed
with the compactification embedding gives the cube criterion for X.
-/

open Set Topology
universe u v

namespace D10Topology.Ch11

abbrev betaSet (X : Type u) [TopologicalSpace X] :=
  Specs.D10Topology.Ch11.StoneCechConstruction.betaSet X

abbrev Beta (X : Type u) [TopologicalSpace X] : Type u :=
  Specs.D10Topology.Ch11.StoneCechConstruction.Beta X

def betaUnit {X : Type u} [TopologicalSpace X] : X → Beta X :=
  Specs.D10Topology.Ch11.StoneCechConstruction.betaUnit

@[simp] theorem betaUnit_val {X : Type u} [TopologicalSpace X] (x : X) :
    (betaUnit x).val = Ch10.evaluationMap x := rfl

@[simp] theorem betaUnit_coordinate {X : Type u} [TopologicalSpace X] (x : X)
    (f : Ch10.EvaluationIndex X) : (betaUnit x).val f = f x := rfl

theorem betaSet_closed (X : Type u) [TopologicalSpace X] : IsClosed (betaSet X) :=
  isClosed_closure

instance beta_compact (X : Type u) [TopologicalSpace X] : CompactSpace (Beta X) :=
  (isCompact_iff_compactSpace).mp (betaSet_closed X).isCompact

instance beta_hausdorff (X : Type u) [TopologicalSpace X] : T2Space (Beta X) :=
  inferInstance

theorem betaUnit_continuous {X : Type u} [TopologicalSpace X] :
    Continuous (betaUnit (X := X)) :=
  Ch10.tychonoff_cube_evaluation_continuous.subtype_mk _

theorem betaUnit_embedding {X : Type u} [TopologicalSpace X] (hX : Ch07.Tychonoff X) :
    IsEmbedding (betaUnit (X := X)) :=
  (Ch10.tychonoff_evaluation_embedding hX).codRestrict (betaSet X) _

theorem betaUnit_dense {X : Type u} [TopologicalSpace X] :
    DenseRange (betaUnit (X := X)) := by
  change Dense (range (betaUnit (X := X)))
  rw [Subtype.dense_iff]
  have h : Subtype.val '' range (betaUnit (X := X)) =
      range (Ch10.evaluationMap (X := X)) := by
    rw [← range_comp]
    rfl
  rw [h]
  exact subset_rfl

theorem beta_hausdorffCompactification {X : Type u} [TopologicalSpace X]
    (hX : Ch07.Tychonoff X) : HausdorffCompactification (betaUnit (X := X)) :=
  ⟨betaUnit_embedding hX, betaUnit_dense, inferInstance, inferInstance⟩

theorem tychonoff_of_hausdorffCompactification {X : Type u} {K : Type v}
    [TopologicalSpace X] [TopologicalSpace K] (i : X → K)
    (hi : HausdorffCompactification i) : Ch07.Tychonoff X := by
  let : CompactSpace K := hi.2.2.1
  let : T2Space K := hi.2.2.2
  have hK : Ch07.Tychonoff K := Ch10.compact_hausdorff_tychonoff
    ((Ch05.coverCompact_iff_compactSpace K).mpr inferInstance)
  exact Ch10.tychonoff_of_cube_embedding (Ch10.evaluationMap ∘ i)
    ((Ch10.tychonoff_evaluation_embedding hK).comp hi.1)

theorem has_hausdorffCompactification_iff_tychonoff (X : Type u) [TopologicalSpace X] :
    (∃ (K : Type u) (_ : TopologicalSpace K) (i : X → K),
      HausdorffCompactification i) ↔ Ch07.Tychonoff X := by
  constructor
  · rintro ⟨K, tK, i, hi⟩
    exact tychonoff_of_hausdorffCompactification i hi
  · intro hX
    exact ⟨Beta X, inferInstance, betaUnit, beta_hausdorffCompactification hX⟩

theorem empty_betaSet (X : Type u) [TopologicalSpace X] [IsEmpty X] : betaSet X = ∅ := by
  simp only [betaSet, Specs.D10Topology.Ch11.StoneCechConstruction.betaSet,
    range_eq_empty, closure_empty]

theorem empty_beta (X : Type u) [TopologicalSpace X] [IsEmpty X] : IsEmpty (Beta X) :=
  isEmpty_coe_sort.mpr (empty_betaSet X)

end D10Topology.Ch11
