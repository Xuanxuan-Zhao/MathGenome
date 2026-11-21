import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.TychonoffCube
import MathGenome.Internal.PointSetTopology.D10Topology.Ch10.EvaluationEmbedding
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationHeredityImages
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationProducts
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.MetricSeparation
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.UrysohnSeparation
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.CompactNormal

/-!
Cube representation, independent of compactification. Complete regularity
provides a coordinate equal to 1 at x and zero outside a prescribed open
neighborhood. Closed singletons give point separation. The general evaluation
criterion then applies, including when X is empty.
-/

open Set Topology
universe u v

namespace D10Topology.Ch10

abbrev Cube (ι : Type u) := Specs.D10Topology.Ch10.TychonoffCube.Cube ι
abbrev EvaluationIndex (X : Type u) [TopologicalSpace X] :=
  Specs.D10Topology.Ch10.TychonoffCube.EvaluationIndex X

def evaluationMap {X : Type u} [TopologicalSpace X] : X → Cube (EvaluationIndex X) :=
  fun x f => f x

theorem tychonoff_cube_evaluation_continuous {X : Type u} [TopologicalSpace X] :
    Continuous (evaluationMap (X := X)) :=
  evaluation_continuous (fun f : EvaluationIndex X => f) (fun f => f.continuous)

theorem tychonoff_evaluation_embedding {X : Type u} [TopologicalSpace X]
    (hX : Ch07.Tychonoff X) : IsEmbedding (evaluationMap (X := X)) := by
  let : T2Space X := hX.2
  apply evaluation_embedding_unitInterval (fun f : EvaluationIndex X => f)
    (fun f => f.continuous)
  · intro x y hxy
    obtain ⟨f, hf, hfx, hfy⟩ := hX.1 {y} isClosed_singleton x
      (by simpa only [mem_singleton_iff] using hxy)
    refine ⟨⟨f, hf⟩, ?_⟩
    change f x ≠ f y
    rw [hfx, hfy y (mem_singleton y)]
    exact one_ne_zero
  · intro U hU x hx
    obtain ⟨f, hf, hfx, hfU⟩ := hX.1 Uᶜ hU.isClosed_compl x (by simpa only [mem_compl_iff, not_not] using hx)
    refine ⟨⟨f, hf⟩, ?_, hfU⟩
    change 0 < (f x : ℝ)
    rw [hfx]
    exact zero_lt_one

theorem cube_tychonoff (ι : Type u) : Ch07.Tychonoff (Cube ι) := by
  have hI : Ch07.Tychonoff unitInterval :=
    Ch07.t4_implies_tychonoff unitInterval (Ch07.metric_t4 inferInstance)
  have hp := Ch07.product_tychonoff (fun _ : ι => inferInstance)
    (fun _ => hI)
  rw [Ch03.productTopology_eq_pi] at hp
  exact hp

theorem tychonoff_of_cube_embedding {X : Type u} {ι : Type v}
    [TopologicalSpace X] (e : X → Cube ι) (he : IsEmbedding e) :
    Ch07.Tychonoff X := by
  have hc := cube_tychonoff ι
  let : CompletelyRegularSpace (Cube ι) :=
    (Ch07.completelyRegular_iff_mathlib _).mp hc.1
  let : T2Space (Cube ι) := hc.2
  exact ⟨(Ch07.completelyRegular_iff_mathlib X).mpr he.isInducing.completelyRegularSpace,
    he.t2Space⟩

theorem tychonoff_iff_cube_embedding (X : Type u) [TopologicalSpace X] :
    Ch07.Tychonoff X ↔ ∃ (ι : Type u) (e : X → Cube ι), IsEmbedding e := by
  constructor
  · intro hX
    exact ⟨EvaluationIndex X, evaluationMap, tychonoff_evaluation_embedding hX⟩
  · rintro ⟨ι, e, he⟩
    exact tychonoff_of_cube_embedding e he

theorem empty_evaluation_embedding (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    IsEmbedding (evaluationMap (X := X)) := by
  apply tychonoff_evaluation_embedding
  exact ⟨fun _ _ x => isEmptyElim x, inferInstance⟩

theorem compact_hausdorff_tychonoff {X : Type u} [TopologicalSpace X] [T2Space X]
    (hX : Ch05.CoverCompact X) : Ch07.Tychonoff X :=
  Ch07.t4_implies_tychonoff X (Ch07.compact_hausdorff_t4 hX)

theorem compact_evaluation_image {X : Type u} [TopologicalSpace X]
    (hX : Ch05.CoverCompact X) :
    Ch05.SubspaceCompact (range (evaluationMap (X := X))) :=
  Ch05.continuous_compact_image evaluationMap hX tychonoff_cube_evaluation_continuous

theorem compact_hausdorff_evaluation_image {X : Type u} [TopologicalSpace X] [T2Space X]
    (hX : Ch05.CoverCompact X) :
    IsEmbedding (evaluationMap (X := X)) ∧
    Ch05.SubspaceCompact (range (evaluationMap (X := X))) ∧
    IsClosed (range (evaluationMap (X := X))) := by
  have hK := compact_evaluation_image hX
  exact ⟨tychonoff_evaluation_embedding (compact_hausdorff_tychonoff hX), hK,
    Ch05.compact_subset_closed _ hK⟩

end D10Topology.Ch10
