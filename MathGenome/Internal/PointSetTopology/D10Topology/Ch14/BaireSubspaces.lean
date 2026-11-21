import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.BaireSubspaces
import MathGenome.Internal.PointSetTopology.D10Topology.Ch14.CategoryInterface
import MathGenome.Internal.PointSetTopology.D10Topology.Ch14.MetricBaire
import MathGenome.Internal.PointSetTopology.D10Topology.Ch14.LCHBaire
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.CauchyBasics
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.SubspacesExhaustion

/-! Baire subspaces (paper.tex, d10:14:baire-subspaces).

The open and dense Gδ cases use the general library subspace theorems,
translated through the accepted countable-family category interface.
For an arbitrary Gδ subset A in the last two cases, its closure is a
closed complete metric or LCH subspace. A is a dense Gδ in that closure.
An explicit homeomorphism identifies the resulting iterated subspace with
the original subspace A. No complete metric on A itself is asserted. -/

open Set
universe u

namespace D10Topology.Ch14

theorem open_subspace_baire {X : Type u} [TopologicalSpace X]
    (hX : BaireIn X) (A : Set X) (hA : IsOpen A) : BaireIn A := by
  let : BaireSpace X := (baire_iff_library X).mp hX
  exact (baire_iff_library A).mpr hA.baireSpace

theorem dense_gdelta_subspace_baire {X : Type u} [TopologicalSpace X]
    (hX : BaireIn X) (A : Set X) (hA : IsGδ A) (hd : Dense A) : BaireIn A := by
  let : BaireSpace X := (baire_iff_library X).mp hX
  exact (baire_iff_library A).mpr (hA.baireSpace_of_dense hd)

/-- A Gδ subset is Baire whenever its closure, with its subspace topology,
is Baire. No Baire condition on the original ambient space is needed. -/
theorem gdelta_subspace_baire_of_baire_closure {X : Type u} [TopologicalSpace X]
    (A : Set X) (hA : IsGδ A) (hF : BaireIn (closure A)) : BaireIn A := by
  let : BaireSpace (closure A) := (baire_iff_library (closure A)).mp hF
  let D : Set (closure A) := Subtype.val ⁻¹' A
  have : BaireSpace D :=
    (hA.preimage continuous_subtype_val).baireSpace_of_dense
      (by simp [Subtype.dense_iff, inter_eq_right.mpr subset_closure])
  let e : D ≃ₜ A :=
    { toEquiv :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          invFun := fun x => ⟨⟨x.1, subset_closure x.2⟩, x.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact (baire_iff_library A).mpr e.baireSpace

theorem gdelta_subspace_complete_metric_baire {X : Type u} (d : MetricSpace X)
    (hc : Ch09.SequentiallyComplete d.toPseudoMetricSpace) (A : Set X)
    (hA : @IsGδ X (Ch09.metricTopology d.toPseudoMetricSpace) A) :
    @BaireIn A (TopologicalSpace.induced (Subtype.val : A → X)
      (Ch09.metricTopology d.toPseudoMetricSpace)) := by
  let := d
  apply gdelta_subspace_baire_of_baire_closure A hA
  exact complete_metric_baire
    (MetricSpace.induced (Subtype.val : closure A → X) Subtype.val_injective d)
    (Ch09.closed_subspace_complete d (closure A) hc isClosed_closure)

theorem gdelta_subspace_lch_baire {X : Type u} [TopologicalSpace X]
    (hX : Ch11.LCH X) (A : Set X) (hA : IsGδ A) : BaireIn A := by
  apply gdelta_subspace_baire_of_baire_closure A hA
  have hF : Ch11.LCH (closure A) := by
    let : T2Space X := hX.2
    exact ⟨Ch11.closed_subspace_locallyCompact hX.1 (closure A) isClosed_closure,
      inferInstance⟩
  exact lch_baire (closure A) hF

end D10Topology.Ch14
