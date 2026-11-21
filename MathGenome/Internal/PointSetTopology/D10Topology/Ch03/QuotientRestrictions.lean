import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch03.QuotientRestrictions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.QuotientMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Subspaces

/-!
Quotient restrictions and products of continuous open surjections,
paper.tex `d10:03:quotient-restriction` (Proposition 3.13).
Every restriction below is over a full inverse image, hence a saturated
subset. No claim about arbitrary domain restrictions is made.
-/

open Set Topology
universe u v w

namespace D10Topology.Ch03

section Restrictions
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

theorem quotient_restrictPreimage_of_isOpen (q : X → Y) (B : Set Y)
    (hq : QuotientMap q) (hA : IsOpen (q ⁻¹' B)) :
    QuotientMap (B.restrictPreimage q) := by
  have hf := (quotientMap_iff_mathlib q).mp hq
  exact (quotientMap_iff_mathlib _).mpr
    (hf.restrictPreimage_isOpen ((hq.2 B).mpr hA))

theorem quotient_restrictPreimage_of_isClosed (q : X → Y) (B : Set Y)
    (hq : QuotientMap q) (hA : IsClosed (q ⁻¹' B)) :
    QuotientMap (B.restrictPreimage q) := by
  have hf := (quotientMap_iff_mathlib q).mp hq
  have hB : IsClosed B := hf.isCoinducing.isClosed_preimage.mp hA
  apply (quotientMap_iff_mathlib _).mpr
  refine ⟨?_, hf.surjective.restrictPreimage B⟩
  apply IsCoinducing.of_isClosed_preimage_iff_isClosed
  intro V
  rw [hB.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
    ← hf.isCoinducing.isClosed_preimage,
    hA.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed,
    image_val_preimage_restrictPreimage]

/-- Images of relative opens are relative images of ambient opens.
The full-preimage domain is essential to this identity. -/
theorem openMap_restrictPreimage (q : X → Y) (B : Set Y) (ho : IsOpenMap q) :
    IsOpenMap (B.restrictPreimage q) := by
  intro V hV
  obtain ⟨U, hU, rfl⟩ := (subspace_open_iff (q ⁻¹' B) V).mp hV
  rw [image_restrictPreimage]
  exact (ho U hU).preimage continuous_subtype_val

theorem closedMap_restrictPreimage (q : X → Y) (B : Set Y) (hc : IsClosedMap q) :
    IsClosedMap (B.restrictPreimage q) := by
  intro V hV
  obtain ⟨F, hF, rfl⟩ := (subspace_closed_iff (q ⁻¹' B) V).mp hV
  rw [image_restrictPreimage]
  exact (hc F hF).preimage continuous_subtype_val

theorem open_quotient_restrictPreimage (q : X → Y) (B : Set Y)
    (hq : QuotientMap q) (ho : IsOpenMap q) :
    IsOpenMap (B.restrictPreimage q) ∧ QuotientMap (B.restrictPreimage q) := by
  have hro := openMap_restrictPreimage q B ho
  exact ⟨hro, continuous_open_surjection_quotient _
    (quotient_continuous q hq).restrictPreimage hro (hq.1.restrictPreimage B)⟩

theorem closed_quotient_restrictPreimage (q : X → Y) (B : Set Y)
    (hq : QuotientMap q) (hc : IsClosedMap q) :
    IsClosedMap (B.restrictPreimage q) ∧ QuotientMap (B.restrictPreimage q) := by
  have hrc := closedMap_restrictPreimage q B hc
  exact ⟨hrc, continuous_closed_surjection_quotient _
    (quotient_continuous q hq).restrictPreimage hrc (hq.1.restrictPreimage B)⟩

end Restrictions

/-- The coordinatewise map on arbitrary dependent products. The library's
product openness lemma needs surjectivity at all but finitely many coordinates;
the present hypotheses give it at every coordinate. Surjectivity of the product
uses choice, as allowed in F1. No inhabited factors or index type are assumed. -/
theorem product_open_surjections {I : Type u} {X : I → Type v} {Y : I → Type w}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (q : ∀ i, X i → Y i) (hc : ∀ i, Continuous (q i))
    (ho : ∀ i, IsOpenMap (q i)) (hs : ∀ i, Function.Surjective (q i)) :
    Continuous (Pi.map q) ∧ IsOpenMap (Pi.map q) ∧
      Function.Surjective (Pi.map q) ∧ QuotientMap (Pi.map q) := by
  have hpc : Continuous (Pi.map q) := Continuous.piMap hc
  have hpo : IsOpenMap (Pi.map q) := IsOpenMap.piMap ho (Filter.Eventually.of_forall hs)
  have hps : Function.Surjective (Pi.map q) := Function.Surjective.piMap hs
  exact ⟨hpc, hpo, hps, continuous_open_surjection_quotient _ hpc hpo hps⟩

end D10Topology.Ch03
