import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.LCHBaire
import MathGenome.Internal.PointSetTopology.D10Topology.Ch14.CategoryInterface
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.CompactShrinking
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
Baire for locally compact Hausdorff spaces (paper.tex, d10:14:baire-lch).

The accepted compact-shrinking interface upgrades the manuscript's single
compact neighborhood to Mathlib's local compactness under Hausdorffness.
The library's second Baire theorem constructs nested compact neighborhoods
and uses compact intersection; it assumes no metric. Finally the accepted
category interface identifies its Baire property with the manuscript's
countable-family formulation.
-/

universe u

namespace D10Topology.Ch14

theorem lch_baire (X : Type u) [TopologicalSpace X] (hX : Ch11.LCH X) :
    BaireIn X := by
  obtain ⟨hcompact, hhausdorff⟩ :=
    (Ch11.lch_iff_locallyCompactSpace_and_t2 X).mp hX
  letI : LocallyCompactSpace X := hcompact
  letI : T2Space X := hhausdorff
  exact (baire_iff_library X).mpr BaireSpace.of_t2Space_locallyCompactSpace

theorem compact_hausdorff_baire (X : Type u) [TopologicalSpace X]
    (hcompact : Specs.D10Topology.Ch05.Compactness.CoverCompact X)
    (hhausdorff : T2Space X) : BaireIn X := by
  letI : CompactSpace X := (Ch05.coverCompact_iff_compactSpace X).mp hcompact
  letI : T2Space X := hhausdorff
  apply lch_baire X
  exact (Ch11.lch_iff_locallyCompactSpace_and_t2 X).mpr ⟨inferInstance, hhausdorff⟩

end D10Topology.Ch14
