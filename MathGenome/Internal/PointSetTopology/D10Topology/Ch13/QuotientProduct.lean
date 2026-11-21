import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.QuotientProduct
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.QuotientMaps
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.EvaluationParameter

/-! The LCH quotient-product theorem (paper.tex, d10:13:quotient-product).

Use the quotient mapping test. A map out of X × B whose pullback to
X × A is continuous is itself continuous: curry along the locally compact
factor X, descend the resulting family through q, then uncurry.
Mathlib's continuous_lift_prod_right implements this argument for arbitrary
target spaces. The source LCH convention supplies its local compactness
instance via the upstream Hausdorff compact-neighborhood bridge.
-/

universe u v w

namespace D10Topology.Ch13

theorem quotient_product_lch {X : Type u} {A : Type v} {B : Type w}
    [TopologicalSpace X] [TopologicalSpace A] [TopologicalSpace B]
    (q : A → B) (hq : Ch03.QuotientMap q) (hX : Ch11.LCH X) :
    Ch03.QuotientMap (fun p : X × A => (p.1, q p.2)) := by
  let : T2Space X := hX.2
  let : LocallyCompactSpace X :=
    (Ch11.locallyCompact_iff_locallyCompactSpace X).mp hX.1
  apply Ch03.quotient_of_mapping_test
  · exact continuous_fst.prodMk ((Ch03.quotient_continuous q hq).comp continuous_snd)
  · rintro ⟨x, b⟩
    obtain ⟨a, rfl⟩ := hq.1 b
    exact ⟨(x, a), rfl⟩
  · intro Z tZ h hh
    letI : TopologicalSpace Z := tZ
    exact ((Ch03.quotientMap_iff_mathlib q).mp hq).continuous_lift_prod_right hh

end D10Topology.Ch13
