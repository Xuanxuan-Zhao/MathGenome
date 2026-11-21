import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch08.CountableProducts
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products

/-!
Countable products preserve the three countability properties asserted in
paper.tex, `d10:08:permanence`. The bridge `productTopology_eq_pi`
identifies the paper's initial topology with the library product topology.
First countability is stated using the paper's countable local bases and
transported through `firstCountable_iff_mathlib` in both directions.

The library's separability instance constructs a countable dense range
indexed by finite sets of coordinates and choices in their countable dense
sets; it does not assert countability of the whole product of those sets.
All three library instances allow empty factors and empty index types.
-/

universe u v

namespace D10Topology.Ch08

theorem countable_product_firstCountable
    {I : Type u} [Countable I] {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i))
    (h : ∀ i, FirstCountable (tX i)) :
    FirstCountable (Ch03.productTopology tX) := by
  rw [Ch03.productTopology_eq_pi]
  let := tX
  let : ∀ i, FirstCountableTopology (X i) :=
    fun i => firstCountable_iff_mathlib.mp (h i)
  exact firstCountable_iff_mathlib.mpr inferInstance

theorem countable_product_secondCountable
    {I : Type u} [Countable I] {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i))
    (h : ∀ i, SecondCountable (tX i)) :
    SecondCountable (Ch03.productTopology tX) := by
  rw [Ch03.productTopology_eq_pi]
  let := tX
  let : ∀ i, SecondCountableTopology (X i) := h
  exact inferInstance

theorem countable_product_separable
    {I : Type u} [Countable I] {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i))
    (h : ∀ i, Separable (tX i)) :
    Separable (Ch03.productTopology tX) := by
  rw [Ch03.productTopology_eq_pi]
  let := tX
  let : ∀ i, TopologicalSpace.SeparableSpace (X i) := h
  exact inferInstance

end D10Topology.Ch08
