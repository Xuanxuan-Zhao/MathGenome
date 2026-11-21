import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationProducts
import MathGenome.Internal.PointSetTopology.D10Topology.Ch07.SeparationConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products

/-!
Arbitrary products preserve the separation properties in
`paper.tex`, d10:07:heredity-products.

The Chapter 3 bridge identifies the paper's initial product topology
with Mathlib's dependent-product topology. The library product instances
require neither inhabited factors nor an inhabited index type. In particular,
the statements include empty products and products with empty factors.
-/

universe u v

namespace D10Topology.Ch07

open D10Topology.Ch03

variable {I : Type u} {X : I → Type v}

theorem product_t0 (tX : ∀ i, TopologicalSpace (X i))
    (h : ∀ i, @T0 (X i) (tX i)) :
    @T0 (Product X) (productTopology tX) := by
  let := tX
  let : ∀ i, T0Space (X i) := h
  rw [productTopology_eq_pi]
  exact inferInstance

theorem product_t1 (tX : ∀ i, TopologicalSpace (X i))
    (h : ∀ i, @T1 (X i) (tX i)) :
    @T1 (Product X) (productTopology tX) := by
  let := tX
  let : ∀ i, T1Space (X i) := h
  rw [productTopology_eq_pi]
  exact inferInstance

theorem product_t2 (tX : ∀ i, TopologicalSpace (X i))
    (h : ∀ i, @T2 (X i) (tX i)) :
    @T2 (Product X) (productTopology tX) := by
  let := tX
  let : ∀ i, T2Space (X i) := h
  rw [productTopology_eq_pi]
  exact inferInstance

theorem product_regular (tX : ∀ i, TopologicalSpace (X i))
    (h : ∀ i, @Regular (X i) (tX i)) :
    @Regular (Product X) (productTopology tX) := by
  let := tX
  let : ∀ i, RegularSpace (X i) := h
  rw [productTopology_eq_pi]
  exact inferInstance

/-- This is complete regularity of the whole product: every closed F and
x outside F admit a continuous unit-interval function equal to 1 at x
and 0 throughout F. No point-separation assumption is imposed. -/
theorem product_completelyRegular (tX : ∀ i, TopologicalSpace (X i))
    (h : ∀ i, @CompletelyRegular (X i) (tX i)) :
    @CompletelyRegular (Product X) (productTopology tX) := by
  let := tX
  let : ∀ i, CompletelyRegularSpace (X i) :=
    fun i => (completelyRegular_iff_mathlib (X i)).mp (h i)
  rw [productTopology_eq_pi]
  exact (completelyRegular_iff_mathlib (Product X)).mpr inferInstance

theorem product_t3 (tX : ∀ i, TopologicalSpace (X i))
    (h : ∀ i, @T3 (X i) (tX i)) :
    @T3 (Product X) (productTopology tX) :=
  ⟨product_regular tX (fun i => (h i).1), product_t1 tX (fun i => (h i).2)⟩

theorem product_tychonoff (tX : ∀ i, TopologicalSpace (X i))
    (h : ∀ i, @Tychonoff (X i) (tX i)) :
    @Tychonoff (Product X) (productTopology tX) :=
  ⟨product_completelyRegular tX (fun i => (h i).1),
    product_t2 tX (fun i => (h i).2)⟩

end D10Topology.Ch07
