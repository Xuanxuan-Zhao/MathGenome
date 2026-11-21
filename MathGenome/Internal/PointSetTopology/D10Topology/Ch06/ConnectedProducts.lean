import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.ConnectedProducts
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.Connectedness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products

/-! Arbitrary connected products, paper.tex `d10:06:product`.
Source connectedness includes the empty space. The upstream bridge to
preconnectedness and the equality with the canonical Pi topology allow the
library's arbitrary-product theorem to apply with exactly this convention. -/

universe u v

namespace D10Topology.Ch06

theorem connected_product {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i))
    (hX : ∀ i, @Connected (X i) (tX i)) :
    @Connected (Ch03.Product X) (Ch03.productTopology tX) := by
  rw [Ch03.productTopology_eq_pi]
  let := tX
  let : ∀ i, PreconnectedSpace (X i) :=
    fun i => (connected_iff_preconnectedSpace (X i)).mp (hX i)
  exact (connected_iff_preconnectedSpace (Ch03.Product X)).mpr inferInstance

theorem connected_factor_of_product {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (hn : Nonempty (Ch03.Product X))
    (hP : @Connected (Ch03.Product X) (Ch03.productTopology tX)) (i : I) :
    @Connected (X i) (tX i) := by
  let := tX
  let : TopologicalSpace (Ch03.Product X) := Ch03.productTopology tX
  exact connected_surjective_image (Ch03.projection i) hP
    (Ch03.projection_continuous tX i) (Ch03.projection_surjective hn i)

theorem connected_product_iff {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (hn : Nonempty (Ch03.Product X)) :
    @Connected (Ch03.Product X) (Ch03.productTopology tX) ↔
      ∀ i, @Connected (X i) (tX i) :=
  ⟨connected_factor_of_product tX hn, connected_product tX⟩

theorem connected_empty_product {I : Type u} {X : I → Type v} [IsEmpty I]
    (tX : ∀ i, TopologicalSpace (X i)) :
    @Connected (Ch03.Product X) (Ch03.productTopology tX) := by
  let : TopologicalSpace (Ch03.Product X) := Ch03.productTopology tX
  exact connected_of_subsingleton (Ch03.Product X)

theorem connected_product_of_empty_factor {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (i : I) [IsEmpty (X i)] :
    @Connected (Ch03.Product X) (Ch03.productTopology tX) := by
  let : TopologicalSpace (Ch03.Product X) := Ch03.productTopology tX
  let : IsEmpty (Ch03.Product X) := Ch03.product_empty_of_factor i
  exact connected_of_subsingleton (Ch03.Product X)

end D10Topology.Ch06
