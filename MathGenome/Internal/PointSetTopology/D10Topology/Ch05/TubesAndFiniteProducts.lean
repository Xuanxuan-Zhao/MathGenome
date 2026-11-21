import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.TubesAndFiniteProducts
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products

/-!
Tube lemma, closed projections, and compact finite products, with the
open-cover convention of chapter 5. No Hausdorff or inhabited instances are
required. The library tube lemma is applied to a singleton and the compact
whole second factor. Closedness is then deduced by applying this tube to the
complement of a closed set.
-/

open Set
universe u v

namespace D10Topology.Ch05

theorem tube_lemma {X : Type u} {K : Type v}
    [TopologicalSpace X] [TopologicalSpace K] (hK : CoverCompact K)
    (x : X) (W : Set (X × K)) (hW : IsOpen W)
    (hxW : ({x} : Set X) ×ˢ (univ : Set K) ⊆ W) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ×ˢ (univ : Set K) ⊆ W := by
  have hcompact : IsCompact (univ : Set K) :=
    (coverCompact_iff_isCompact_univ K).mp hK
  obtain ⟨U, V, hU, _hV, hxU, hKV, hUV⟩ :=
    generalized_tube_lemma isCompact_singleton hcompact hW hxW
  exact ⟨U, hU, hxU (mem_singleton x), (prod_mono (Subset.refl U) hKV).trans hUV⟩

theorem projection_closed {X : Type u} {K : Type v}
    [TopologicalSpace X] [TopologicalSpace K] (hK : CoverCompact K) :
    IsClosedMap (Prod.fst : X × K → X) := by
  intro C hC
  rw [← isOpen_compl_iff]
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  have hfiber : ({x} : Set X) ×ˢ (univ : Set K) ⊆ Cᶜ := by
    rintro ⟨y, k⟩ ⟨hy, _⟩ hmem
    have hyx : y = x := mem_singleton_iff.mp hy
    subst y
    exact hx ⟨(x, k), hmem, rfl⟩
  obtain ⟨U, hU, hxU, htube⟩ := tube_lemma hK x Cᶜ hC.isOpen_compl hfiber
  refine ⟨U, ?_, hU, hxU⟩
  intro y hy
  rintro ⟨⟨z, k⟩, hmem, hzy⟩
  change z = y at hzy
  subst z
  exact htube ⟨hy, mem_univ k⟩ hmem

theorem compact_binary_product {X : Type u} {K : Type v}
    [TopologicalSpace X] [TopologicalSpace K]
    (hX : CoverCompact X) (hK : CoverCompact K) : CoverCompact (X × K) := by
  letI : CompactSpace X := (coverCompact_iff_compactSpace X).mp hX
  letI : CompactSpace K := (coverCompact_iff_compactSpace K).mp hK
  exact (coverCompact_iff_compactSpace (X × K)).mpr inferInstance

/-- The project product topology is identified with the library Pi topology
before applying compactness of a product. This specializes the library product
theorem to finite indices, including the empty index type. -/
theorem compact_finite_product {I : Type u} {X : I → Type v} [Finite I]
    (tX : ∀ i, TopologicalSpace (X i))
    (hX : ∀ i, @CoverCompact (X i) (tX i)) :
    @CoverCompact (Ch03.Product X) (Ch03.productTopology tX) := by
  rw [Ch03.productTopology_eq_pi]
  letI := tX
  letI : ∀ i, CompactSpace (X i) :=
    fun i => (coverCompact_iff_compactSpace (X i)).mp (hX i)
  exact (coverCompact_iff_compactSpace (Ch03.Product X)).mpr inferInstance

theorem empty_product_compact {I : Type u} {X : I → Type v} [IsEmpty I]
    (tX : ∀ i, TopologicalSpace (X i)) :
    (∃! _x : Ch03.Product X, True) ∧
      @CoverCompact (Ch03.Product X) (Ch03.productTopology tX) := by
  exact ⟨Ch03.empty_product_singleton,
    compact_finite_product tX (fun i => isEmptyElim i)⟩

/-- An empty factor makes the product empty, regardless of the other factors
or of finiteness of the index type. In particular this covers finite products
with an empty factor without imposing an inhabitedness condition. -/
theorem empty_factor_product_compact {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (i : I) [IsEmpty (X i)] :
    IsEmpty (Ch03.Product X) ∧
      @CoverCompact (Ch03.Product X) (Ch03.productTopology tX) := by
  letI : IsEmpty (Ch03.Product X) := Ch03.product_empty_of_factor i
  letI : TopologicalSpace (Ch03.Product X) := Ch03.productTopology tX
  exact ⟨inferInstance, empty_space_compact (Ch03.Product X)⟩

end D10Topology.Ch05
