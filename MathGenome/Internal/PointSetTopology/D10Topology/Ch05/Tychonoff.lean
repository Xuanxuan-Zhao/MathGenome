import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Tychonoff
import MathGenome.Internal.PointSetTopology.D10Topology.Ch03.Products
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.CompactImagesAndSeparation

/-!
The Tychonoff product theorem, paper.tex `d10:05:tychonoff`.
The canonical product-topology and open-cover compactness bridges identify
the precise objects in Mathlib's arbitrary, non-Hausdorff product theorem.
Its ultrafilter proof chooses coordinate limits without asserting uniqueness.
-/

open Set
universe u v

namespace D10Topology.Ch05

/-- An arbitrary family of compact spaces has compact product. Choice is
allowed; no factor need be nonempty or Hausdorff. -/
theorem tychonoff_product {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i))
    (hX : ∀ i, @CoverCompact (X i) (tX i)) :
    @CoverCompact (Ch03.Product X) (Ch03.productTopology tX) := by
  rw [Ch03.productTopology_eq_pi]
  let := tX
  let : ∀ i, CompactSpace (X i) :=
    fun i => (coverCompact_iff_compactSpace (X i)).mp (hX i)
  exact (coverCompact_iff_compactSpace (Ch03.Product X)).mpr Pi.compactSpace

/-- Nonemptiness makes each continuous projection surjective. -/
theorem compact_factors_of_nonempty_product {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (hne : Nonempty (Ch03.Product X))
    (hP : @CoverCompact (Ch03.Product X) (Ch03.productTopology tX)) :
    ∀ i, @CoverCompact (X i) (tX i) := by
  let := tX
  let : TopologicalSpace (Ch03.Product X) := Ch03.productTopology tX
  intro i
  apply (coverCompact_iff_isCompact_univ (X i)).mpr
  have himage := ((coverCompact_iff_isCompact_univ (Ch03.Product X)).mp hP).image
    (Ch03.projection_continuous tX i)
  simpa only [image_univ, range_eq_univ.mpr (Ch03.projection_surjective hne i)] using himage

theorem nonempty_product_compact_iff {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (hne : Nonempty (Ch03.Product X)) :
    @CoverCompact (Ch03.Product X) (Ch03.productTopology tX) ↔
      ∀ i, @CoverCompact (X i) (tX i) :=
  ⟨compact_factors_of_nonempty_product tX hne, tychonoff_product tX⟩

/-- No factor assumptions are required for an empty indexing type. -/
theorem empty_index_product_compact {I : Type u} {X : I → Type v} [IsEmpty I]
    (tX : ∀ i, TopologicalSpace (X i)) :
    @CoverCompact (Ch03.Product X) (Ch03.productTopology tX) :=
  tychonoff_product tX (fun i => isEmptyElim i)

/-- An empty factor makes the product compact irrespective of the other factors. -/
theorem product_compact_of_empty_factor {I : Type u} {X : I → Type v}
    (tX : ∀ i, TopologicalSpace (X i)) (i : I) [IsEmpty (X i)] :
    @CoverCompact (Ch03.Product X) (Ch03.productTopology tX) := by
  let : TopologicalSpace (Ch03.Product X) := Ch03.productTopology tX
  let : IsEmpty (Ch03.Product X) := Ch03.product_empty_of_factor i
  exact empty_space_compact (Ch03.Product X)

theorem real_not_coverCompact : ¬ CoverCompact ℝ := by
  intro h
  obtain ⟨_, xmax, _, hmax⟩ := continuous_real_extrema (fun x : ℝ => x) h continuous_id
  exact (lt_add_one xmax).not_ge (hmax (xmax + 1))

theorem empty_real_compact_counterexample :
    CoverCompact (Empty × ℝ) ∧ ¬ CoverCompact ℝ :=
  ⟨empty_space_compact (Empty × ℝ), real_not_coverCompact⟩

end D10Topology.Ch05
