import MathGenome.Internal.RealAnalysis.D11.Ch21.CompactCoveringRatios
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.CompactContentCluster

/-!
# Invariant compact content from the compact product

The library's `haar.chaar` is defined by choosing a point in the intersection
of the closures of the covering-ratio tails inside the compact product.
Its existence proof uses `isCompact_univ_pi` and the finite-intersection
property over all open identity neighborhoods. We bridge that construction
to the present covering numbers and to tails over arbitrary neighborhoods.
This is before the outer-measure construction or Haar normalization.
-/
noncomputable section
namespace D11.Ch21

open Set TopologicalSpace
open scoped Topology
open Specs.D11.Ch21.CompactContentCluster
universe u

/-- The content selected by the Tychonoff/FIP compact-product construction,
with the original fixed normalization set. -/
def compactContent (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (K₀ : PositiveCompacts G) : Compacts G → ℝ :=
  MeasureTheory.Measure.haar.chaar K₀

/-- Tychonoff compactness with one finite real interval per compact subset. -/
theorem compact_content_product_isCompact : productCompactStatement.{u} := by
  intro G _ _ _ _ _ K₀
  apply isCompact_univ_pi
  intro K
  exact isCompact_Icc

/-- Any finitely many neighborhood tails have a common covering-ratio point. -/
theorem compact_content_finite_intersection : finiteIntersectionStatement.{u} := by
  intro G _ _ _ _ _ K₀ t ht
  let U : Set G := ⋂ V ∈ t, V
  have hU : U ∈ 𝓝 (1 : G) := (Filter.biInter_finset_mem t).2 ht
  refine ⟨coveringRatio G K₀ U, ?_, ?_⟩
  · have hb := (compact_covering_ratios G K₀ U hU).2.2.2.2.1
    intro K _
    exact hb K
  · simp only [mem_iInter]
    intro V hV
    apply subset_closure
    refine ⟨U, ⟨?_, hU⟩, rfl⟩
    exact (iInter_subset _ V).trans (iInter_subset _ hV)

/-- Transfer the open-tail cluster point to every identity-neighborhood tail. -/
private theorem chaar_mem_ratioCluster (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K₀ : PositiveCompacts G) (V : Set G)
    (hV : V ∈ 𝓝 (1 : G)) :
    MeasureTheory.Measure.haar.chaar K₀ ∈ ratioCluster G K₀ V := by
  obtain ⟨W, hWV, hWo, hW1⟩ := mem_nhds_iff.mp hV
  have hc := MeasureTheory.Measure.haar.chaar_mem_clPrehaar K₀ ⟨⟨W, hWo⟩, hW1⟩
  apply (closure_mono ?_) hc
  rintro f ⟨U, ⟨hUW, hUo, hU1⟩, rfl⟩
  exact ⟨U, ⟨hUW.trans hWV, hUo.mem_nhds hU1⟩, rfl⟩

/-- The selected content has all the required laws and belongs to every
neighborhood-tail closure in the compact product. -/
theorem compactContent_spec : contentStatement.{u} := by
  intro G _ _ _ _ _ K₀
  let h : Compacts G → ℝ := MeasureTheory.Measure.haar.chaar K₀
  have hp : h ∈ contentProduct G K₀ :=
    MeasureTheory.Measure.haar.chaar_mem_haarProduct K₀
  refine ⟨hp, chaar_mem_ratioCluster G K₀, ?_⟩
  refine ⟨MeasureTheory.Measure.haar.chaar_empty K₀,
    MeasureTheory.Measure.haar.chaar_self K₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro K
    exact hp K (mem_univ K)
  · intro a K
    exact MeasureTheory.Measure.haar.is_left_invariant_chaar a K
  · intro K L hKL
    exact MeasureTheory.Measure.haar.chaar_mono hKL
  · intro K L
    exact MeasureTheory.Measure.haar.chaar_sup_le K L
  · intro K L hKL
    exact MeasureTheory.Measure.haar.chaar_sup_eq hKL L.isCompact.isClosed

/-- A finite invariant additive content, normalized at the fixed `K₀`,
obtained by the compact-product cluster construction over all neighborhoods. -/
theorem compact_content_cluster : clusterStatement.{u} := by
  intro G _ _ _ _ _ K₀
  exact ⟨compactContent G K₀, compactContent_spec G K₀⟩

end D11.Ch21
