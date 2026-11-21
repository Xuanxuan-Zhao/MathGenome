import MathGenome.Internal.RealAnalysis.D11.Ch21.LchGroupInterface
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch21.CompactCoveringRatios
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! Finite covering ratios for arbitrary locally compact Hausdorff groups.
The library index uses inverse images of translations. We verify below that
its finite minimizers are precisely covers by left-translate images after
inverting the centers; no finiteness assertion relies on the default value
of the natural-number infimum. -/
noncomputable section
namespace D11.Ch21
open Set TopologicalSpace
open scoped Topology Pointwise
universe u

/-- Least finite left-translate covering number, with zero for the empty set. -/
def coveringNumber (G : Type u) [Group G] (K V : Set G) : ℕ :=
  MeasureTheory.Measure.haar.index K V

/-- Covering ratio with the fixed compact normalization set. -/
def coveringRatio (G : Type u) [Group G] [TopologicalSpace G]
    (K₀ : PositiveCompacts G) (U : Set G) (K : Compacts G) : ℝ :=
  (coveringNumber G K U : ℝ) / coveringNumber G K₀ U

private theorem inverse_centers_cover (G : Type u) [Group G] (V : Set G) (t : Finset G) :
    (⋃ a ∈ t.map (Equiv.inv G).toEmbedding, (fun x => a * x) '' V) =
      ⋃ g ∈ t, (fun x => g * x) ⁻¹' V := by
  ext x
  simp only [mem_iUnion, Finset.mem_map, Equiv.toEmbedding_apply, Equiv.inv_apply,
    mem_image, mem_preimage]
  constructor
  · rintro ⟨a, ⟨g, hg, rfl⟩, v, hv, rfl⟩
    exact ⟨g, hg, by simpa using hv⟩
  · rintro ⟨g, hg, hx⟩
    exact ⟨g⁻¹, ⟨g, hg, rfl⟩, g * x, hx, inv_mul_cancel_left g x⟩

theorem finite_minimal_left_translate_cover :
    Specs.D11.Ch21.CompactCoveringRatios.finiteMinimalCoverStatement.{u} := by
  intro G _ _ _ _ _ K V hK hV
  constructor
  · obtain ⟨t, ht, hc⟩ := MeasureTheory.Measure.haar.index_elim hK hV
    refine ⟨t.map (Equiv.inv G).toEmbedding, ?_, ?_⟩
    · rwa [inverse_centers_cover]
    · simpa [Specs.D11.Ch21.CompactCoveringRatios.coveringNumberValue,
        MeasureTheory.Measure.haar.index] using hc
  · intro t ht
    have hc : K ⊆ ⋃ g ∈ t.map (Equiv.inv G).toEmbedding,
        (fun x => g * x) ⁻¹' V := by
      rw [← inverse_centers_cover]
      simpa using ht
    apply Nat.sInf_le
    exact ⟨t.map (Equiv.inv G).toEmbedding, hc, Finset.card_map _⟩

theorem coveringNumber_empty :
    Specs.D11.Ch21.CompactCoveringRatios.emptyStatement.{u} := by
  intro G _ V
  exact MeasureTheory.Measure.haar.index_empty

private theorem coveringNumber_self (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K₀ : PositiveCompacts G) :
    coveringNumber G K₀ K₀ = 1 := by
  have hp := MeasureTheory.Measure.haar.index_pos K₀ K₀.interior_nonempty
  have hle : coveringNumber G K₀ K₀ ≤ 1 := by
    apply Nat.sInf_le
    refine ⟨{1}, ?_, by simp⟩
    simp
  exact Nat.le_antisymm hle hp

/-- All assertions of the finite compact covering-ratio lemma, including the
separated-union equality and both normalization and empty-set values. -/
theorem compact_covering_ratios :
    Specs.D11.Ch21.CompactCoveringRatios.ratiosStatement.{u} := by
  intro G _ _ _ _ _ K₀ U hU
  have hUi : (interior U).Nonempty :=
    ⟨1, mem_interior_iff_mem_nhds.mpr hU⟩
  refine ⟨MeasureTheory.Measure.haar.index_pos K₀ hUi,
    coveringNumber_self G K₀,
    MeasureTheory.Measure.haar.prehaar_self hUi,
    MeasureTheory.Measure.haar.prehaar_empty K₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro K
    exact ⟨MeasureTheory.Measure.haar.prehaar_nonneg K₀ K,
      MeasureTheory.Measure.haar.prehaar_le_index K₀ K hUi⟩
  · intro a K
    exact MeasureTheory.Measure.haar.is_left_invariant_prehaar hUi a K
  · intro K L hKL
    exact MeasureTheory.Measure.haar.prehaar_mono hUi hKL
  · intro K L
    exact MeasureTheory.Measure.haar.prehaar_sup_le K L hUi
  · intro K L hKL
    exact MeasureTheory.Measure.haar.prehaar_sup_eq hUi hKL

end D11.Ch21
