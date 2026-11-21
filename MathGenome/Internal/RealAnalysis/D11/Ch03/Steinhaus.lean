import MathGenome.Internal.RealAnalysis.D11.Ch03.EuclideanRegularity
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch03.Steinhaus
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-! Steinhaus on the completed Lebesgue real line.
Inner regularity extracts a positive compact subset. This subset is Borel, so
the native Haar theorem applies without identifying the completed and Borel
sigma-algebras. Its difference neighborhood is contained in `E - E`.
-/

open Set MeasureTheory
open scoped ENNReal Pointwise Topology

namespace D11.Ch03.Steinhaus

open LebesgueMeasures

/-- A Euclidean ball on the one-dimensional shared space is an open interval. -/
theorem ball_zero_eq_interval (δ : ℝ) :
    Metric.ball (0 : Point 1) δ = {h : Point 1 | -δ < h 0 ∧ h 0 < δ} := by
  ext h
  simp [EuclideanSpace.norm_eq, Real.norm_eq_abs,
    Real.sqrt_sq_eq_abs, abs_lt]

theorem steinhaus : Specs.D11.Ch03.Steinhaus.steinhaus := by
  intro E hE hpos
  have hsup : lebesgue 1 E =
      ⨆ (K : Set (Point 1)) (_ : K ⊆ E) (_ : IsCompact K), lebesgue 1 K :=
    EuclideanRegularity.inner_regularity 1 E hE
  have hposSup : 0 < ⨆ (K : Set (Point 1)) (_ : K ⊆ E) (_ : IsCompact K),
      lebesgue 1 K := by
    rw [← hsup]
    exact hpos
  obtain ⟨K, hK⟩ := (lt_iSup_iff).mp hposSup
  obtain ⟨hKE, hK⟩ := (lt_iSup_iff).mp hK
  obtain ⟨hK, hKpos⟩ := (lt_iSup_iff).mp hK
  have hvol : 0 < (volume : Measure (Point 1)) K := by
    rwa [← EuclideanRegularity.lebesgue_eq_volume 1 K]
  have hnhds : K - K ∈ 𝓝 (0 : Point 1) :=
    Measure.sub_mem_nhds_zero_of_addHaar_pos volume K hK.measurableSet hvol
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδ, ?_⟩
  rw [← ball_zero_eq_interval]
  exact hball.trans (Set.sub_subset_sub hKE hKE)

end D11.Ch03.Steinhaus
