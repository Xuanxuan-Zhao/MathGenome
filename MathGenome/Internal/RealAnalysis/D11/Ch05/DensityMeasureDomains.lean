import MathGenome.Internal.RealAnalysis.Specs.D11.Ch05.DensityMeasureDomains
import MathGenome.Internal.RealAnalysis.D11.Ch05.NonnegativeIntegral
import MathGenome.Internal.RealAnalysis.D11.Ch01.ExhaustionRestriction
import MathGenome.Internal.RealAnalysis.D11.Ch01.MeasureBoundsContinuity

/-! The measure with density and continuity with respect to its domain
(paper.tex:1687–1703, 1732–1743). The proved bridge for the canonical source
integral identifies the measurable-set prescription with `withDensity`.
Both continuity assertions then apply the upstream set-continuity theorem to
this same measure. For decreasing domains only one weighted integral is finite;
the ambient measure and earlier weighted integrals may be infinite.
-/
open Set Filter MeasureTheory
open scoped ENNReal Topology
universe u
noncomputable section
namespace D11.Ch05.DensityMeasureDomains

open NonnegativeIntegral
open D11.Ch01.ExhaustionRestriction

def densityMeasure {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (h : X → ℝ≥0∞) : Measure X := μ.withDensity h

theorem densityMeasure_apply {X : Type u} [MeasurableSpace X]
    (μ : Measure X) (h : X → ℝ≥0∞) (_hh : Measurable h)
    (E : Set X) (hE : MeasurableSet E) :
    densityMeasure μ h E = nonnegativeIntegral (restrictOnSpace μ E) h := by
  rw [integral_eq_lintegral]
  exact withDensity_apply h hE

theorem densityMeasure_mass : Specs.D11.Ch05.DensityMeasureDomains.densityMeasure_mass := by
  intro X _ μ h hh
  change densityMeasure μ h univ = nonnegativeIntegral μ h
  rw [densityMeasure_apply μ h hh univ MeasurableSet.univ]
  simp only [restrictOnSpace, Measure.restrict_univ]

theorem densityMeasure_finite : Specs.D11.Ch05.DensityMeasureDomains.densityMeasure_finite := by
  intro X _ μ h hh hfin
  exact ⟨by rw [densityMeasure_mass μ h hh]; exact hfin⟩

theorem densityMeasure_null : Specs.D11.Ch05.DensityMeasureDomains.densityMeasure_null := by
  intro X _ μ h hh N hN hzero
  change densityMeasure μ h N = 0
  rw [densityMeasure_apply μ h hh N hN, integral_eq_lintegral]
  exact setLIntegral_measure_zero N h hzero

theorem densityMeasure_countable_additivity :
    Specs.D11.Ch05.DensityMeasureDomains.densityMeasure_countable_additivity := by
  intro X _ μ h hh E hE hd
  change nonnegativeIntegral (restrictOnSpace μ (⋃ n, E n)) h =
    ∑' n, nonnegativeIntegral (restrictOnSpace μ (E n)) h
  rw [← densityMeasure_apply μ h hh _ (MeasurableSet.iUnion hE)]
  simp_rw [← densityMeasure_apply μ h hh _ (hE _)]
  exact measure_iUnion hd hE

theorem domain_continuity_from_below :
    Specs.D11.Ch05.DensityMeasureDomains.domain_continuity_from_below := by
  intro X _ μ f hf E s hE hmono hlim
  change Monotone (fun n => nonnegativeIntegral (restrictOnSpace μ (E n)) f) ∧
    (⨆ n, nonnegativeIntegral (restrictOnSpace μ (E n)) f) =
      nonnegativeIntegral (restrictOnSpace μ s) f ∧
    Tendsto (fun n => nonnegativeIntegral (restrictOnSpace μ (E n)) f)
      atTop (𝓝 (nonnegativeIntegral (restrictOnSpace μ s) f))
  have hs : MeasurableSet s := hlim ▸ MeasurableSet.iUnion hE
  have h := D11.Ch01.MeasureBoundsContinuity.continuity_from_below
    (densityMeasure μ f) E s hE hmono hlim
  simpa only [densityMeasure_apply μ f hf _ hs,
    densityMeasure_apply μ f hf _ (hE _)] using h

theorem domain_continuity_from_above :
    Specs.D11.Ch05.DensityMeasureDomains.domain_continuity_from_above := by
  intro X _ μ f hf E s hE hanti hlim hfin
  change Antitone (fun n => nonnegativeIntegral (restrictOnSpace μ (E n)) f) ∧
    (⨅ n, nonnegativeIntegral (restrictOnSpace μ (E n)) f) =
      nonnegativeIntegral (restrictOnSpace μ s) f ∧
    Tendsto (fun n => nonnegativeIntegral (restrictOnSpace μ (E n)) f)
      atTop (𝓝 (nonnegativeIntegral (restrictOnSpace μ s) f))
  change ∃ N, nonnegativeIntegral (restrictOnSpace μ (E N)) f < ∞ at hfin
  have hs : MeasurableSet s := hlim ▸ MeasurableSet.iInter hE
  have hfinite : ∃ N, densityMeasure μ f (E N) < ∞ := by
    simpa only [densityMeasure_apply μ f hf _ (hE _)] using hfin
  have h := D11.Ch01.MeasureBoundsContinuity.continuity_from_above
    (densityMeasure μ f) E s hE hanti hlim hfinite
  simpa only [densityMeasure_apply μ f hf _ hs,
    densityMeasure_apply μ f hf _ (hE _)] using h

end D11.Ch05.DensityMeasureDomains
