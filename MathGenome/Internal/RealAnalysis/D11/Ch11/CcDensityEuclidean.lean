import MathGenome.Internal.RealAnalysis.Specs.D11.Ch11.CcDensityEuclidean
import MathGenome.Internal.RealAnalysis.D11.Ch11.StepDensity
import MathGenome.Internal.RealAnalysis.D11.Ch19.CcCzero
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.LpSeminorm.Trim

/-! Compactly supported continuous approximation for completed Euclidean
Lebesgue measure. We first use rectangle step density in the completed
space. Rectangle steps are Borel strongly measurable, so their norms agree
with those for Borel volume. The regular-measure approximation theorem then
gives a Cc approximant. Trimming identities transfer this approximant and
its error back to the completed measure; the Lp triangle inequality finishes.
No BorelSpace instance for the completed measurable space is asserted. -/

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace D11.Ch11.CcDensityEuclidean
open D11.Ch03 D11.Ch03.LebesgueMeasures D11.Ch11.StepDensity

variable {d : ℕ} [NeZero d] {𝕜 : Type} [RCLike 𝕜]

/-- Every Cc function defines an ordinary Lp class for the completed measure. -/
lemma cc_memLp (p : ℝ≥0∞) (g : CompactlySupportedContinuousMap (Point d) 𝕜) :
    @MemLp _ _ (lebesgueSpace d) _ _ g p (lebesgue d) := by
  let : MeasurableSpace (Point d) := lebesgueSpace d
  exact g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport

/-- Rectangle steps have Borel representatives before passing to the completion. -/
lemma steps_stronglyMeasurable {g : Point d → 𝕜} (hg : g ∈ rectangleSteps d 𝕜) :
    StronglyMeasurable g := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨a, b, c, rfl⟩ := hg
    apply stronglyMeasurable_const.indicator
    exact OpensMeasurableSpace.borel_le _
      (endpointBox_borel d a b (fun _ => true) (fun _ => false))
  | zero => exact stronglyMeasurable_const
  | add f g _ _ hf hg => exact hf.add hg
  | smul c f _ hf => exact hf.const_smul c

/-- Apply Borel regular-measure approximation to a step and transport its
membership and error to the full completed Lebesgue measure. -/
lemma exists_cc_approx_step {p : ℝ≥0∞} (hp : p ≠ ∞)
    {g : Point d → 𝕜} (hg : g ∈ rectangleSteps d 𝕜)
    (hgp : @MemLp _ _ (lebesgueSpace d) _ _ g p (lebesgue d))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ h : CompactlySupportedContinuousMap (Point d) 𝕜,
      ∃ _hh : @MemLp _ _ (lebesgueSpace d) _ _ h p (lebesgue d),
        @eLpNorm _ _ _ _ (lebesgueSpace d) (g - (h : Point d → 𝕜)) p (lebesgue d) ≤
          ENNReal.ofReal ε := by
  have htrim_eq : (lebesgue d).trim (native_borel_le d) =
      (volume : Measure (Point d)) := borel_restriction d (native_borel_le d)
  have hgB := steps_stronglyMeasurable hg
  have hgtrim : MemLp g p ((lebesgue d).trim (native_borel_le d)) := by
    change eLpNorm g p ((lebesgue d).trim (native_borel_le d)) < ∞
    rw [eLpNorm_trim (native_borel_le d) hgB]
    exact hgp
  rw [htrim_eq] at hgtrim
  obtain ⟨h, hsupp, herr, hcont, hmem⟩ :=
    hgtrim.exists_hasCompactSupport_eLpNorm_sub_le hp
      (ne_of_gt (ENNReal.ofReal_pos.mpr hε))
  have htrim : MemLp h p ((lebesgue d).trim (native_borel_le d)) := by
    rw [htrim_eq]
    exact hmem
  have hh := memLp_of_memLp_trim (native_borel_le d) htrim
  refine ⟨⟨⟨h, hcont⟩, hsupp⟩, hh, ?_⟩
  have heq := eLpNorm_trim (p := p) (μ := lebesgue d) (native_borel_le d)
    (hgB.sub hcont.stronglyMeasurable)
  rw [htrim_eq] at heq
  exact heq.symm.trans_le herr

/-- Cc is dense in the ordinary scalar Lp quotient for completed Lebesgue measure. -/
theorem cc_density : Specs.D11.Ch11.CcDensityEuclidean.cc_density := by
  intro d _ 𝕜 _ _ _ p _ hp
  let : MeasurableSpace (Point d) := lebesgueSpace d
  intro f ε hε
  change Lp 𝕜 p (lebesgue d) at f
  obtain ⟨g, hg, hgp, herr⟩ := StepDensity.step_density d 𝕜 p hp f (ε / 2) (half_pos hε)
  change MemLp g p (lebesgue d) at hgp
  change ‖f - hgp.toLp g‖ < ε / 2 at herr
  obtain ⟨h, hh, herror⟩ := exists_cc_approx_step hp hg hgp (half_pos hε)
  refine ⟨h, hh, ?_⟩
  have hnorm : ‖hgp.toLp g - hh.toLp h‖ ≤ ε / 2 := by
    rw [← MemLp.toLp_sub hgp hh, Lp.norm_toLp]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top herror).trans_eq
      (ENNReal.toReal_ofReal (half_pos hε).le)
  calc
    ‖f - hh.toLp h‖ ≤ ‖f - hgp.toLp g‖ + ‖hgp.toLp g - hh.toLp h‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le herr hnorm
    _ = ε := add_halves ε

end D11.Ch11.CcDensityEuclidean
