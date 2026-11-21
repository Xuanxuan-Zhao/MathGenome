import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.RNPositiveFinite
import MathGenome.Internal.RealAnalysis.D11.Ch15.MaximalAdmissibleDensity
import MathGenome.Internal.RealAnalysis.D11.Ch14.Hahn
import MathGenome.Internal.RealAnalysis.D11.Ch05.MarkovZeroFinite
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Completion of the supremal-admissible-density proof of finite positive RN.
The library's `exists_positive_of_not_mutuallySingular` is the finite Hahn
argument applied to the residual and small multiples of the reference measure.
Its hypotheses are exactly finiteness of the two measures. No RN existence,
Hilbert projection, Hilbert representation, or Lp duality is used. -/

open Set Filter MeasureTheory
open scoped ENNReal
universe u
noncomputable section

namespace D11.Ch15.RNPositiveFinite

open D11.Ch15.MaximalAdmissibleDensity

theorem residual_vanishes : Specs.D11.Ch15.RNPositiveFinite.residual_vanishes := by
  intro X _ μ ν _ _ h hac hh hmax
  obtain ⟨hrfin, hrac, hrapply, hradd⟩ := residual_properties μ ν h hh hac
  let _ := hrfin
  have hsing : residualMeasure μ ν h ⟂ₘ μ := by
    by_contra hnot
    obtain ⟨c, hc, P, hP, hμP, hpos⟩ :=
      Measure.exists_positive_of_not_mutuallySingular (residualMeasure μ ν h) μ hnot
    have hboost (E : Set X) (hE : MeasurableSet E) :
        (∫⁻ x in E ∩ P, (c : ℝ≥0∞) + h x ∂μ) ≤ ν (E ∩ P) := by
      specialize hpos E hE
      rw [hrapply _ (hE.inter hP)] at hpos
      rw [lintegral_add_left measurable_const, lintegral_const, Measure.restrict_apply_univ]
      exact add_le_of_le_tsub_right_of_le (hh.2 _ (hE.inter hP)) hpos
    have hadm : admissible μ ν (h + P.indicator (fun _ => (c : ℝ≥0∞))) := by
      refine ⟨hh.1.add (measurable_const.indicator hP), fun E hE => ?_⟩
      have hsplit :
          (∫⁻ x in E, (h + P.indicator (fun _ => (c : ℝ≥0∞))) x ∂μ) =
            (∫⁻ x in E ∩ P, (c : ℝ≥0∞) + h x ∂μ) +
            ∫⁻ x in E \ P, h x ∂μ := by
        simp only [lintegral_add_left measurable_const, lintegral_add_left hh.1,
          setLIntegral_const, add_assoc, lintegral_inter_add_sdiff _ _ hP,
          Pi.add_apply, lintegral_indicator hP, Measure.restrict_apply hP]
        rw [inter_comm, add_comm]
      rw [hsplit, ← measure_inter_add_sdiff E hP]
      exact add_le_add (hboost E hE) (hh.2 _ (hE.diff hP))
    have hbound :
        (∫⁻ x, h x + P.indicator (fun _ => (c : ℝ≥0∞)) x ∂μ) ≤
          supremumIntegral μ ν :=
      le_sSup ⟨h + P.indicator (fun _ => (c : ℝ≥0∞)), hadm, rfl⟩
    have hfinite : (∫⁻ x, h x ∂μ) ≠ ∞ :=
      (lt_of_le_of_lt (by simpa using hh.2 univ MeasurableSet.univ)
        (measure_lt_top ν univ)).ne
    apply not_lt_of_ge hbound
    rw [← hmax, lintegral_add_left hh.1, lintegral_indicator hP, setLIntegral_const]
    exact ENNReal.lt_add_right hfinite
      (ENNReal.mul_pos_iff.mpr ⟨ENNReal.coe_pos.mpr hc, hμP⟩).ne'
  exact Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular hrac hsing

theorem rn_positive_finite : Specs.D11.Ch15.RNPositiveFinite.rn_positive_finite := by
  intro X _ μ ν _ _ hac
  obtain ⟨h, hh, hmax, hfin⟩ := exists_maximizer μ ν
  obtain ⟨_, _, _, hradd⟩ := residual_properties μ ν h hh hac
  have hz := residual_vanishes μ ν h hac hh hmax
  have hdensity : μ.withDensity h = ν := by simpa only [hz, zero_add] using hradd
  -- `ofReal ∘ toReal` sets precisely the infinite values to zero. This is a
  -- measurable modification even when the original measure is incomplete.
  let k : X → ℝ≥0∞ := fun x => ENNReal.ofReal (h x).toReal
  have hk : Measurable k := hh.1.ennreal_toReal.ennreal_ofReal
  have hkh : k =ᵐ[μ] h := by
    filter_upwards [hfin] with x hx
    exact ENNReal.ofReal_toReal hx.ne
  have hktotal : (∫⁻ x, k x ∂μ) < ∞ := by
    rw [lintegral_congr_ae hkh, ← setLIntegral_univ,
      ← withDensity_apply _ MeasurableSet.univ, hdensity]
    exact measure_lt_top ν univ
  refine ⟨k, hk, fun x => ENNReal.ofReal_lt_top, ?_, ?_⟩
  · exact (Ch05.NonnegativeIntegral.integral_eq_lintegral μ k).trans_lt hktotal
  · intro E hE
    change ν E = Ch05.NonnegativeIntegral.nonnegativeIntegral (μ.restrict E) k
    rw [Ch05.NonnegativeIntegral.integral_eq_lintegral,
      lintegral_congr_ae (ae_restrict_of_ae hkh), ← withDensity_apply _ hE, hdensity]

theorem density_unique : Specs.D11.Ch15.RNPositiveFinite.density_unique := by
  intro X _ μ ν _ _ h k hh hk hrep krep
  have hdensity : μ.withDensity h = ν := by
    ext E hE
    rw [withDensity_apply _ hE, hrep E hE]
    exact (Ch05.NonnegativeIntegral.integral_eq_lintegral (μ.restrict E) h).symm
  have kdensity : μ.withDensity k = ν := by
    ext E hE
    rw [withDensity_apply _ hE, krep E hE]
    exact (Ch05.NonnegativeIntegral.integral_eq_lintegral (μ.restrict E) k).symm
  exact (withDensity_eq_iff_of_sigmaFinite hh.aemeasurable hk.aemeasurable).mp
    (hdensity.trans kdensity.symm)

theorem rn_positive_finite_real :
    Specs.D11.Ch15.RNPositiveFinite.rn_positive_finite_real := by
  intro X _ μ ν _ _ hac
  obtain ⟨g, hg, hgfin, hgint, hrep⟩ := rn_positive_finite μ ν hac
  let h : X → ℝ := fun x => (g x).toReal
  have hnonneg : ∀ x, 0 ≤ h x := fun x => ENNReal.toReal_nonneg
  have hrecover : (fun x => ENNReal.ofReal (h x)) = g :=
    funext fun x => ENNReal.ofReal_toReal (hgfin x).ne
  have hfinite : (∫⁻ x, g x ∂μ) ≠ ∞ := by
    change Ch05.NonnegativeIntegral.nonnegativeIntegral μ g < ∞ at hgint
    rw [Ch05.NonnegativeIntegral.integral_eq_lintegral] at hgint
    exact hgint.ne
  have hi : Integrable h μ := integrable_toReal_of_lintegral_ne_top hg.aemeasurable hfinite
  refine ⟨h, hg.ennreal_toReal, hnonneg, hi, ?_, ?_⟩
  · intro E hE
    rw [hrecover]
    exact hrep E hE
  · intro E hE
    rw [ofReal_integral_eq_lintegral_ofReal hi.integrableOn
      (Eventually.of_forall hnonneg), hrecover]
    exact (hrep E hE).trans
      (Ch05.NonnegativeIntegral.integral_eq_lintegral (μ.restrict E) g)

theorem real_density_unique : Specs.D11.Ch15.RNPositiveFinite.real_density_unique := by
  intro X _ μ ν _ _ h k hh hk hh0 hk0 hi ki hrep krep
  have heq : (fun x => ENNReal.ofReal (h x)) =ᵐ[μ] (fun x => ENNReal.ofReal (k x)) := by
    apply density_unique μ ν _ _ hh.ennreal_ofReal hk.ennreal_ofReal
    · intro E hE
      change ν E = Ch05.NonnegativeIntegral.nonnegativeIntegral (μ.restrict E) _
      rw [Ch05.NonnegativeIntegral.integral_eq_lintegral,
        ← ofReal_integral_eq_lintegral_ofReal hi.integrableOn
          (Eventually.of_forall hh0)]
      exact hrep E hE
    · intro E hE
      change ν E = Ch05.NonnegativeIntegral.nonnegativeIntegral (μ.restrict E) _
      rw [Ch05.NonnegativeIntegral.integral_eq_lintegral,
        ← ofReal_integral_eq_lintegral_ofReal ki.integrableOn
          (Eventually.of_forall hk0)]
      exact krep E hE
  filter_upwards [heq] with x hx
  have hx' := congrArg ENNReal.toReal hx
  simpa only [ENNReal.toReal_ofReal (hh0 x), ENNReal.toReal_ofReal (hk0 x)] using hx'

end D11.Ch15.RNPositiveFinite
