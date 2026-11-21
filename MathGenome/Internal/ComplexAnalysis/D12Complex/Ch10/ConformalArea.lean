import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch10.ConformalArea
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch01.RealComplexDifferential
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.UnivalentHolomorphicInverse
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace D12Complex.ConformalArea

theorem real_jacobian : Specs.D12Complex.Ch10.ConformalArea.real_jacobian_type := by
  intro Ω f hf z hz
  exact (realDifferential_det f (deriv f z) z
    ((hasComplexDerivativeAt_iff f _ z).mpr (hf.2 z hz).hasDerivAt)).1

private lemma real_derivative {Ω : Set ℂ} {f : ℂ → ℂ} (hf : HolomorphicOn Ω f)
    {E : Set ℂ} (hEΩ : E ⊆ Ω) :
    ∀ z ∈ E, HasFDerivWithinAt f (fderiv ℝ f z) E z :=
  fun z hz => ((hf.2 z (hEΩ hz)).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt

private lemma abs_jacobian {Ω : Set ℂ} {f : ℂ → ℂ} (hf : HolomorphicOn Ω f)
    {z : ℂ} (hz : z ∈ Ω) : |(fderiv ℝ f z).det| = ‖deriv f z‖ ^ 2 := by
  rw [real_jacobian Ω f hf z hz, abs_of_nonneg (sq_nonneg _)]

theorem image_nullMeasurable :
    Specs.D12Complex.Ch10.ConformalArea.image_nullMeasurable_type := by
  intro Ω E f hf hi hE hEΩ
  exact nullMeasurable_image_of_fderivWithin volume hE (real_derivative hf hEΩ) (hi.mono hEΩ)

theorem area : Specs.D12Complex.Ch10.ConformalArea.area_type := by
  intro Ω E f hf hi hE hEΩ
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image₀ volume hE
    (real_derivative hf hEΩ) (hi.mono hEΩ)]
  apply setLIntegral_congr_fun₀ hE
  intro z hz
  dsimp only
  rw [abs_jacobian hf (hEΩ hz)]

/-- A Borel core differs by a null set whose image is also null. This is the
completion step needed to apply the weighted Borel change-of-variables results. -/
private lemma measurable_core {Ω E : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (hE : NullMeasurableSet E volume) (hEΩ : E ⊆ Ω) :
    ∃ S : Set ℂ, S ⊆ E ∧ MeasurableSet S ∧ S =ᵐ[volume] E ∧
      f '' S =ᵐ[volume] f '' E := by
  obtain ⟨S, hSE, hS, hSEae⟩ := hE.exists_measurable_subset_ae_eq
  refine ⟨S, hSE, hS, hSEae, ?_⟩
  have hn : volume (E \ S) = 0 := (ae_eq_set.mp hSEae).2
  have him : volume (f '' (E \ S)) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun z hz => (real_derivative hf hEΩ z hz.1).differentiableWithinAt.mono sdiff_subset) hn
  have heq : E = S ∪ (E \ S) := by rw [union_sdiff_cancel hSE]
  rw [heq, image_union]
  exact (union_ae_eq_left_of_ae_eq_empty (ae_eq_empty.mpr him)).symm

/-- The domain assumption in the upstream univalence theorem is local:
every point of an arbitrary open set has a disk contained in that set. -/
private lemma deriv_ne_zero {Ω : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (hi : InjOn f Ω) {z : ℂ} (hz : z ∈ Ω) :
    deriv f z ≠ 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hf.1 z hz
  have hdom : IsDomain (Metric.ball z r) :=
    (isDomain_iff _).mpr ⟨isOpen_ball, isConnected_ball hr⟩
  exact UnivalentHolomorphicInverse.injective_holomorphic_deriv_ne_zero
    (Metric.ball z r) f hdom ⟨isOpen_ball, fun w hw => hf.2 w (hball hw)⟩
      (hi.mono hball) z (Metric.mem_ball_self hr)

theorem measurable_composition :
    Specs.D12Complex.Ch10.ConformalArea.measurable_composition_type := by
  intro Ω E f hf hi hE hEΩ h hh
  let J : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal |(fderiv ℝ f z).det|
  have hdΩ := real_derivative hf (Subset.rfl : Ω ⊆ Ω)
  have hJΩ : AEMeasurable J (volume.restrict Ω) :=
    aemeasurable_ofReal_abs_det_fderivWithin volume hf.1.measurableSet hdΩ
  have hJ : AEMeasurable J (volume.restrict E) :=
    hJΩ.mono_measure (Measure.restrict_mono_set volume hEΩ)
  have hJpos : ∀ᵐ z ∂volume.restrict E, J z ≠ 0 := by
    apply (ae_restrict_iff'₀ hE).mpr
    exact ae_of_all _ (fun z hz => by
      dsimp [J]
      rw [abs_jacobian hf (hEΩ hz)]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr
        (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (deriv_ne_zero hf hi (hEΩ hz))))))
  have hac : volume.restrict E ≪ (volume.restrict E).withDensity J :=
    withDensity_absolutelyContinuous' hJ hJpos
  have hfm : AEMeasurable f (volume.restrict E) :=
    (show ContinuousOn f E from fun z hz =>
      (hf.2 z (hEΩ hz)).continuousAt.continuousWithinAt).aemeasurable₀ hE
  have hfd : AEMeasurable f ((volume.restrict E).withDensity J) :=
    hfm.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmap : Measure.map f ((volume.restrict E).withDensity J) =
      volume.restrict (f '' E) :=
    map_withDensity_abs_det_fderiv_eq_addHaar volume hE
      (real_derivative hf hEΩ) (hi.mono hEΩ)
  have hhE : AEMeasurable h (volume.restrict (f '' E)) :=
    hh.mono_measure (Measure.restrict_mono_set volume (image_mono hEΩ))
  have hcomp : AEMeasurable (fun z => h (f z)) (volume.restrict E) := by
    rw [← hmap] at hhE
    exact (hhE.comp_aemeasurable hfd).mono_ac hac
  refine ⟨hcomp, hcomp.mul ?_⟩
  apply hJ.congr
  apply (ae_restrict_iff'₀ hE).mpr
  exact ae_of_all _ (fun z hz => by dsimp [J]; rw [abs_jacobian hf (hEΩ hz)])

theorem lintegral_changeOfVariables :
    Specs.D12Complex.Ch10.ConformalArea.lintegral_changeOfVariables_type := by
  intro Ω E f hf hi hE hEΩ h _
  obtain ⟨S, hSE, hS, hSEae, him⟩ := measurable_core hf hE hEΩ
  rw [← setLIntegral_congr him, ← setLIntegral_congr hSEae,
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
      (real_derivative hf (hSE.trans hEΩ)) (hi.mono (hSE.trans hEΩ)) h]
  apply setLIntegral_congr_fun hS
  intro z hz
  dsimp only
  rw [abs_jacobian hf (hEΩ (hSE hz)), mul_comm]

private lemma scalar_changeOfVariables {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Ω E : Set ℂ} {f : ℂ → ℂ}
    (hf : HolomorphicOn Ω f) (hi : InjOn f Ω)
    (hE : NullMeasurableSet E volume) (hEΩ : E ⊆ Ω) (h : ℂ → F) :
    (IntegrableOn h (f '' E) ↔
      IntegrableOn (fun z => (‖deriv f z‖ ^ 2) • h (f z)) E) ∧
    (∫ w in f '' E, h w) = ∫ z in E, (‖deriv f z‖ ^ 2) • h (f z) := by
  obtain ⟨S, hSE, hS, hSEae, him⟩ := measurable_core hf hE hEΩ
  have hd := real_derivative hf (hSE.trans hEΩ)
  have hj : (fun z => |(fderiv ℝ f z).det| • h (f z)) =ᵐ[volume.restrict S]
      (fun z => (‖deriv f z‖ ^ 2) • h (f z)) := by
    apply (ae_restrict_iff' hS).mpr
    exact ae_of_all _ (fun z hz => by dsimp only; rw [abs_jacobian hf (hEΩ (hSE hz))])
  constructor
  · rw [integrableOn_congr_set_ae him.symm, integrableOn_congr_set_ae hSEae.symm]
    exact (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hS hd
      (hi.mono (hSE.trans hEΩ)) h).trans (integrable_congr hj)
  · rw [← setIntegral_congr_set him, ← setIntegral_congr_set hSEae,
      integral_image_eq_integral_abs_det_fderiv_smul volume hS hd
        (hi.mono (hSE.trans hEΩ)) h]
    exact integral_congr_ae hj

theorem integral_real_changeOfVariables :
    Specs.D12Complex.Ch10.ConformalArea.integral_real_changeOfVariables_type := by
  intro Ω E f hf hi hE hEΩ h hh
  obtain ⟨hint, heq⟩ := scalar_changeOfVariables hf hi hE hEΩ h
  simpa only [smul_eq_mul, mul_comm] using And.intro (hint.mp hh) heq

theorem integral_complex_changeOfVariables :
    Specs.D12Complex.Ch10.ConformalArea.integral_complex_changeOfVariables_type := by
  intro Ω E f hf hi hE hEΩ h hh
  obtain ⟨hint, heq⟩ := scalar_changeOfVariables hf hi hE hEΩ h
  simpa only [Complex.real_smul, mul_comm] using And.intro (hint.mp hh) heq

end D12Complex.ConformalArea
