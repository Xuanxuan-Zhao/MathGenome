import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.IntegralOperators.VolterraTraceCounterexample
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.HilbertSchmidtKernels
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.TraceIdeals.TraceClassDefinitions
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Logic.Equiv.Nat
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.OpenPos
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fredholm.CompactNonzeroSpectrum
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

noncomputable section
open MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology
namespace ExpandedFA.IntegralOperators.VolterraTraceCounterexample

open Spec

/-- The original Volterra integral, as a continuous linear map on L²(0,1). -/
abbrev volterra (𝕜 : Type) [RCLike 𝕜] := VolterraValue 𝕜

theorem integral_formula : Spec.IntegralFormula := by
  intro 𝕜 _ f
  have h := ExpandedFA.PartV.L2Kernel.kernel_representative_formula
    intervalMeasure intervalMeasure (rawKernel 𝕜) f (rawKernel_memLp 𝕜) (Lp.memLp f)
  have hf : (Lp.memLp f).toLp (f : ℝ → 𝕜) = f := Lp.toLp_coeFn f _
  rw [hf] at h
  change (VolterraValue 𝕜 f : ℝ → 𝕜) =ᵐ[intervalMeasure]
    (fun x => ∫ y, rawKernel 𝕜 (x,y) * f y ∂intervalMeasure) at h
  filter_upwards [h, ae_restrict_mem measurableSet_Ioo] with x hx hxm
  rw [hx]
  have heq : (fun t => rawKernel 𝕜 (x,t) * f t) = (Set.Iio x).indicator f := by
    funext t
    simp only [rawKernel, Set.indicator_apply, Set.mem_Iio]
    split <;> simp_all
  have hset : Set.Iio x ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo 0 x := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hxm.2⟩⟩
  rw [heq, integral_indicator measurableSet_Iio]
  change (∫ t, f t ∂((volume.restrict (Set.Ioo (0 : ℝ) 1)).restrict (Set.Iio x))) = _
  rw [Measure.restrict_restrict measurableSet_Iio, hset]

theorem hilbertSchmidt (𝕜 : Type) [RCLike 𝕜] :
    TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue (volterra 𝕜) := by
  exact (ExpandedFA.TraceIdeals.HilbertSchmidtKernels.kernel_isometry
    intervalMeasure intervalMeasure (kernelValue 𝕜)).1

theorem compact (𝕜 : Type) [RCLike 𝕜] :
    Compactness.DefinitionsSpec.IsCompactLinearMapValue (volterra 𝕜).toLinearMap := by
  exact ExpandedFA.TraceIdeals.HilbertSchmidtBasis.compactness
    (volterra 𝕜) (hilbertSchmidt 𝕜)

/-- A section of the triangular indicator has length x. -/
lemma kernel_section_square (𝕜 : Type) [RCLike 𝕜] {x : ℝ}
    (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ t, ‖rawKernel 𝕜 (x,t)‖ ^ 2 ∂intervalMeasure) = x := by
  have heq : (fun t => ‖rawKernel 𝕜 (x,t)‖ ^ 2) =
      (Set.Iio x).indicator (fun _ => (1 : ℝ)) := by
    funext t
    simp only [rawKernel, Set.indicator_apply, Set.mem_Iio]
    split <;> simp_all
  rw [heq, integral_indicator measurableSet_Iio, intervalMeasure,
    Measure.restrict_restrict measurableSet_Iio]
  have hset : Set.Iio x ∩ Set.Ioo (0 : ℝ) 1 = Set.Ioo 0 x := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioo]
    exact ⟨fun h => ⟨h.2.1, h.1⟩, fun h => ⟨h.2, h.1, h.2.trans hx.2⟩⟩
  rw [hset, setIntegral_const]
  simp [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal hx.1.le]

/-- The squared L² norm of the actual kernel, including its normalization. -/
theorem kernel_square_norm (𝕜 : Type) [RCLike 𝕜] :
    ‖kernelValue 𝕜‖ ^ 2 = 1 / 2 := by
  rw [kernelValue, ← ExpandedFA.PartV.L2Kernel.integral_sq_norm _ (rawKernel_memLp 𝕜)]
  have hi := (memLp_two_iff_integrable_sq_norm
    (rawKernel_memLp 𝕜).aestronglyMeasurable).mp (rawKernel_memLp 𝕜)
  rw [integral_prod _ hi]
  calc
    _ = ∫ x, x ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      exact kernel_section_square 𝕜 hx
    _ = 1 / 2 := by
      rw [intervalMeasure, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), integral_id]
      norm_num

/-- The Hilbert–Schmidt norm has the same square, by the canonical kernel isometry. -/
theorem hilbertSchmidt_square_norm : Spec.HilbertSchmidtSquareNorm := by
  intro 𝕜 _ hh
  have h : TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtNormValue
      ⟨volterra 𝕜, hh⟩ = ‖kernelValue 𝕜‖ :=
    (ExpandedFA.TraceIdeals.HilbertSchmidtKernels.kernel_isometry
      intervalMeasure intervalMeasure (kernelValue 𝕜)).2 hh
  exact (congrArg (fun x : ℝ => x ^ 2) h).trans (kernel_square_norm 𝕜)

lemma singularValue_positive (n : ℕ) : 0 < singularValue n := by
  unfold singularValue
  positivity

/-- The explicit singular-value list is not summable; this does not assume
that it has already been identified with the singular values of V. -/
theorem singularValue_not_summable : ¬ Summable singularValue := by
  have hdiv : ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) + 1 / 2)) := by
    have h := Real.summable_one_div_nat_add_rpow (1 / 2) 1
    simp only [Real.rpow_one] at h
    have heq : (fun n : ℕ => 1 / |(n : ℝ) + 1 / 2|) =
        (fun n : ℕ => 1 / ((n : ℝ) + 1 / 2)) := by
      funext n
      rw [abs_of_pos (by positivity)]
    rw [heq] at h
    exact fun hs => (lt_irrefl (1 : ℝ)) (h.mp hs)
  intro hs
  apply hdiv
  convert hs.mul_right Real.pi using 1
  funext n
  simp only [singularValue, mul_inv_rev, one_div]
  field_simp

/-- Once the exact singular values are established, the existing S₁ definition
immediately rules out trace class, without a Lidskii assumption. -/
theorem notTraceClass_of_singularValues
    (hs : Spec.SingularValues) : Spec.NotTraceClass := by
  intro 𝕜 _ h
  apply singularValue_not_summable
  exact h.2.congr (hs 𝕜)

/-- A globally continuous primitive of an integrable function on the unit interval. -/
def intervalPrimitive {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (x : ℝ) : 𝕜 :=
  ∫ t in (0 : ℝ)..x, (Ioo (0 : ℝ) 1).indicator f t

lemma intervalPrimitive_continuous {𝕜 : Type} [RCLike 𝕜] {f : ℝ → 𝕜}
    (hf : IntegrableOn f (Ioo 0 1)) : Continuous (intervalPrimitive f) :=
  ((integrable_indicator_iff measurableSet_Ioo).mpr hf).continuous_primitive 0

lemma intervalPrimitive_zero {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) :
    intervalPrimitive f 0 = 0 := by simp [intervalPrimitive]

lemma intervalPrimitive_eq_integral {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    intervalPrimitive f x = ∫ t in Ioo 0 x, f t := by
  dsimp [intervalPrimitive]
  rw [intervalIntegral.integral_of_le hx.1, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  exact Set.indicator_of_mem (s := Ioo (0 : ℝ) 1) ⟨ht.1, ht.2.trans_le hx.2⟩ f

/-- Uniqueness of the homogeneous integration eigen-equation on a finite interval.
The equation is initially only a.e., and its unknown need only be integrable. -/
lemma integral_eigenfunction_eq_zero {𝕜 : Type} [RCLike 𝕜]
    {f : ℝ → 𝕜} (hf : IntegrableOn f (Ioo 0 1)) {z : 𝕜} (hz : z ≠ 0)
    (he : (fun x => ∫ t in Ioo 0 x, f t) =ᵐ[volume.restrict (Ioo 0 1)]
      fun x => z * f x) :
    f =ᵐ[volume.restrict (Ioo 0 1)] 0 := by
  let F := intervalPrimitive f
  have hF : Continuous F := intervalPrimitive_continuous hf
  have hF_eq {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
      F x = ∫ t in Ioo 0 x, f t := intervalPrimitive_eq_integral f hx
  let g : ℝ → 𝕜 := fun x => z⁻¹ * F x
  have hg : Continuous g := continuous_const.mul hF
  have hfg : f =ᵐ[volume.restrict (Ioo 0 1)] g := by
    filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    dsimp [g]
    rw [hF_eq (Ioo_subset_Icc_self hxm), hx, inv_mul_cancel_left₀ hz]
  let G : ℝ → 𝕜 := fun x => ∫ t in (0 : ℝ)..x, g t
  have hG : Continuous G := intervalIntegral.continuous_primitive
    (fun a b => hg.intervalIntegrable a b) 0
  have hGF {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : G x = F x := by
    dsimp [G]
    rw [intervalIntegral.integral_of_le hx.1, integral_Ioc_eq_integral_Ioo, hF_eq hx]
    apply integral_congr_ae
    have hsub : Ioo (0 : ℝ) x ⊆ Ioo 0 1 := fun t ht => ⟨ht.1, ht.2.trans_le hx.2⟩
    exact Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hsub hfg)
  have hG' (x : ℝ) : HasDerivAt G (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 x)
      hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have hzero : ∀ x ∈ Icc (0 : ℝ) 1, G x = 0 := by
    apply eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right (K := ‖z⁻¹‖) hG.continuousOn
      (fun x _ => (hG' x).hasDerivWithinAt) (by simp [G])
    intro x hx
    dsimp [g]
    rw [← hGF (Ico_subset_Icc_self hx), norm_mul]
  filter_upwards [hfg, ae_restrict_mem measurableSet_Ioo] with x hx hxm
  rw [hx]
  change z⁻¹ * F x = 0
  rw [← hGF (Ioo_subset_Icc_self hxm), hzero x (Ioo_subset_Icc_self hxm), mul_zero]

lemma integral_not_eq_one {𝕜 : Type} [RCLike 𝕜]
    {f : ℝ → 𝕜} (hf : IntegrableOn f (Ioo 0 1))
    (he : (fun x => ∫ t in Ioo 0 x, f t) =ᵐ[volume.restrict (Ioo 0 1)]
      fun _ => (1 : 𝕜)) : False := by
  have hF : Continuous (intervalPrimitive f) := intervalPrimitive_continuous hf
  have hFone : intervalPrimitive f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)]
      fun _ => (1 : 𝕜) := by
    filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    rw [intervalPrimitive_eq_integral f (Ioo_subset_Icc_self hxm), hx]
  have hEq := Measure.eqOn_open_of_ae_eq hFone isOpen_Ioo hF.continuousOn continuousOn_const
  have hclosure := hEq.closure hF continuous_const
  have h0 : (0 : ℝ) ∈ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  have hbad := hclosure h0
  simp [intervalPrimitive_zero] at hbad

/-- The a.e. eigen-equation bootstraps to a continuous representative;
ODE uniqueness then rules out every nonzero real or complex eigenvalue. -/
theorem no_nonzero_eigenvalue : Spec.NoNonzeroEigenvalue := by
  intro 𝕜 _ z hz f he
  have hrep : (volterra 𝕜 f : ℝ → 𝕜) =ᵐ[intervalMeasure]
      fun x => z * f x := by
    rw [he]
    exact Lp.coeFn_smul z f
  have hzero := integral_eigenfunction_eq_zero
    ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hz
    ((integral_formula 𝕜 f).symm.trans hrep)
  apply Lp.ext
  exact hzero.trans (Lp.coeFn_zero 𝕜 2 intervalMeasure).symm

/-- A continuous primitive vanishes at zero, so the constant class one
cannot belong to the range of Volterra. -/
theorem not_surjective (𝕜 : Type) [RCLike 𝕜] :
    ¬ Function.Surjective (volterra 𝕜) := by
  intro hs
  obtain ⟨f, hf⟩ := hs (Lp.const 2 intervalMeasure (1 : 𝕜))
  apply integral_not_eq_one ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
  have hrep := Lp.coeFn_const 2 intervalMeasure (1 : 𝕜)
  rw [← hf] at hrep
  exact (integral_formula 𝕜 f).symm.trans hrep

/-- Compact spectral theory and the eigenvalue obstruction give precisely
zero spectrum. Non-surjectivity supplies membership of zero over both fields. -/
theorem zero_spectrum : Spec.ZeroSpectrum := by
  intro 𝕜 _
  ext z
  rw [Set.mem_singleton_iff]
  constructor
  · intro hz
    by_contra hz0
    obtain ⟨f, hf, he⟩ :=
      (ExpandedFA.Fredholm.compact_nonzero_spectrum_iff_eigenvalue
        (volterra 𝕜) (compact 𝕜) z hz0).mp hz
    exact hf (no_nonzero_eigenvalue 𝕜 z hz0 f he)
  · rintro rfl
    apply (spectrum.zero_mem_iff 𝕜).mpr
    intro hu
    exact not_surjective 𝕜 (ContinuousLinearMap.isUnit_iff_bijective.mp hu).2

/-- Scalar embedding into complex L² preserves the actual quotient norm. -/
lemma complexify_norm (𝕜 : Type) [RCLike 𝕜] (f : Space 𝕜) :
    ‖(RCLike.map 𝕜 ℂ).compLp f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
  filter_upwards [(RCLike.map 𝕜 ℂ).coeFn_compLp f] with t ht
  rw [ht]
  exact RCLike.norm_to_complex (f t)

/-- The representative formula identifies the independently chosen integral
operators under scalar embedding. -/
lemma complexify_volterra (hV : Spec.IntegralFormula) (𝕜 : Type) [RCLike 𝕜] (f : Space 𝕜) :
    (RCLike.map 𝕜 ℂ).compLp (VolterraValue 𝕜 f) =
      VolterraValue ℂ ((RCLike.map 𝕜 ℂ).compLp f) := by
  apply Lp.ext
  filter_upwards [(RCLike.map 𝕜 ℂ).coeFn_compLp (VolterraValue 𝕜 f),
    hV 𝕜 f, hV ℂ ((RCLike.map 𝕜 ℂ).compLp f),
    ae_restrict_mem measurableSet_Ioo] with x hmap hv hc hx
  rw [hmap, hv, hc]
  have hsub : Ioo (0 : ℝ) x ⊆ Ioo 0 1 := fun t ht => ⟨ht.1, ht.2.trans hx.2⟩
  have hi : IntegrableOn (f : ℝ → 𝕜) (Ioo 0 x) :=
    IntegrableOn.mono_set ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) hsub
  rw [← (RCLike.map 𝕜 ℂ).integral_comp_comm hi]
  exact integral_congr_ae (Filter.EventuallyEq.symm (ae_restrict_of_ae_restrict_of_subset hsub
    ((RCLike.map 𝕜 ℂ).coeFn_compLp f)))

/-- The same embedding intertwines every iterate of the original operators. -/
lemma complexify_volterra_pow (hV : Spec.IntegralFormula) (𝕜 : Type) [RCLike 𝕜]
    (n : ℕ) (f : Space 𝕜) :
    (RCLike.map 𝕜 ℂ).compLp (((VolterraValue 𝕜)^n) f) =
      ((VolterraValue ℂ)^n) ((RCLike.map 𝕜 ℂ).compLp f) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ', mul_apply_eq_comp]
    rw [complexify_volterra hV, ih]

/-- Isometry and intertwining bound each real or complex power by the
corresponding power on complex L². -/
lemma volterra_pow_norm_le_complex (hV : Spec.IntegralFormula) (𝕜 : Type) [RCLike 𝕜]
    (n : ℕ) : ‖(VolterraValue 𝕜)^n‖ ≤ ‖(VolterraValue ℂ)^n‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  rw [← complexify_norm 𝕜 (((VolterraValue 𝕜)^n) f), complexify_volterra_pow hV]
  calc
    _ ≤ ‖(VolterraValue ℂ)^n‖ * ‖(RCLike.map 𝕜 ℂ).compLp f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [complexify_norm]

/-- Gelfand's formula turns the complex zero spectrum into a norm-root limit. -/
lemma complex_quasinilpotent :
    Filter.Tendsto (fun n : ℕ => ‖(VolterraValue ℂ) ^ (n + 1)‖ ^
      (1 / ((n + 1 : ℕ) : ℝ))) Filter.atTop (𝓝 0) := by
  have hr : spectralRadius ℂ (VolterraValue ℂ) = 0 := by
    simp [spectralRadius_eq_of_unital, zero_spectrum ℂ]
  have h := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (VolterraValue ℂ)
  rw [hr] at h
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp h
  have ht' : Filter.Tendsto (fun n : ℕ => ‖(VolterraValue ℂ) ^ n‖ ^ (1 / (n : ℝ)))
      Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, ← ENNReal.toReal_rpow, toReal_coe_nnnorm,
      ENNReal.toReal_zero] using ht
  exact ht'.comp (Filter.tendsto_add_atTop_nat 1)

/-- Volterra is quasinilpotent over both scalar fields, in the norm-root sense. -/
theorem quasinilpotent : Spec.Quasinilpotent := by
  intro 𝕜 _
  apply squeeze_zero (fun n => Real.rpow_nonneg (norm_nonneg _) _)
    (fun n => Real.rpow_le_rpow (norm_nonneg _)
      (volterra_pow_norm_le_complex integral_formula 𝕜 (n + 1)) (by positivity))
    complex_quasinilpotent

lemma integral_function_injective {𝕜 : Type} [RCLike 𝕜]
    {f : ℝ → 𝕜} (hf : IntegrableOn f (Ioo 0 1))
    (he : (fun x => ∫ t in Ioo 0 x, f t) =ᵐ[volume.restrict (Ioo 0 1)] 0) :
    f =ᵐ[volume.restrict (Ioo 0 1)] 0 := by
  have hF : Continuous (intervalPrimitive f) := intervalPrimitive_continuous hf
  have hFzero : intervalPrimitive f =ᵐ[volume.restrict (Ioo (0 : ℝ) 1)] 0 := by
    filter_upwards [he, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    rw [intervalPrimitive_eq_integral f (Ioo_subset_Icc_self hxm), hx]
  have hEq := Measure.eqOn_open_of_ae_eq hFzero isOpen_Ioo hF.continuousOn continuousOn_const
  have hfi := (integrable_indicator_iff measurableSet_Ioo).mpr hf
  have hderiv := LocallyIntegrable.ae_hasDerivAt_integral hfi.locallyIntegrable
  filter_upwards [ae_restrict_of_ae hderiv, ae_restrict_mem measurableSet_Ioo] with x hx hxm
  have hd := hx 0
  rw [Set.indicator_of_mem hxm] at hd
  apply hd.unique
  apply (hasDerivAt_const x (0 : 𝕜)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hxm] with y hy
  exact hEq hy

lemma injective (𝕜 : Type) [RCLike 𝕜] : Function.Injective (volterra 𝕜) := by
  have hz (f : Space 𝕜) (hf : volterra 𝕜 f = 0) : f = 0 := by
    apply Lp.ext
    have hrep : (volterra 𝕜 f : ℝ → 𝕜) =ᵐ[intervalMeasure] 0 := by
      rw [hf]
      exact Lp.coeFn_zero 𝕜 2 intervalMeasure
    exact (integral_function_injective
      ((Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      ((integral_formula 𝕜 f).symm.trans hrep)).trans (Lp.coeFn_zero 𝕜 2 intervalMeasure).symm
  intro f g hfg
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, hfg, sub_self]

lemma adjoint_formula (𝕜 : Type) [RCLike 𝕜] (g : Space 𝕜) :
    (ContinuousLinearMap.adjoint (volterra 𝕜) g : ℝ → 𝕜) =ᵐ[intervalMeasure]
      fun t => ∫ x in Ioo t 1, g x := by
  have h := ((ExpandedFA.PartV.L2KernelCompact.l2_kernel_adjoint_correct
    intervalMeasure intervalMeasure (kernelValue 𝕜)).2 g).2
  have hk : (kernelValue 𝕜 : ℝ × ℝ → 𝕜) =ᵐ[intervalMeasure.prod intervalMeasure]
      rawKernel 𝕜 := (rawKernel_memLp 𝕜).coeFn_toLp
  have hs := (Measure.measurePreserving_swap (μ := intervalMeasure) (ν := intervalMeasure)).quasiMeasurePreserving.ae_eq_comp hk
  change (ContinuousLinearMap.adjoint (volterra 𝕜) g : ℝ → 𝕜) =ᵐ[intervalMeasure]
    (fun t => ∫ x, star ((kernelValue 𝕜) (x,t)) * g x ∂intervalMeasure) at h
  filter_upwards [h, Measure.ae_ae_of_ae_prod hs, ae_restrict_mem measurableSet_Ioo] with t ht hkt htm
  rw [ht]
  calc
    _ = ∫ x, star (rawKernel 𝕜 (x,t)) * g x ∂intervalMeasure := by
      apply integral_congr_ae
      filter_upwards [hkt] with x hx
      change kernelValue 𝕜 (x,t) = rawKernel 𝕜 (x,t) at hx
      rw [hx]
    _ = ∫ x in Ioo t 1, g x := by
      have heq : (fun x => star (rawKernel 𝕜 (x,t)) * g x) = (Ioi t).indicator g := by
        funext x
        simp only [rawKernel, Set.indicator_apply, Set.mem_Ioi]
        split <;> simp_all
      rw [heq, integral_indicator measurableSet_Ioi]
      change (∫ x, g x ∂((volume.restrict (Ioo (0 : ℝ) 1)).restrict (Ioi t))) = _
      rw [Measure.restrict_restrict measurableSet_Ioi]
      congr 2
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioo]
      exact ⟨fun hx => ⟨hx.1, hx.2.2⟩,
        fun hx => ⟨hx.1, htm.1.trans hx.1, hx.2⟩⟩


def exponentialFunction (n : ℤ) (x : ℝ) : ℂ := fourier n (x : AddCircle (1 : ℝ))

lemma exponentialFunction_continuous (n : ℤ) : Continuous (exponentialFunction n) :=
  (fourier n).continuous.comp (AddCircle.continuous_mk' (1 : ℝ))

lemma exponentialFunction_norm (n : ℤ) (x : ℝ) : ‖exponentialFunction n x‖ = 1 := by
  exact Circle.norm_coe _

lemma exponentialFunction_memLp (n : ℤ) : MemLp (exponentialFunction n) 2 intervalMeasure := by
  apply MemLp.of_bound (C := 1) (exponentialFunction_continuous n).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => (exponentialFunction_norm n x).le

def exponentialVector (n : ℤ) : Space ℂ :=
  (exponentialFunction_memLp n).toLp (exponentialFunction n)

lemma exponentialVector_ae (n : ℤ) : (exponentialVector n : ℝ → ℂ) =ᵐ[intervalMeasure]
    exponentialFunction n := (exponentialFunction_memLp n).coeFn_toLp

lemma intervalMeasure_eq_Ioc : intervalMeasure = volume.restrict (Ioc (0 : ℝ) 1) := by
  exact (restrict_Ioo_eq_restrict_Ioc : volume.restrict (Ioo (0 : ℝ) 1) = volume.restrict (Ioc 0 1))

lemma intervalIntegral_unit_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → E) : (∫ x in (0 : ℝ)..1, f x) = ∫ x, f x ∂intervalMeasure := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), intervalMeasure_eq_Ioc]

lemma exponential_coefficient (f : Space ℂ) (n : ℤ) :
    inner ℂ (exponentialVector n) f = fourierCoeffOn (by norm_num : (0 : ℝ) < 1) f n := by
  rw [L2.inner_def, fourierCoeffOn_eq_integral]
  simp only [sub_zero, one_div_one, one_smul, intervalIntegral_unit_eq]
  apply integral_congr_ae
  filter_upwards [exponentialVector_ae n] with x hx
  simp only [RCLike.inner_apply', hx, exponentialFunction, ← fourier_neg, smul_eq_mul]
  simp only [fourier_coe_apply, sub_zero]

lemma exponential_coefficient_self (j i : ℤ) :
    fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (exponentialFunction j) i =
      if i = j then 1 else 0 := by
  let : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
  have h : fourierCoeffOn (by norm_num : (0 : ℝ) < 1) (exponentialFunction j) i =
      fourierCoeff (T := (1 : ℝ)) (fourier j) i := by
    rw [fourierCoeffOn_eq_integral, fourierCoeff_eq_intervalIntegral _ _ 0]
    simp only [sub_zero, zero_add, one_div_one, one_smul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [exponentialFunction, fourier_coe_apply, sub_zero]
  rw [h, fourierCoeff_fourier]
  simp [Pi.single_apply, eq_comm]

lemma orthonormal_exponentialVector : Orthonormal ℂ exponentialVector := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [exponential_coefficient]
  have hj : (exponentialVector j : ℝ → ℂ) =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      exponentialFunction j := by
    rw [← intervalMeasure_eq_Ioc]
    exact exponentialVector_ae j
  rw [fourierCoeffOn_congr_ae (by norm_num : (0 : ℝ) < 1) hj]
  exact exponential_coefficient_self j i

lemma exponential_parseval (f : Space ℂ) :
    HasSum (fun n : ℤ => ‖inner ℂ (exponentialVector n) f‖ ^ 2) (‖f‖ ^ 2) := by
  have hf : MemLp (f : ℝ → ℂ) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
    rw [← intervalMeasure_eq_Ioc]
    exact Lp.memLp f
  have h := hasSum_sq_fourierCoeffOn (by norm_num : (0 : ℝ) < 1) hf
  simp only [sub_zero, inv_one, one_smul, ← exponential_coefficient, intervalIntegral_unit_eq] at h
  convert h using 1
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  congr 1
  funext x
  rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re]

lemma exponential_dense_span :
    (Submodule.span ℂ (range exponentialVector)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  have hz : ∀ n : ℤ, inner ℂ (exponentialVector n) f = 0 := by
    intro n
    exact (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.subset_span (mem_range_self n))
  have h := exponential_parseval f
  simp only [hz, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  have hn : ‖f‖ ^ 2 = 0 := h.unique hasSum_zero
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg f])

def exponentialBasis : HilbertBasis ℤ ℂ (Space ℂ) :=
  HilbertBasis.mk orthonormal_exponentialVector exponential_dense_span.ge

lemma exponentialBasis_apply (n : ℤ) : exponentialBasis n = exponentialVector n :=
  congrFun (HilbertBasis.coe_mk _ _) n

lemma exponentialBasis_ae (n : ℤ) : (exponentialBasis n : ℝ → ℂ) =ᵐ[intervalMeasure]
    exponentialFunction n := by
  rw [exponentialBasis_apply]
  exact exponentialVector_ae n


-- Paste after the genuine complex interval Fourier basis declarations.
def exponentialFrequency (n : ℤ) : ℂ := 2 * Real.pi * Complex.I * n

lemma exponentialFrequency_ne_zero {n : ℤ} (hn : n ≠ 0) : exponentialFrequency n ≠ 0 := by
  unfold exponentialFrequency
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hn)

lemma exponentialFunction_formula (n : ℤ) (x : ℝ) :
    exponentialFunction n x = Complex.exp (exponentialFrequency n * x) := by
  simp only [exponentialFunction, fourier_coe_apply, Complex.ofReal_one, div_one, exponentialFrequency]

lemma lower_integral_exponential {n : ℤ} (hn : n ≠ 0) {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in Ioo 0 x, exponentialFunction n t) =
      (exponentialFrequency n)⁻¹ * (exponentialFunction n x - 1) := by
  simp_rw [exponentialFunction_formula]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx,
    integral_exp_mul_complex (exponentialFrequency_ne_zero hn)]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [div_eq_inv_mul]


lemma volterra_exponential (hV : IntegralFormula) (b : HilbertBasis ℤ ℂ (Space ℂ))
    (hb : ∀ n, (b n : ℝ → ℂ) =ᵐ[intervalMeasure] exponentialFunction n)
    {n : ℤ} (hn : n ≠ 0) :
    VolterraValue ℂ (b n) = (exponentialFrequency n)⁻¹ • (b n - b 0) := by
  apply Lp.ext
  have hc := Lp.coeFn_smul (exponentialFrequency n)⁻¹ (b n - b 0)
  have hd := Lp.coeFn_sub (b n) (b 0)
  filter_upwards [hV ℂ (b n), hb n, hb 0, hc, hd,
    ae_restrict_mem measurableSet_Ioo] with x hv hbn hb0 hc hd hx
  simp only [Pi.smul_apply, Pi.sub_apply] at hc hd
  rw [hv, hc, hd, hbn, hb0]
  change (∫ t in Ioo 0 x, b n t) =
    (exponentialFrequency n)⁻¹ * (exponentialFunction n x - exponentialFunction 0 x)
  have hi : (∫ t in Ioo 0 x, b n t) = ∫ t in Ioo 0 x, exponentialFunction n t := by
    apply integral_congr_ae
    exact ae_restrict_of_ae_restrict_of_subset
      (show Ioo (0 : ℝ) x ⊆ Ioo 0 1 from fun t ht => ⟨ht.1, ht.2.trans hx.2⟩) (hb n)
  rw [hi, lower_integral_exponential hn hx.1.le]
  simp only [exponentialFunction, fourier_zero]

lemma diagonal_exponential (hV : IntegralFormula) (b : HilbertBasis ℤ ℂ (Space ℂ))
    (hb : ∀ n, (b n : ℝ → ℂ) =ᵐ[intervalMeasure] exponentialFunction n)
    {n : ℤ} (hn : n ≠ 0) :
    inner ℂ (b n) (VolterraValue ℂ (b n)) = (exponentialFrequency n)⁻¹ := by
  rw [volterra_exponential hV b hb hn, inner_smul_right, inner_sub_right]
  rw [b.orthonormal.inner_eq_zero hn, sub_zero,
    inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp


lemma inverse_exponentialFrequency_norm (n : ℕ) :
    ‖(exponentialFrequency ((n : ℤ) + 1))⁻¹‖ = (2 * Real.pi)⁻¹ * (1 / ((n : ℝ) + 1)) := by
  simp only [norm_inv, exponentialFrequency, norm_mul, Complex.norm_ofNat, Complex.norm_real,
    Real.norm_eq_abs, Complex.norm_I, mul_one, Complex.norm_intCast]
  push_cast
  rw [abs_of_pos Real.pi_pos, abs_of_pos (by positivity : 0 < (n : ℝ) + 1)]
  simp only [mul_inv_rev, one_div]
  ring

lemma inverse_exponentialFrequency_not_summable : ¬ Summable (fun n : ℤ => (exponentialFrequency n)⁻¹) := by
  intro hs
  have hseq := hs.norm.comp_injective (i := fun n : ℕ => (n : ℤ) + 1) (by
    intro n m h
    exact_mod_cast (add_right_cancel h))
  change Summable (fun n : ℕ => ‖(exponentialFrequency ((n : ℤ) + 1))⁻¹‖) at hseq
  simp_rw [inverse_exponentialFrequency_norm] at hseq
  have hhar : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
    have h := hseq.mul_left (2 * Real.pi)
    simpa [← mul_assoc, mul_inv_cancel₀ (show (2 : ℝ) * Real.pi ≠ 0 by positivity)] using h
  have hdiv := Real.summable_one_div_nat_add_rpow (1 : ℝ) (1 : ℝ)
  simp only [Real.rpow_one] at hdiv
  have hhar' : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1|) := by
    exact hhar.congr fun n => by rw [abs_of_pos (by positivity)]
  exact (lt_irrefl (1 : ℝ)) (hdiv.mp hhar')


lemma diagonal_exponential_not_summable (hV : IntegralFormula)
    (b : HilbertBasis ℤ ℂ (Space ℂ))
    (hb : ∀ n, (b n : ℝ → ℂ) =ᵐ[intervalMeasure] exponentialFunction n) :
    ¬ Summable (fun n => inner ℂ (b n) (VolterraValue ℂ (b n))) := by
  intro hs
  apply inverse_exponentialFrequency_not_summable
  apply hs.congr_cofinite
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with n hn
  exact diagonal_exponential hV b hb hn

lemma not_basis_independent_of_exponential (hV : IntegralFormula)
    (b : HilbertBasis ℤ ℂ (Space ℂ))
    (hb : ∀ n, (b n : ℝ → ℂ) =ᵐ[intervalMeasure] exponentialFunction n) :
    NotBasisIndependentTrace := by
  classical
  rintro ⟨τ, hτ⟩
  let e : ℕ ≃ ℤ := Equiv.intEquivNat.symm
  let bn : HilbertBasis ℕ ℂ (Space ℂ) := HilbertBasis.mk
    (b.orthonormal.comp e e.injective) (by
      rw [e.surjective.range_comp b]
      exact b.dense_span.ge)
  have hbn : ∀ n, bn n = b (e n) := fun n => congrFun (HilbertBasis.coe_mk _ _) n
  have hs := hτ bn
  simp only [hbn] at hs
  have hsb : HasSum (fun n => inner ℂ (b n) (VolterraValue ℂ (b n))) τ :=
    (e.hasSum_iff).mp hs
  exact diagonal_exponential_not_summable hV b hb hsb.summable

theorem notBasisIndependentTrace_of_integralFormula (hV : Spec.IntegralFormula) :
    Spec.NotBasisIndependentTrace :=
  not_basis_independent_of_exponential hV exponentialBasis exponentialBasis_ae

/-- The non-summable complex Fourier diagonal rules out trace class directly. -/
theorem complex_notTraceClass_of_integralFormula (hV : Spec.IntegralFormula) :
    ¬ ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (VolterraValue ℂ) := by
  intro hT
  exact diagonal_exponential_not_summable hV exponentialBasis exponentialBasis_ae
    ((ExpandedFA.TraceIdeals.TraceClassDefinitions.diagonal_trace
      ℂ (Space ℂ) (VolterraValue ℂ) hT ℤ exponentialBasis).2.summable)

/-- A complex orthonormal-basis diagonal need not even be summable. -/
theorem notBasisIndependentTrace : Spec.NotBasisIndependentTrace :=
  notBasisIndependentTrace_of_integralFormula integral_formula

/-- The Fourier diagonal also gives a direct complex trace-class obstruction. -/
theorem complex_notTraceClass :
    ¬ TraceIdeals.TraceClassDefinitions.Spec.IsTraceClassValue (volterra ℂ) :=
  complex_notTraceClass_of_integralFormula integral_formula


def gramPrimitive {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (x : ℝ) : 𝕜 :=
  ∫ t in x..(1 : ℝ), intervalPrimitive f t

lemma gramPrimitive_deriv {𝕜 : Type} [RCLike 𝕜] {f : ℝ → 𝕜}
    (hf : IntegrableOn f (Ioo 0 1)) (x : ℝ) :
    HasDerivAt (gramPrimitive f) (-intervalPrimitive f x) x := by
  have hF := intervalPrimitive_continuous hf
  exact intervalIntegral.integral_hasDerivAt_left (hF.intervalIntegrable x 1)
    hF.stronglyMeasurable.stronglyMeasurableAtFilter hF.continuousAt

lemma gramPrimitive_continuous {𝕜 : Type} [RCLike 𝕜] {f : ℝ → 𝕜}
    (hf : IntegrableOn f (Ioo 0 1)) : Continuous (gramPrimitive f) :=
  continuous_iff_continuousAt.mpr fun x => (gramPrimitive_deriv hf x).continuousAt

lemma gramPrimitive_eq_integral {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    gramPrimitive f x = ∫ t in Ioo x 1, intervalPrimitive f t := by
  rw [gramPrimitive, intervalIntegral.integral_of_le hx.2, integral_Ioc_eq_integral_Ioo]

lemma gram_formula (𝕜 : Type) [RCLike 𝕜] (f : Space 𝕜) :
    (ContinuousLinearMap.adjoint (volterra 𝕜) (volterra 𝕜 f) : ℝ → 𝕜) =ᵐ[intervalMeasure]
      gramPrimitive (f : ℝ → 𝕜) := by
  have hFrep : (volterra 𝕜 f : ℝ → 𝕜) =ᵐ[intervalMeasure] intervalPrimitive (f : ℝ → 𝕜) := by
    filter_upwards [integral_formula 𝕜 f, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    rw [hx, intervalPrimitive_eq_integral f (Ioo_subset_Icc_self hxm)]
  filter_upwards [adjoint_formula 𝕜 (volterra 𝕜 f), ae_restrict_mem measurableSet_Ioo] with x hx hxm
  rw [hx, gramPrimitive_eq_integral f (Ioo_subset_Icc_self hxm)]
  apply integral_congr_ae
  exact ae_restrict_of_ae_restrict_of_subset
    (show Ioo x (1 : ℝ) ⊆ Ioo 0 1 from fun t ht => ⟨hxm.1.trans ht.1, ht.2⟩) hFrep

/-- A nonzero Gram eigen-equation has a C¹ representative with the actual
endpoint conditions; its second derivative satisfies the scalar ODE inside. -/
lemma gram_eigenfunction_regular {𝕜 : Type} [RCLike 𝕜] (f : Space 𝕜)
    {z : 𝕜} (hz : z ≠ 0)
    (he : ContinuousLinearMap.adjoint (volterra 𝕜) (volterra 𝕜 f) = z • f) :
    ∃ g g' : ℝ → 𝕜, Continuous g ∧ Continuous g' ∧
      (f : ℝ → 𝕜) =ᵐ[intervalMeasure] g ∧
      (∀ x, HasDerivAt g (g' x) x) ∧
      (∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt g' (-z⁻¹ * g x) x) ∧
      g' 0 = 0 ∧ g 1 = 0 := by
  have hf : IntegrableOn (f : ℝ → 𝕜) (Ioo 0 1) :=
    (Lp.memLp f).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  let F := intervalPrimitive (f : ℝ → 𝕜)
  let G := gramPrimitive (f : ℝ → 𝕜)
  let g : ℝ → 𝕜 := fun x => z⁻¹ * G x
  let g' : ℝ → 𝕜 := fun x => -z⁻¹ * F x
  have hF : Continuous F := intervalPrimitive_continuous hf
  have hG : Continuous G := gramPrimitive_continuous hf
  have hg : Continuous g := continuous_const.mul hG
  have hg' : Continuous g' := continuous_const.mul hF
  have hrep : G =ᵐ[intervalMeasure] fun x => z * f x := by
    have h := gram_formula 𝕜 f
    rw [he] at h
    exact h.symm.trans (Lp.coeFn_smul z f)
  have hfg : (f : ℝ → 𝕜) =ᵐ[intervalMeasure] g := by
    filter_upwards [hrep] with x hx
    dsimp [g]
    rw [hx, inv_mul_cancel_left₀ hz]
  have hd (x : ℝ) : HasDerivAt g (g' x) x := by
    exact (gramPrimitive_deriv hf x).const_mul z⁻¹ |>.congr_deriv (by dsimp [g']; ring)
  have hFd (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) : HasDerivAt F (g x) x := by
    let H : ℝ → 𝕜 := fun y => ∫ t in (0 : ℝ)..y, g t
    have hH : HasDerivAt H (g x) x :=
      intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 x)
        hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
    apply hH.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    rw [show F y = ∫ t in Ioo 0 y, f t from intervalPrimitive_eq_integral f (Ioo_subset_Icc_self hy)]
    dsimp [H]
    rw [intervalIntegral.integral_of_le hy.1.le, integral_Ioc_eq_integral_Ioo]
    exact integral_congr_ae (ae_restrict_of_ae_restrict_of_subset
      (show Ioo (0 : ℝ) y ⊆ Ioo 0 1 from fun t ht => ⟨ht.1, ht.2.trans hy.2⟩) hfg)
  refine ⟨g, g', hg, hg', hfg, hd, ?_, ?_, ?_⟩
  · intro x hx
    exact (hFd x hx).const_mul (-z⁻¹)
  · simp [g', F, intervalPrimitive_zero]
  · simp [g, G, gramPrimitive]


set_option maxHeartbeats 1000000 in
lemma singularValue_square_hasSum : HasSum (fun n => singularValue n ^ 2) (1 / 2 : ℝ) := by
  have hz := hasSum_zeta_two
  have he : HasSum (fun n : ℕ => (1 : ℝ) / ((2 * n : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 24) := by
    convert hz.mul_left (1 / 4) using 1
    · funext n
      push_cast
      simp only [mul_pow, div_eq_mul_inv, mul_inv_rev ]
      ring
    · ring
  have ho : Summable (fun n : ℕ => (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ^ 2) :=
    hz.summable.comp_injective (i := fun n : ℕ => 2 * n + 1) (by intro m n h; dsimp at h; omega)
  have hOdd : HasSum (fun n : ℕ => (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 8) := by
    have htotal := (he.even_add_odd (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) ho.hasSum).unique hz
    convert ho.hasSum using 1
    linarith
  convert hOdd.mul_left (4 / Real.pi ^ 2) using 1
  · funext n
    unfold singularValue
    push_cast
    field_simp
    ring
  · field_simp
    ring


def trigPairVector : Option (Bool × ℕ) → Space ℂ
  | none => exponentialVector 0
  | some (false,n) => ((Real.sqrt 2 : ℂ) / 2) •
      (exponentialVector (n+1) + exponentialVector (-(n+1 : ℤ)))
  | some (true,n) => ((Real.sqrt 2 : ℂ) / 2 * (-Complex.I)) •
      (exponentialVector (n+1) - exponentialVector (-(n+1 : ℤ)))

lemma trigPairVector_orthonormal : Orthonormal ℂ trigPairVector := by
  rw [orthonormal_iff_ite]
  rintro (_ | ⟨a,n⟩) (_ | ⟨b,m⟩)
  · simpa only [trigPairVector] using orthonormal_iff_ite.mp orthonormal_exponentialVector 0 0
  · cases b <;>
      simp [trigPairVector, inner_smul_right, inner_add_right, inner_sub_right,
        orthonormal_iff_ite.mp orthonormal_exponentialVector,
        show (0 : ℤ) ≠ ↑m + 1 by omega,
        show (0 : ℤ) ≠ -(↑m + 1) by omega] <;> omega
  · cases a <;>
      simp [trigPairVector, inner_smul_left, inner_add_left, inner_sub_left,
        orthonormal_iff_ite.mp orthonormal_exponentialVector,
        show (↑n + 1 : ℤ) ≠ 0 by omega,
        show (-(↑n + 1) : ℤ) ≠ 0 by omega] <;> omega
  · have hnm : ((n : ℤ) + 1 = (m : ℤ) + 1) ↔ n = m := by omega
    have hnmn : ((n : ℤ) + 1 = -((m : ℤ) + 1)) ↔ False := iff_false_intro (by omega)
    have hnnm : (-((n : ℤ) + 1) = ((m : ℤ) + 1)) ↔ False := iff_false_intro (by omega)
    have hnnmn : (-((n : ℤ) + 1) = -((m : ℤ) + 1)) ↔ n = m := by omega
    have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      norm_cast
      exact Real.sq_sqrt (by norm_num)
    cases a <;> cases b <;>
      simp only [trigPairVector, inner_smul_left, inner_smul_right, inner_add_left,
        inner_add_right, inner_sub_left, inner_sub_right,
        orthonormal_iff_ite.mp orthonormal_exponentialVector,
        hnm, hnmn, hnnm, hnnmn]
    all_goals by_cases h : n = m <;>
      simp [h, map_mul, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_I] <;>
      ring_nf <;> simp [hs, Complex.I_sq, map_ofNat] <;> norm_num

lemma trigPairVector_dense_span :
    (Submodule.span ℂ (range trigPairVector)).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  have hi (i : Option (Bool × ℕ)) : inner ℂ (trigPairVector i) f = 0 :=
    (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.subset_span (mem_range_self i))
  have hc0 : (Real.sqrt 2 : ℂ) / 2 ≠ 0 := by
    exact div_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne')
      (by norm_num)
  have hp (n : ℕ) : inner ℂ (exponentialVector (n+1)) f = 0 ∧
      inner ℂ (exponentialVector (-(n+1 : ℤ))) f = 0 := by
    have hc := hi (some (false,n))
    have hs := hi (some (true,n))
    simp only [trigPairVector, inner_smul_left, inner_add_left] at hc
    simp only [trigPairVector, inner_smul_left, inner_sub_left] at hs
    have hc' := (mul_eq_zero.mp hc).resolve_left ((map_ne_zero (starRingEnd ℂ)).mpr hc0)
    have hs' := (mul_eq_zero.mp hs).resolve_left
      ((map_ne_zero (starRingEnd ℂ)).mpr (mul_ne_zero hc0 (neg_ne_zero.mpr Complex.I_ne_zero)))
    constructor
    · linear_combination (hc' + hs') / 2
    · linear_combination (hc' - hs') / 2
  have he (k : ℤ) : inner ℂ (exponentialVector k) f = 0 := by
    by_cases hk : k = 0
    · simpa [hk, trigPairVector] using hi none
    · rcases lt_or_gt_of_ne hk with hk | hk
      · let n := (-k-1).toNat
        have hn : (-(n+1 : ℤ)) = k := by dsimp [n]; omega
        simpa only [hn] using (hp n).2
      · let n := (k-1).toNat
        have hn : (n+1 : ℤ) = k := by dsimp [n]; omega
        simpa only [hn] using (hp n).1
  have h := exponential_parseval f
  simp only [he, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  have hn : ‖f‖ ^ 2 = 0 := h.unique hasSum_zero
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg f])


def trigPairFunction : Option (Bool × ℕ) → ℝ → ℝ
  | none, _ => 1
  | some (false,n), t => Real.sqrt 2 * Real.cos (2 * Real.pi * (n+1) * t)
  | some (true,n), t => Real.sqrt 2 * Real.sin (2 * Real.pi * (n+1) * t)

lemma exponentialFunction_eq_trig (n : ℤ) (x : ℝ) :
    exponentialFunction n x = (Real.cos (2 * Real.pi * n * x) : ℂ) +
      Real.sin (2 * Real.pi * n * x) * Complex.I := by
  rw [exponentialFunction, fourier_coe_apply]
  convert Complex.exp_ofReal_mul_I (2 * Real.pi * n * x) using 1
  congr 1
  push_cast
  ring

lemma exponentialFunction_add_neg (n : ℤ) (x : ℝ) :
    exponentialFunction n x + exponentialFunction (-n) x =
      2 * (Real.cos (2 * Real.pi * n * x) : ℂ) := by
  simp only [exponentialFunction_eq_trig, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg,
    Real.sin_neg, Complex.ofReal_neg]
  ring

lemma exponentialFunction_sub_neg (n : ℤ) (x : ℝ) :
    exponentialFunction n x - exponentialFunction (-n) x =
      2 * (Real.sin (2 * Real.pi * n * x) : ℂ) * Complex.I := by
  simp only [exponentialFunction_eq_trig, Int.cast_neg, mul_neg, neg_mul, Real.cos_neg,
    Real.sin_neg, Complex.ofReal_neg]
  ring

lemma trigPairVector_ae (i : Option (Bool × ℕ)) :
    (trigPairVector i : ℝ → ℂ) =ᵐ[intervalMeasure] fun t => (trigPairFunction i t : ℂ) := by
  rcases i with _ | ⟨b,n⟩
  · filter_upwards [exponentialVector_ae 0] with t ht
    simpa [trigPairVector, trigPairFunction, exponentialFunction, fourier_zero] using ht
  · cases b
    · filter_upwards [Lp.coeFn_smul ((Real.sqrt 2 : ℂ) / 2)
        (exponentialVector (n+1) + exponentialVector (-(n+1 : ℤ))),
        Lp.coeFn_add (exponentialVector (n+1)) (exponentialVector (-(n+1 : ℤ))),
        exponentialVector_ae (n+1), exponentialVector_ae (-(n+1 : ℤ))] with t ht ha hp hn
      dsimp only [trigPairVector]
      rw [ht, Pi.smul_apply, ha, Pi.add_apply, hp, hn, smul_eq_mul, exponentialFunction_add_neg]
      simp only [trigPairFunction, Int.cast_add, Int.cast_natCast, Int.cast_one, Complex.ofReal_mul]
      ring
    · filter_upwards [Lp.coeFn_smul ((Real.sqrt 2 : ℂ) / 2 * (-Complex.I))
        (exponentialVector (n+1) - exponentialVector (-(n+1 : ℤ))),
        Lp.coeFn_sub (exponentialVector (n+1)) (exponentialVector (-(n+1 : ℤ))),
        exponentialVector_ae (n+1), exponentialVector_ae (-(n+1 : ℤ))] with t ht ha hp hn
      dsimp only [trigPairVector]
      rw [ht, Pi.smul_apply, ha, Pi.sub_apply, hp, hn, smul_eq_mul, exponentialFunction_sub_neg]
      simp only [trigPairFunction, Int.cast_add, Int.cast_natCast, Int.cast_one, Complex.ofReal_mul]
      ring_nf
      rw [Complex.I_sq]
      ring

lemma trigPairFunction_continuous (i : Option (Bool × ℕ)) : Continuous (trigPairFunction i) := by
  rcases i with _ | ⟨b,n⟩
  · exact continuous_const
  · cases b <;> fun_prop [trigPairFunction]

lemma trigPairFunction_memLp (i : Option (Bool × ℕ)) :
    MemLp (trigPairFunction i) 2 intervalMeasure := by
  apply MemLp.of_bound (C := Real.sqrt 2 + 1) (trigPairFunction_continuous i).aestronglyMeasurable
  refine Filter.Eventually.of_forall fun t => ?_
  rcases i with _ | ⟨b,n⟩
  · simp only [trigPairFunction, norm_one]
    linarith [Real.sqrt_nonneg 2]
  · cases b <;> simp only [trigPairFunction, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
    · nlinarith [Real.abs_cos_le_one (2 * Real.pi * (n+1) * t), Real.sqrt_nonneg 2]
    · nlinarith [Real.abs_sin_le_one (2 * Real.pi * (n+1) * t), Real.sqrt_nonneg 2]

def ordinaryTrigPairVector (𝕜 : Type) [RCLike 𝕜] (i : Option (Bool × ℕ)) : Space 𝕜 :=
  ((trigPairFunction_memLp i).ofReal (K := 𝕜)).toLp (fun t => (trigPairFunction i t : 𝕜))

lemma ordinaryTrigPairVector_ae (𝕜 : Type) [RCLike 𝕜] (i : Option (Bool × ℕ)) :
    (ordinaryTrigPairVector 𝕜 i : ℝ → 𝕜) =ᵐ[intervalMeasure]
      fun t => (trigPairFunction i t : 𝕜) :=
  ((trigPairFunction_memLp i).ofReal (K := 𝕜)).coeFn_toLp

lemma ordinaryTrigPairVector_complex (i : Option (Bool × ℕ)) :
    ordinaryTrigPairVector ℂ i = trigPairVector i := by
  apply Lp.ext
  exact (ordinaryTrigPairVector_ae ℂ i).trans (trigPairVector_ae i).symm

lemma ordinaryTrigPairVector_inner (𝕜 : Type) [RCLike 𝕜] (i j : Option (Bool × ℕ)) :
    inner 𝕜 (ordinaryTrigPairVector 𝕜 i) (ordinaryTrigPairVector 𝕜 j) =
      RCLike.ofReal (K := 𝕜) (∫ t, trigPairFunction i t * trigPairFunction j t ∂intervalMeasure) := by
  rw [L2.inner_def, ← integral_ofReal]
  apply integral_congr_ae
  filter_upwards [ordinaryTrigPairVector_ae 𝕜 i, ordinaryTrigPairVector_ae 𝕜 j] with t hi hj
  rw [hi, hj]
  simp only [RCLike.inner_apply', RCLike.conj_ofReal, RCLike.ofReal_mul]

lemma ordinaryTrigPairVector_orthonormal (𝕜 : Type) [RCLike 𝕜] :
    Orthonormal 𝕜 (ordinaryTrigPairVector 𝕜) := by
  rw [orthonormal_iff_ite]
  intro i j
  have hc := orthonormal_iff_ite.mp trigPairVector_orthonormal i j
  rw [← ordinaryTrigPairVector_complex i, ← ordinaryTrigPairVector_complex j,
    ordinaryTrigPairVector_inner] at hc
  rw [ordinaryTrigPairVector_inner]
  by_cases h : i = j
  · simp only [h, ↓reduceIte] at hc ⊢
    have hr : (∫ t, trigPairFunction j t * trigPairFunction j t ∂intervalMeasure) = 1 := by
      simpa only [RCLike.ofReal_re, RCLike.one_re, RCLike.zero_re] using congrArg RCLike.re hc
    rw [hr, RCLike.ofReal_one]
  · simp only [h, ↓reduceIte] at hc ⊢
    have hr : (∫ t, trigPairFunction i t * trigPairFunction j t ∂intervalMeasure) = 0 := by
      simpa only [RCLike.ofReal_re, RCLike.one_re, RCLike.zero_re] using congrArg RCLike.re hc
    rw [hr, RCLike.ofReal_zero]



lemma complexify_trig_inner (𝕜 : Type) [RCLike 𝕜] (f : Space 𝕜) (i : Option (Bool × ℕ)) :
    inner ℂ (trigPairVector i) ((RCLike.map 𝕜 ℂ).compLp f) =
      RCLike.map 𝕜 ℂ (inner 𝕜 (ordinaryTrigPairVector 𝕜 i) f) := by
  rw [L2.inner_def, L2.inner_def,
    ← (RCLike.map 𝕜 ℂ).integral_comp_comm (L2.integrable_inner (ordinaryTrigPairVector 𝕜 i) f)]
  apply integral_congr_ae
  filter_upwards [trigPairVector_ae i, ordinaryTrigPairVector_ae 𝕜 i,
    (RCLike.map 𝕜 ℂ).coeFn_compLp f] with x ht ho hf
  rw [ht, ho, hf]
  simp only [RCLike.inner_apply', RCLike.conj_ofReal, Complex.conj_ofReal]
  simp only [RCLike.map_apply, RCLike.mul_re, RCLike.mul_im, RCLike.ofReal_re,
    RCLike.ofReal_im, zero_mul, zero_add, mul_zero, sub_zero, RCLike.ofReal_mul]
  simp only [RCLike.ofReal_eq_complex_ofReal, RCLike.I_to_complex]
  push_cast
  simp only [add_zero, zero_add]
  ring


lemma ordinaryTrigPairVector_dense_span (𝕜 : Type) [RCLike 𝕜] :
    (Submodule.span 𝕜 (range (ordinaryTrigPairVector 𝕜))).topologicalClosure = ⊤ := by
  rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro f hf
  let g : Space ℂ := (RCLike.map 𝕜 ℂ).compLp f
  have htest (i : Option (Bool × ℕ)) : inner ℂ (trigPairVector i) g = 0 := by
    rw [complexify_trig_inner]
    have hi := (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.subset_span (mem_range_self i))
    rw [hi, map_zero]
  have hg : g = 0 := by
    let hb : HilbertBasis (Option (Bool × ℕ)) ℂ (Space ℂ) :=
      HilbertBasis.mk trigPairVector_orthonormal trigPairVector_dense_span.ge
    have hbv (i) : hb i = trigPairVector i := congrFun (HilbertBasis.coe_mk trigPairVector_orthonormal trigPairVector_dense_span.ge) i
    have h := hb.hasSum_repr g
    simp only [HilbertBasis.repr_apply_apply, hbv, htest, zero_smul] at h
    exact h.unique hasSum_zero
  apply Lp.ext
  filter_upwards [(RCLike.map 𝕜 ℂ).coeFn_compLp f, Lp.coeFn_zero (E := ℂ) 2 intervalMeasure,
    Lp.coeFn_zero (E := 𝕜) 2 intervalMeasure] with x hgf hzc hzk
  change g x = (RCLike.map 𝕜 ℂ) (f x) at hgf
  simp only [Pi.zero_apply] at hzc hzk
  rw [hg, hzc] at hgf
  rw [hzk]
  apply norm_eq_zero.mp
  rw [← RCLike.norm_to_complex]
  change ‖RCLike.map 𝕜 ℂ (f x)‖ = 0
  rw [← hgf, norm_zero]


def trigIndexEquiv : Option (Bool × ℕ) ≃ ℕ where
  toFun
    | none => 0
    | some p => Equiv.boolProdNatEquivNat p + 1
  invFun
    | 0 => none
    | n+1 => some (Equiv.boolProdNatEquivNat.symm n)
  left_inv := by
    rintro (_ | p)
    · rfl
    · change some (Equiv.boolProdNatEquivNat.symm (Equiv.boolProdNatEquivNat p)) = some p
      rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro (_ | n)
    · rfl
    · change Equiv.boolProdNatEquivNat (Equiv.boolProdNatEquivNat.symm n) + 1 = n+1
      rw [Equiv.apply_symm_apply]

lemma trigIndexEquiv_none : trigIndexEquiv none = 0 := rfl
lemma trigIndexEquiv_cos (n : ℕ) : trigIndexEquiv (some (false,n)) = 2*n+1 := by
  simp [trigIndexEquiv, Equiv.boolProdNatEquivNat, Nat.bit_false, two_mul]
lemma trigIndexEquiv_sin (n : ℕ) : trigIndexEquiv (some (true,n)) = 2*n+2 := by
  simp [trigIndexEquiv, Equiv.boolProdNatEquivNat, Nat.bit_true, two_mul]

lemma trigFunction_index (i : Option (Bool × ℕ)) (t : ℝ) :
    trigFunction (trigIndexEquiv i) t = trigPairFunction i t := by
  rcases i with _ | ⟨b,n⟩
  · simp [trigIndexEquiv_none, trigFunction, trigPairFunction]
  · cases b
    · rw [trigIndexEquiv_cos]
      have hz : 2*n+1 ≠ 0 := by omega
      have hp : (2*n+1)%2 = 1 := by omega
      have hd : (2*n+1+1)/2 = n+1 := by omega
      simp only [trigFunction, hz, ↓reduceIte, hp, hd, trigPairFunction, Nat.cast_add, Nat.cast_one]
    · rw [trigIndexEquiv_sin]
      have hz : 2*n+2 ≠ 0 := by omega
      have hp : ¬ (2*n+2)%2 = 1 := by omega
      have hd : (2*n+2)/2 = n+1 := by omega
      simp only [trigFunction, hz, ↓reduceIte, hp, hd, trigPairFunction, Nat.cast_add, Nat.cast_one]

def ordinaryTrigVector (𝕜 : Type) [RCLike 𝕜] (n : ℕ) : Space 𝕜 :=
  ordinaryTrigPairVector 𝕜 (trigIndexEquiv.symm n)

lemma ordinaryTrigVector_ae (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    (ordinaryTrigVector 𝕜 n : ℝ → 𝕜) =ᵐ[intervalMeasure] fun t => (trigFunction n t : 𝕜) := by
  filter_upwards [ordinaryTrigPairVector_ae 𝕜 (trigIndexEquiv.symm n)] with t ht
  change (ordinaryTrigPairVector 𝕜 (trigIndexEquiv.symm n) : ℝ → 𝕜) t = _
  rw [ht, ← trigFunction_index, Equiv.apply_symm_apply]

lemma ordinaryTrigVector_orthonormal (𝕜 : Type) [RCLike 𝕜] :
    Orthonormal 𝕜 (ordinaryTrigVector 𝕜) :=
  (ordinaryTrigPairVector_orthonormal 𝕜).comp trigIndexEquiv.symm trigIndexEquiv.symm.injective

lemma trigPairFunction_mean (i : Option (Bool × ℕ)) :
    (∫ t, trigPairFunction i t ∂intervalMeasure) = if i = none then 1 else 0 := by
  have h := orthonormal_iff_ite.mp (ordinaryTrigPairVector_orthonormal ℝ) none i
  rw [ordinaryTrigPairVector_inner] at h
  simpa [trigPairFunction, RCLike.ofReal_real_eq_id, eq_comm] using h

lemma trigFunction_mean (n : ℕ) :
    (∫ t, trigFunction n t ∂intervalMeasure) = if n = 0 then 1 else 0 := by
  have hi : (trigIndexEquiv.symm n = none) ↔ n = 0 := by
    constructor
    · intro h
      simpa only [Equiv.apply_symm_apply, trigIndexEquiv_none] using congrArg trigIndexEquiv h
    · rintro rfl
      exact trigIndexEquiv.symm_apply_eq.mpr trigIndexEquiv_none
  have heq : trigFunction n = trigPairFunction (trigIndexEquiv.symm n) := by
    funext t
    rw [← trigFunction_index, Equiv.apply_symm_apply]
  simp only [heq, trigPairFunction_mean, hi]

lemma trigFunction_continuous (n : ℕ) : Continuous (trigFunction n) := by
  have heq : trigFunction n = trigPairFunction (trigIndexEquiv.symm n) := by
    funext t
    rw [← trigFunction_index, Equiv.apply_symm_apply]
  rw [heq]
  exact trigPairFunction_continuous _

lemma ordinaryTrigVector_mean (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    (∫ t, (ordinaryTrigVector 𝕜 n : ℝ → 𝕜) t ∂intervalMeasure) =
      if n = 0 then 1 else 0 := by
  rw [integral_congr_ae (ordinaryTrigVector_ae 𝕜 n), integral_ofReal, trigFunction_mean]
  split_ifs <;> simp only [RCLike.ofReal_one, RCLike.ofReal_zero]


lemma real_primitive_quadratic (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x, g x * (∫ t in (0 : ℝ)..x, g t) ∂intervalMeasure) =
      (∫ x, g x ∂intervalMeasure) ^ 2 / 2 := by
  let F : ℝ → ℝ := fun x => ∫ t in (0 : ℝ)..x, g t
  have hd (x : ℝ) : HasDerivAt F (g x) x :=
    intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable 0 x)
      hg.stronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := 1) (fun x _ => hd x) (fun x _ => hd x)
    (hg.intervalIntegrable 0 1) (hg.intervalIntegrable 0 1)
  have hc : (fun x => F x * g x) = (fun x => g x * F x) := funext fun _ => mul_comm _ _
  rw [hc] at h
  have h0 : F 0 = 0 := by simp [F]
  rw [h0, zero_mul, sub_zero, intervalIntegral_unit_eq] at h
  change (∫ x, g x * F x ∂intervalMeasure) = _
  have h1 : F 1 = ∫ x, g x ∂intervalMeasure := intervalIntegral_unit_eq g
  rw [h1] at h
  nlinarith

lemma volterra_real_diagonal (hV : Spec.IntegralFormula) (𝕜 : Type) [RCLike 𝕜]
    (f : Space 𝕜) (g : ℝ → ℝ) (hg : Continuous g)
    (hf : (f : ℝ → 𝕜) =ᵐ[intervalMeasure] fun t => (g t : 𝕜)) :
    inner 𝕜 f (VolterraValue 𝕜 f) =
      RCLike.ofReal (K := 𝕜) ((∫ t, g t ∂intervalMeasure)^2 / 2) := by
  rw [L2.inner_def, ← real_primitive_quadratic g hg, ← integral_ofReal]
  apply integral_congr_ae
  filter_upwards [hf, hV 𝕜 f, ae_restrict_mem measurableSet_Ioo] with x hx hv hxm
  have hsub : Ioo (0 : ℝ) x ⊆ Ioo 0 1 := fun t ht => ⟨ht.1, ht.2.trans hxm.2⟩
  have hi : (∫ t in Ioo (0 : ℝ) x, f t) = ∫ t in Ioo (0 : ℝ) x, (g t : 𝕜) :=
    integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub hf)
  rw [hx, hv, hi, integral_ofReal]
  rw [intervalIntegral.integral_of_le hxm.1.le, integral_Ioc_eq_integral_Ioo]
  simp only [RCLike.inner_apply', RCLike.conj_ofReal, RCLike.ofReal_mul]

lemma diagonal_ordinaryTrigVector (hV : Spec.IntegralFormula) (𝕜 : Type) [RCLike 𝕜]
    (n : ℕ) : inner 𝕜 (ordinaryTrigVector 𝕜 n) (VolterraValue 𝕜 (ordinaryTrigVector 𝕜 n)) =
      if n = 0 then 1 / 2 else 0 := by
  rw [volterra_real_diagonal hV 𝕜 _ _ (trigFunction_continuous n) (ordinaryTrigVector_ae 𝕜 n),
    trigFunction_mean]
  split_ifs <;> norm_num [map_ofNat, one_div]

lemma ordinaryTrigVector_dense_span (𝕜 : Type) [RCLike 𝕜] :
    (Submodule.span 𝕜 (range (ordinaryTrigVector 𝕜))).topologicalClosure = ⊤ := by
  change (Submodule.span 𝕜 (range (ordinaryTrigPairVector 𝕜 ∘ trigIndexEquiv.symm))).topologicalClosure = ⊤
  rw [trigIndexEquiv.symm.surjective.range_comp]
  exact ordinaryTrigPairVector_dense_span 𝕜

def ordinaryTrigBasis (𝕜 : Type) [RCLike 𝕜] : HilbertBasis ℕ 𝕜 (Space 𝕜) :=
  HilbertBasis.mk (ordinaryTrigVector_orthonormal 𝕜) (ordinaryTrigVector_dense_span 𝕜).ge

lemma ordinaryTrigBasis_apply (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    ordinaryTrigBasis 𝕜 n = ordinaryTrigVector 𝕜 n :=
  congrFun (HilbertBasis.coe_mk _ _) n

lemma ordinaryTrigBasis_ae (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    (ordinaryTrigBasis 𝕜 n : ℝ → 𝕜) =ᵐ[intervalMeasure] fun t => (trigFunction n t : 𝕜) := by
  rw [ordinaryTrigBasis_apply]
  exact ordinaryTrigVector_ae 𝕜 n

theorem trigonometricDiagonal_of_integralFormula (hV : Spec.IntegralFormula) :
    Spec.TrigonometricDiagonal := by
  intro 𝕜 _
  refine ⟨ordinaryTrigBasis 𝕜, ordinaryTrigBasis_ae 𝕜, ?_, ?_⟩
  · intro n
    rw [ordinaryTrigBasis_apply]
    exact diagonal_ordinaryTrigVector hV 𝕜 n
  · have heq : (fun n => inner 𝕜 (ordinaryTrigBasis 𝕜 n)
        (VolterraValue 𝕜 (ordinaryTrigBasis 𝕜 n))) =
        (fun n : ℕ => if n = 0 then (1 / 2 : 𝕜) else 0) := by
      funext n
      rw [ordinaryTrigBasis_apply]
      exact diagonal_ordinaryTrigVector hV 𝕜 n
    rw [heq]
    exact hasSum_ite_eq 0 (1 / 2 : 𝕜)


theorem trigonometricDiagonal : Spec.TrigonometricDiagonal :=
  trigonometricDiagonal_of_integralFormula integral_formula

end ExpandedFA.IntegralOperators.VolterraTraceCounterexample

namespace VolterraSingular

def frequency (n : ℕ) : ℝ := ((n : ℝ) + 1 / 2) * Real.pi
lemma frequency_pos (n : ℕ) : 0 < frequency n := by unfold frequency; positivity
lemma frequency_ne (n : ℕ) : frequency n ≠ 0 := ne_of_gt (frequency_pos n)
lemma cos_frequency (n : ℕ) : Real.cos (frequency n) = 0 := by
  have h : frequency n = (n : ℝ) * Real.pi + Real.pi / 2 := by unfold frequency; ring
  rw [h, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]

lemma integral_cos_mul (a b c : ℝ) (hc : c ≠ 0) :
    (∫ t in a..b, Real.cos (c * t)) = c⁻¹ * (Real.sin (c * b) - Real.sin (c * a)) := by
  rw [intervalIntegral.integral_comp_mul_left _ hc, integral_cos, smul_eq_mul]

lemma integral_sin_mul (a b c : ℝ) (hc : c ≠ 0) :
    (∫ t in a..b, Real.sin (c * t)) = c⁻¹ * (Real.cos (c * a) - Real.cos (c * b)) := by
  rw [intervalIntegral.integral_comp_mul_left _ hc, integral_sin, smul_eq_mul]

lemma lower_integral_cos_frequency (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (∫ t in Ioo 0 x, Real.cos (frequency n * t)) =
      (frequency n)⁻¹ * Real.sin (frequency n * x) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx,
    integral_cos_mul 0 x _ (frequency_ne n)]
  simp

lemma upper_integral_sin_frequency (n : ℕ) {x : ℝ} (hx : x ≤ 1) :
    (∫ t in Ioo x 1, Real.sin (frequency n * t)) =
      (frequency n)⁻¹ * Real.cos (frequency n * x) := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hx,
    integral_sin_mul x 1 _ (frequency_ne n)]
  simp [cos_frequency]

lemma frequency_add (m n : ℕ) :
    frequency m + frequency n = ((m + n + 1 : ℕ) : ℝ) * Real.pi := by
  simp only [frequency, Nat.cast_add, Nat.cast_one]
  ring

lemma frequency_sub (m n : ℕ) :
    frequency m - frequency n = ((m : ℝ) - n) * Real.pi := by
  unfold frequency; ring

lemma sin_frequency_add (m n : ℕ) :
    Real.sin (frequency m + frequency n) = 0 := by
  rw [frequency_add, Real.sin_nat_mul_pi]

lemma sin_frequency_sub (m n : ℕ) :
    Real.sin (frequency m - frequency n) = 0 := by
  rw [frequency_sub]
  exact_mod_cast Real.sin_int_mul_pi ((m : ℤ) - n)

lemma frequency_strictMono : StrictMono frequency := by
  intro m n hmn
  dsimp [frequency]
  apply mul_lt_mul_of_pos_right _ Real.pi_pos
  exact add_lt_add_left (Nat.cast_lt.mpr hmn : (m : ℝ) < n) (1 / 2 : ℝ)

lemma integral_cos_frequency_add (m n : ℕ) :
    (∫ t in (0 : ℝ)..1, Real.cos ((frequency m + frequency n) * t)) = 0 := by
  rw [integral_cos_mul 0 1 _ (ne_of_gt (add_pos (frequency_pos m) (frequency_pos n)))]
  simp [sin_frequency_add]

lemma integral_cos_frequency_sub (m n : ℕ) (hmn : m ≠ n) :
    (∫ t in (0 : ℝ)..1, Real.cos ((frequency m - frequency n) * t)) = 0 := by
  rw [integral_cos_mul 0 1 _ (sub_ne_zero.mpr (frequency_strictMono.injective.ne hmn))]
  simp [sin_frequency_sub]

lemma cos_mul_cos (a b : ℝ) :
    Real.cos a * Real.cos b = (Real.cos (a - b) + Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

lemma sin_mul_sin (a b : ℝ) :
    Real.sin a * Real.sin b = (Real.cos (a - b) - Real.cos (a + b)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]
  ring

lemma integral_cos_frequency_mul_self (n : ℕ) :
    (∫ t in (0 : ℝ)..1, Real.cos (frequency n * t) * Real.cos (frequency n * t)) = 1 / 2 := by
  have heq : (fun t : ℝ => Real.cos (frequency n * t) * Real.cos (frequency n * t)) =
      fun t => (1 + Real.cos ((frequency n + frequency n) * t)) / 2 := by
    funext t
    rw [cos_mul_cos, sub_self, Real.cos_zero, ← add_mul]
  rw [heq, intervalIntegral.integral_div, intervalIntegral.integral_add]
  · simp [integral_cos_frequency_add]
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma integral_sin_frequency_mul_self (n : ℕ) :
    (∫ t in (0 : ℝ)..1, Real.sin (frequency n * t) * Real.sin (frequency n * t)) = 1 / 2 := by
  have heq : (fun t : ℝ => Real.sin (frequency n * t) * Real.sin (frequency n * t)) =
      fun t => (1 - Real.cos ((frequency n + frequency n) * t)) / 2 := by
    funext t
    rw [sin_mul_sin, sub_self, Real.cos_zero, ← add_mul]
  rw [heq, intervalIntegral.integral_div, intervalIntegral.integral_sub]
  · simp [integral_cos_frequency_add]
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma integral_cos_frequency_mul_cos_frequency (m n : ℕ) (hmn : m ≠ n) :
    (∫ t in (0 : ℝ)..1, Real.cos (frequency m * t) * Real.cos (frequency n * t)) = 0 := by
  have heq : (fun t : ℝ => Real.cos (frequency m * t) * Real.cos (frequency n * t)) =
      fun t => (Real.cos ((frequency m - frequency n) * t) + Real.cos ((frequency m + frequency n) * t)) / 2 := by
    funext t
    rw [cos_mul_cos, ← sub_mul, ← add_mul]
  rw [heq, intervalIntegral.integral_div, intervalIntegral.integral_add]
  · simp [integral_cos_frequency_add, integral_cos_frequency_sub _ _ hmn]
  all_goals apply Continuous.intervalIntegrable; fun_prop

lemma integral_sin_frequency_mul_sin_frequency (m n : ℕ) (hmn : m ≠ n) :
    (∫ t in (0 : ℝ)..1, Real.sin (frequency m * t) * Real.sin (frequency n * t)) = 0 := by
  have heq : (fun t : ℝ => Real.sin (frequency m * t) * Real.sin (frequency n * t)) =
      fun t => (Real.cos ((frequency m - frequency n) * t) - Real.cos ((frequency m + frequency n) * t)) / 2 := by
    funext t
    rw [sin_mul_sin, ← sub_mul, ← add_mul]
  rw [heq, intervalIntegral.integral_div, intervalIntegral.integral_sub]
  · simp [integral_cos_frequency_add, integral_cos_frequency_sub _ _ hmn]
  all_goals apply Continuous.intervalIntegrable; fun_prop

abbrev unitMeasure : Measure ℝ :=
  ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.intervalMeasure
abbrev Space (𝕜 : Type) [RCLike 𝕜] :=
  ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.Space 𝕜

lemma cosine_memLp (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    MemLp (fun t : ℝ => (Real.cos (frequency n * t) : 𝕜)) 2 unitMeasure := by
  apply MemLp.of_bound (C := 1)
  · exact (RCLike.continuous_ofReal.comp (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by simpa using Real.abs_cos_le_one (frequency n * t)

lemma sine_memLp (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    MemLp (fun t : ℝ => (Real.sin (frequency n * t) : 𝕜)) 2 unitMeasure := by
  apply MemLp.of_bound (C := 1)
  · exact (RCLike.continuous_ofReal.comp (Real.continuous_sin.comp (continuous_const.mul continuous_id))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by simpa using Real.abs_sin_le_one (frequency n * t)

def cosineLp (𝕜 : Type) [RCLike 𝕜] (n : ℕ) : Space 𝕜 :=
  (cosine_memLp 𝕜 n).toLp (fun t => (Real.cos (frequency n * t) : 𝕜))

def sineLp (𝕜 : Type) [RCLike 𝕜] (n : ℕ) : Space 𝕜 :=
  (sine_memLp 𝕜 n).toLp (fun t => (Real.sin (frequency n * t) : 𝕜))

lemma cosineLp_representative (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    (cosineLp 𝕜 n : ℝ → 𝕜) =ᵐ[unitMeasure] fun t => (Real.cos (frequency n * t) : 𝕜) :=
  MemLp.coeFn_toLp (cosine_memLp 𝕜 n)

lemma sineLp_representative (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    (sineLp 𝕜 n : ℝ → 𝕜) =ᵐ[unitMeasure] fun t => (Real.sin (frequency n * t) : 𝕜) :=
  MemLp.coeFn_toLp (sine_memLp 𝕜 n)

lemma cosineLp_inner (𝕜 : Type) [RCLike 𝕜] (m n : ℕ) :
    inner 𝕜 (cosineLp 𝕜 m) (cosineLp 𝕜 n) = if m = n then 1 / 2 else 0 := by
  rw [L2.inner_def]
  have heq : (fun t => inner 𝕜 (cosineLp 𝕜 m t) (cosineLp 𝕜 n t)) =ᵐ[unitMeasure]
      fun t => ((Real.cos (frequency m * t) * Real.cos (frequency n * t) : ℝ) : 𝕜) := by
    filter_upwards [cosineLp_representative 𝕜 m, cosineLp_representative 𝕜 n] with t hm hn
    rw [hm, hn, RCLike.inner_apply', RCLike.conj_ofReal, ← RCLike.ofReal_mul]
  rw [integral_congr_ae heq, integral_ofReal]
  change ((∫ t in Ioo (0 : ℝ) 1, Real.cos (frequency m * t) * Real.cos (frequency n * t) : ℝ) : 𝕜) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  split_ifs with hmn
  · subst n
    rw [integral_cos_frequency_mul_self]
    norm_num [RCLike.ofReal_div, RCLike.ofReal_ofNat]
  · rw [integral_cos_frequency_mul_cos_frequency _ _ hmn]
    simp

lemma sineLp_inner (𝕜 : Type) [RCLike 𝕜] (m n : ℕ) :
    inner 𝕜 (sineLp 𝕜 m) (sineLp 𝕜 n) = if m = n then 1 / 2 else 0 := by
  rw [L2.inner_def]
  have heq : (fun t => inner 𝕜 (sineLp 𝕜 m t) (sineLp 𝕜 n t)) =ᵐ[unitMeasure]
      fun t => ((Real.sin (frequency m * t) * Real.sin (frequency n * t) : ℝ) : 𝕜) := by
    filter_upwards [sineLp_representative 𝕜 m, sineLp_representative 𝕜 n] with t hm hn
    rw [hm, hn, RCLike.inner_apply', RCLike.conj_ofReal, ← RCLike.ofReal_mul]
  rw [integral_congr_ae heq, integral_ofReal]
  change ((∫ t in Ioo (0 : ℝ) 1, Real.sin (frequency m * t) * Real.sin (frequency n * t) : ℝ) : 𝕜) = _
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  split_ifs with hmn
  · subst n
    rw [integral_sin_frequency_mul_self]
    norm_num [RCLike.ofReal_div, RCLike.ofReal_ofNat]
  · rw [integral_sin_frequency_mul_sin_frequency _ _ hmn]
    simp

def rightVector (𝕜 : Type) [RCLike 𝕜] (n : ℕ) : Space 𝕜 :=
  (Real.sqrt 2 : 𝕜) • cosineLp 𝕜 n

def leftVector (𝕜 : Type) [RCLike 𝕜] (n : ℕ) : Space 𝕜 :=
  (Real.sqrt 2 : 𝕜) • sineLp 𝕜 n

lemma rightVector_orthonormal (𝕜 : Type) [RCLike 𝕜] : Orthonormal 𝕜 (rightVector 𝕜) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [rightVector, rightVector, inner_smul_left, inner_smul_right, RCLike.conj_ofReal, cosineLp_inner]
  split_ifs
  · have hs : (Real.sqrt 2 : 𝕜) * (Real.sqrt 2 : 𝕜) = 2 := by
      rw [← RCLike.ofReal_mul, ← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [RCLike.ofReal_div, RCLike.ofReal_ofNat]
    linear_combination hs / 2
  · simp

lemma leftVector_orthonormal (𝕜 : Type) [RCLike 𝕜] : Orthonormal 𝕜 (leftVector 𝕜) := by
  rw [orthonormal_iff_ite]
  intro m n
  rw [leftVector, leftVector, inner_smul_left, inner_smul_right, RCLike.conj_ofReal, sineLp_inner]
  split_ifs
  · have hs : (Real.sqrt 2 : 𝕜) * (Real.sqrt 2 : 𝕜) = 2 := by
      rw [← RCLike.ofReal_mul, ← sq, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num [RCLike.ofReal_div, RCLike.ofReal_ofNat]
    linear_combination hs / 2
  · simp

lemma cosineLp_lower_integral (𝕜 : Type) [RCLike 𝕜] (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∫ t in Ioo 0 x, cosineLp 𝕜 n t) =
      ((frequency n)⁻¹ : 𝕜) * (Real.sin (frequency n * x) : 𝕜) := by
  have hsub : Ioo (0 : ℝ) x ⊆ Ioo (0 : ℝ) 1 := fun t ht => ⟨ht.1, ht.2.trans hx.2⟩
  rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub (cosineLp_representative 𝕜 n)),
    integral_ofReal, lower_integral_cos_frequency n hx.1.le, RCLike.ofReal_mul, RCLike.ofReal_inv]

lemma sineLp_upper_integral (𝕜 : Type) [RCLike 𝕜] (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (∫ t in Ioo x 1, sineLp 𝕜 n t) =
      ((frequency n)⁻¹ : 𝕜) * (Real.cos (frequency n * x) : 𝕜) := by
  have hsub : Ioo x (1 : ℝ) ⊆ Ioo (0 : ℝ) 1 := fun t ht => ⟨hx.1.trans ht.1, ht.2⟩
  rw [integral_congr_ae (ae_restrict_of_ae_restrict_of_subset hsub (sineLp_representative 𝕜 n)),
    integral_ofReal, upper_integral_sin_frequency n hx.2.le, RCLike.ofReal_mul, RCLike.ofReal_inv]

lemma volterra_cosineLp (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜 (cosineLp 𝕜 n) =
      ((frequency n)⁻¹ : 𝕜) • sineLp 𝕜 n := by
  apply Lp.ext
  filter_upwards [ExpandedFA.IntegralOperators.VolterraTraceCounterexample.integral_formula 𝕜 (cosineLp 𝕜 n),
    Lp.coeFn_smul ((frequency n)⁻¹ : 𝕜) (sineLp 𝕜 n),
    sineLp_representative 𝕜 n, ae_restrict_mem measurableSet_Ioo] with x hV hs hl hx
  rw [hV, hs, Pi.smul_apply, smul_eq_mul, hl]
  exact cosineLp_lower_integral 𝕜 n hx

lemma volterra_rightVector (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜 (rightVector 𝕜 n) =
      ((frequency n)⁻¹ : 𝕜) • leftVector 𝕜 n := by
  rw [rightVector, map_smul, volterra_cosineLp, leftVector, smul_smul, smul_smul, mul_comm]

lemma adjoint_sineLp (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    ContinuousLinearMap.adjoint
      (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜) (sineLp 𝕜 n) =
      ((frequency n)⁻¹ : 𝕜) • cosineLp 𝕜 n := by
  apply Lp.ext
  filter_upwards [ExpandedFA.IntegralOperators.VolterraTraceCounterexample.adjoint_formula 𝕜 (sineLp 𝕜 n),
    Lp.coeFn_smul ((frequency n)⁻¹ : 𝕜) (cosineLp 𝕜 n),
    cosineLp_representative 𝕜 n, ae_restrict_mem measurableSet_Ioo] with x hV hs hl hx
  rw [hV, hs, Pi.smul_apply, smul_eq_mul, hl]
  exact sineLp_upper_integral 𝕜 n hx

lemma adjoint_leftVector (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    ContinuousLinearMap.adjoint
      (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜) (leftVector 𝕜 n) =
      ((frequency n)⁻¹ : 𝕜) • rightVector 𝕜 n := by
  rw [leftVector, map_smul, adjoint_sineLp, rightVector, smul_smul, smul_smul, mul_comm]

lemma gram_eigenvalue (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    Module.End.HasEigenvalue ((ContinuousLinearMap.adjoint
      (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜)).comp
      (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜)).toLinearMap
      ((((frequency n)⁻¹ : ℝ) ^ 2 : ℝ) : 𝕜) := by
  apply Module.End.hasEigenvalue_of_hasEigenvector
  apply (Module.End.hasEigenvector_iff).mpr
  refine ⟨?_, (rightVector_orthonormal 𝕜).ne_zero n⟩
  rw [Module.End.mem_eigenspace_iff]
  change ContinuousLinearMap.adjoint
    (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜)
    (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜 (rightVector 𝕜 n)) = _
  rw [volterra_rightVector, map_smul, adjoint_leftVector, smul_smul,
    RCLike.ofReal_pow, RCLike.ofReal_inv, pow_two]

lemma canonical_singular_occurrence (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    ∃ k : ℕ,
      ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.singularSequence
        (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜) k =
          (frequency n)⁻¹ := by
  have h := (ExpandedFA.CompactSpectral.SingularApproximation.singular_spectral_multiplicity
    𝕜 (Space 𝕜) (Space 𝕜)
    (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜)
    (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.compact 𝕜)
    ((frequency n)⁻¹) (inv_pos.mpr (frequency_pos n))).2.1
  obtain ⟨k, hk, hv⟩ := h.mp (gram_eigenvalue 𝕜 n)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  exact ⟨j, hv⟩

lemma inverse_frequency_strictAnti : StrictAnti (fun n => (frequency n)⁻¹) := by
  intro m n hmn
  exact inv_strictAnti₀ (frequency_pos m) (frequency_strictMono hmn)

/-- Every explicit singular value occurs in the antitone canonical list.
Its increasing occurrence index can only move a term to the right, giving
termwise domination. Equality of Hilbert--Schmidt square sums forces equality. -/
theorem exact_singularValues (𝕜 : Type) [RCLike 𝕜] (n : ℕ) :
    ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.singularSequence
      (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜) n =
        (frequency n)⁻¹ := by
  let T := ExpandedFA.IntegralOperators.VolterraTraceCounterexample.Spec.VolterraValue 𝕜
  let a := ExpandedFA.TraceIdeals.TraceClassDefinitions.Spec.singularSequence T
  have hprops := ExpandedFA.CompactSpectral.SingularApproximation.singular_sequence_properties
    𝕜 (Space 𝕜) (Space 𝕜) T
    (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.compact 𝕜)
  have hanti : Antitone a := hprops.2.1
  have hnonneg (j : ℕ) : 0 ≤ a j := hprops.1 (j + 1) (Nat.succ_pos j)
  choose k hk using canonical_singular_occurrence 𝕜
  have hk' (j : ℕ) : a (k j) = (frequency j)⁻¹ := hk j
  have hkmono : StrictMono k := by
    intro i j hij
    by_contra hkij
    have hh := hanti (Nat.le_of_not_gt hkij)
    rw [hk' i, hk' j] at hh
    exact (not_le_of_gt (inverse_frequency_strictAnti hij)) hh
  have hle (j : ℕ) : (frequency j)⁻¹ ≤ a j := by
    rw [← hk' j]
    exact hanti hkmono.le_apply
  have hsqle (j : ℕ) : ((frequency j)⁻¹) ^ 2 ≤ a j ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr (frequency_pos j).le) (hle j) 2
  have hnorm := ExpandedFA.TraceIdeals.HilbertSchmidtBasis.singular_norm_identity
    ⟨T, ExpandedFA.IntegralOperators.VolterraTraceCounterexample.hilbertSchmidt 𝕜⟩
  change (Summable fun j => a j ^ 2) ∧
    ExpandedFA.TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtNormValue
      ⟨T, ExpandedFA.IntegralOperators.VolterraTraceCounterexample.hilbertSchmidt 𝕜⟩ ^ 2 =
        ∑' j, a j ^ 2 at hnorm
  have hsum : (∑' j, a j ^ 2) = 1 / 2 := hnorm.2.symm.trans
    (ExpandedFA.IntegralOperators.VolterraTraceCounterexample.hilbertSchmidt_square_norm 𝕜 _)
  have hbasel : HasSum (fun j => ((frequency j)⁻¹) ^ 2) (1 / 2 : ℝ) :=
    ExpandedFA.IntegralOperators.VolterraTraceCounterexample.singularValue_square_hasSum
  have hsqeq : a n ^ 2 = ((frequency n)⁻¹) ^ 2 := by
    by_contra hne
    have hlt : ((frequency n)⁻¹) ^ 2 < a n ^ 2 := lt_of_le_of_ne (hsqle n) (Ne.symm hne)
    have hh := Summable.tsum_lt_tsum hsqle hlt hbasel.summable hnorm.1
    rw [hsum, hbasel.tsum_eq] at hh
    exact (lt_irrefl (1 / 2 : ℝ)) hh
  exact (sq_eq_sq₀ (hnonneg n) (inv_nonneg.mpr (frequency_pos n).le)).mp hsqeq

end VolterraSingular

namespace ExpandedFA.IntegralOperators.VolterraTraceCounterexample
open Spec

/-- The canonical ordered singular sequence is exactly the half-integer list. -/
theorem singularValues : Spec.SingularValues := by
  intro 𝕜 _ n
  exact VolterraSingular.exact_singularValues 𝕜 n

/-- Divergence of these actual singular values rules out S₁. -/
theorem notTraceClass : Spec.NotTraceClass :=
  notTraceClass_of_singularValues singularValues

/-- The complete original Volterra counterexample on ordinary L²(0,1). -/
theorem counterexample : Spec.Counterexample :=
  ⟨integral_formula, hilbertSchmidt, compact, singularValues, notTraceClass,
    zero_spectrum, quasinilpotent, no_nonzero_eigenvalue, trigonometricDiagonal,
    notBasisIndependentTrace⟩

end ExpandedFA.IntegralOperators.VolterraTraceCounterexample
