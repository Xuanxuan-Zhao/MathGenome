import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HausdorffYoung
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Interpolation.RieszThorin
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v

namespace ExpandedFA.PartIV.HausdorffYoung
open Interpolation.RieszThorinSpec

/-- The interpolation parameter for an interior exponent. -/
theorem interior_parameter (a : ExponentPair) (h₁ : a.p ≠ 1) (h₂ : a.p ≠ 2) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ Interpolates 1 2 a.p θ ∧
      Interpolates ∞ 2 a.q θ := by
  have hp0 : a.p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one a.lower)
  have hpfin : a.p ≠ ∞ := ne_top_of_le_ne_top (by norm_num) a.upper
  have hinvfin : a.p⁻¹ ≠ ∞ := by simp [hp0]
  have hlo : (2 : ℝ≥0∞)⁻¹ < a.p⁻¹ :=
    ENNReal.inv_lt_inv.mpr (lt_of_le_of_ne a.upper h₂)
  have hhi : a.p⁻¹ < 1 := ENNReal.inv_lt_one.mpr (lt_of_le_of_ne a.lower h₁.symm)
  have hxlo : (1 / 2 : ℝ) < (a.p⁻¹).toReal := by
    have := (ENNReal.toReal_lt_toReal (by norm_num) hinvfin).mpr hlo
    norm_num at this ⊢
    exact this
  have hxhi : (a.p⁻¹).toReal < 1 := by
    exact (ENNReal.toReal_lt_toReal hinvfin ENNReal.one_ne_top).mpr hhi
  let θ := 2 * (1 - (a.p⁻¹).toReal)
  have hθ₀ : 0 < θ := by dsimp [θ]; linarith
  have hθ₁ : θ < 1 := by dsimp [θ]; linarith
  have hp : Interpolates 1 2 a.p θ := by
    dsimp [Interpolates]
    apply (ENNReal.toReal_eq_toReal_iff' hinvfin (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    simp only [ENNReal.toReal_mul, inv_one,
      mul_one, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - θ),
      ENNReal.toReal_ofReal hθ₀.le]
    dsimp [θ]
    rw [ENNReal.toReal_inv]
    ring
  refine ⟨θ, hθ₀, hθ₁, hp, ?_⟩
  exact Interpolation.interpolates_conjugates 1 2 a.p ∞ 2 a.q θ hθ₀.le hθ₁.le hp

/-- The interpolation estimate evaluated in the same sum-domain operator.
The two endpoints are handled without a density assumption on L∞. -/
theorem sum_operator_bound {X : Type u} {Y : Type v}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (T : SumSpace μ 1 2 →ₗ[ℂ] (Y →ₘ[ν] ℂ))
    (h₀ : EndpointBound T 1 ∞ 1) (h₁ : EndpointBound T 2 2 1)
    (a : ExponentPair) (f : Lp ℂ a.p μ) :
    ∃ hf : (f : X →ₘ[μ] ℂ) ∈ SumSpace μ 1 2,
      MemLp (T ⟨f, hf⟩) a.q ν ∧
        (eLpNorm (T ⟨f, hf⟩) a.q ν).toReal ≤ ‖f‖ := by
  by_cases hp₁ : a.p = 1
  · have hq : a.q = ∞ := by
      have hc : ENNReal.HolderConjugate 1 a.q := hp₁ ▸ a.conjugate
      exact @ENNReal.HolderConjugate.unique 1 a.q hc ∞ inferInstance
    have hf : (f : X →ₘ[μ] ℂ) ∈ SumSpace μ 1 2 :=
      (le_sup_left : Lp.LpSubmodule ℂ ℂ 1 μ ≤ SumSpace μ 1 2) (hp₁ ▸ f.property)
    have hm : MemLp (f : X →ₘ[μ] ℂ) 1 μ := hp₁ ▸ Lp.memLp f
    obtain ⟨hmout, hbound⟩ := h₀ ⟨f, hf⟩ hm
    refine ⟨hf, hq.symm ▸ hmout, ?_⟩
    simp only [ENNReal.ofReal_one, one_mul] at hbound
    have hb := ENNReal.toReal_mono (by simpa only [hp₁] using Lp.eLpNorm_ne_top f) hbound
    simpa only [hq, Lp.norm_def, hp₁] using hb
  by_cases hp₂ : a.p = 2
  · have hq : a.q = 2 := by
      have hc : ENNReal.HolderConjugate 2 a.q := hp₂ ▸ a.conjugate
      exact @ENNReal.HolderConjugate.unique 2 a.q hc 2 inferInstance
    have hf : (f : X →ₘ[μ] ℂ) ∈ SumSpace μ 1 2 :=
      (le_sup_right : Lp.LpSubmodule ℂ ℂ 2 μ ≤ SumSpace μ 1 2) (hp₂ ▸ f.property)
    have hm : MemLp (f : X →ₘ[μ] ℂ) 2 μ := hp₂ ▸ Lp.memLp f
    obtain ⟨hmout, hbound⟩ := h₁ ⟨f, hf⟩ hm
    refine ⟨hf, hq.symm ▸ hmout, ?_⟩
    simp only [ENNReal.ofReal_one, one_mul] at hbound
    have hb := ENNReal.toReal_mono (by simpa only [hp₂] using Lp.eLpNorm_ne_top f) hbound
    simpa only [hq, Lp.norm_def, hp₂] using hb
  obtain ⟨θ, hθ₀, hθ₁, hp, hq⟩ := interior_parameter a hp₁ hp₂
  obtain ⟨hf, hm, hb⟩ := Interpolation.riesz_thorin μ ν 1 2 ∞ 2 a.p a.q θ 1 1
    hθ₀ hθ₁ (by norm_num) (by norm_num) hp hq T h₀ h₁ f
  exact ⟨hf, hm, by simpa using hb⟩

/-- Interpolation builds bounded linear maps and transfers compatibility on every
intersection by retaining the common a.e. quotient operator. -/
theorem interpolation_assembly :
    Specs.ExpandedFA.PartIV.HausdorffYoung.InterpolationAssembly.{u,v} := by
  intro X Y _ _ μ ν _ _ formula h
  obtain ⟨T, h₀, h₁, hformula⟩ := h
  have hb := sum_operator_bound μ ν T h₀ h₁
  let lift : ∀ a : ExponentPair, Lp ℂ a.p μ →ₗ[ℂ] Lp ℂ a.q ν := fun a =>
    { toFun := fun f => ⟨T ⟨f, (hb a f).choose⟩, (hb a f).choose_spec.1.eLpNorm_lt_top⟩
      map_add' := by
        intro f g
        apply Subtype.ext
        change T ⟨(f + g : Lp ℂ a.p μ).val, _⟩ = _
        convert T.map_add ⟨f, (hb a f).choose⟩ ⟨g, (hb a g).choose⟩ using 1
      map_smul' := by
        intro c f
        apply Subtype.ext
        change T ⟨(c • f : Lp ℂ a.p μ).val, _⟩ = _
        convert T.map_smul c ⟨f, (hb a f).choose⟩ using 1 }
  have hnorm : ∀ a f, ‖lift a f‖ ≤ 1 * ‖f‖ := by
    intro a f
    exact (hb a f).choose_spec.2.trans_eq (one_mul _).symm
  let F : ∀ a : ExponentPair, Lp ℂ a.p μ →L[ℂ] Lp ℂ a.q ν :=
    fun a => (lift a).mkContinuous 1 (hnorm a)
  refine ⟨⟨F, ?_, ?_, ?_⟩⟩
  · intro a
    exact (F a).opNorm_le_bound (by norm_num) (hnorm a)
  · intro a f hf
    exact hformula ⟨f, (hb a f).choose⟩ hf
  · intro a b f g hfg
    have hval : (f : X →ₘ[μ] ℂ) = (g : X →ₘ[μ] ℂ) := AEEqFun.ext hfg
    have hsum : (⟨f, (hb a f).choose⟩ : SumSpace μ 1 2) = ⟨g, (hb b g).choose⟩ :=
      Subtype.ext hval
    change (T ⟨f, (hb a f).choose⟩ : Y → ℂ) =ᵐ[ν] T ⟨g, (hb b g).choose⟩
    rw [hsum]

/-- Counting-measure L² norm of the circle Fourier coefficients, for arbitrary
L² classes. Both the summability and the norm equality come from Parseval. -/
theorem circle_parseval (f : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ)))) :
    MemLp (fourierCoeff f) 2 (Measure.count : Measure ℤ) ∧
      eLpNorm (fourierCoeff f) 2 Measure.count = eLpNorm f 2 AddCircle.haarAddCircle := by
  have hs := (hasSum_sq_fourierCoeff f).summable
  have hi : Integrable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) Measure.count := by
    apply integrable_count_iff.mpr
    simpa only [Real.norm_eq_abs, abs_sq] using hs
  have hm : MemLp (fourierCoeff f) 2 (Measure.count : Measure ℤ) :=
    (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr hi
  refine ⟨hm, ?_⟩
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    (Lp.memLp f).eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  congr 2
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [integral_countable hi]
  simpa using tsum_sq_fourierCoeff f

private abbrev circleMeasure := AddCircle.haarAddCircle (T := (1 : ℝ))

private theorem circle_sum_mem_one (f : SumSpace circleMeasure 1 2) :
    MemLp (f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ) 1 circleMeasure := by
  have hle : Lp.LpSubmodule ℂ ℂ 2 circleMeasure ≤ Lp.LpSubmodule ℂ ℂ 1 circleMeasure := by
    intro g hg
    exact (Lp.mem_Lp_iff_memLp).mpr
      ((Lp.mem_Lp_iff_memLp.mp hg).mono_exponent (by norm_num))
  exact Lp.mem_Lp_iff_memLp.mp ((sup_le le_rfl hle) f.property)

/-- The coefficient map on the common circle L¹+L² domain. -/
private def circleSumOperator :
    SumSpace circleMeasure 1 2 →ₗ[ℂ] (ℤ →ₘ[Measure.count] ℂ) where
  toFun f := AEEqFun.mk (fourierCoeff (f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ)) (by fun_prop)
  map_add' f g := by
    rw [AEEqFun.mk_add_mk]
    apply AEEqFun.mk_eq_mk.mpr
    apply Filter.Eventually.of_forall
    intro n
    have h := fourierCoeff_congr_ae (AEEqFun.coeFn_add f.val g.val)
    exact congrFun (h.trans (fourierCoeff.add
      (memLp_one_iff_integrable.mp (circle_sum_mem_one f))
      (memLp_one_iff_integrable.mp (circle_sum_mem_one g)))) n
  map_smul' c f := by
    rw [AEEqFun.smul_mk]
    apply AEEqFun.mk_eq_mk.mpr
    apply Filter.Eventually.of_forall
    intro n
    have h := fourierCoeff_congr_ae (AEEqFun.coeFn_smul c f.val)
    exact (congrFun h n).trans (fourierCoeff.const_smul _ c n)

private theorem circle_sum_agreement (f : SumSpace circleMeasure 1 2) :
    circleSumOperator f =ᵐ[Measure.count]
      fourierCoeff (f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ) :=
  AEEqFun.coeFn_mk _ _

private theorem circle_endpoint_one : EndpointBound circleSumOperator 1 ∞ 1 := by
  intro f hf
  have hcoeff : ∀ n : ℤ,
      ‖fourierCoeff (f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ) n‖ ≤
        (eLpNorm (f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ) 1 circleMeasure).toReal := by
    intro n
    calc
      _ ≤ ∫ t, ‖fourier (-n) t • (f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ) t‖
          ∂circleMeasure := norm_integral_le_integral_norm _
      _ = ∫ t, ‖(f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ) t‖ ∂circleMeasure := by
        apply integral_congr_ae
        filter_upwards [] with t
        simp only [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
      _ = _ := by
        have hnorm := L1.norm_eq_integral_norm (hf.toLp _)
        rw [Lp.norm_toLp] at hnorm
        rw [hnorm]
        exact (integral_congr_ae (hf.coeFn_toLp.fun_comp norm)).symm
  have he : eLpNorm (circleSumOperator f) ∞ Measure.count ≤
      eLpNorm (f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ) 1 circleMeasure := by
    rw [eLpNorm_congr_ae (circle_sum_agreement f)]
    have hb := eLpNorm_le_of_ae_bound (p := (∞ : ℝ≥0∞)) (μ := (Measure.count : Measure ℤ))
      (by fun_prop : AEStronglyMeasurable
        (fourierCoeff (f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ)) Measure.count)
      (Filter.Eventually.of_forall hcoeff)
    simpa only [ENNReal.toReal_top, inv_zero, ENNReal.rpow_zero, one_mul,
      ENNReal.ofReal_toReal hf.eLpNorm_ne_top] using hb
  exact ⟨he.trans_lt hf.eLpNorm_lt_top, by simpa only [ENNReal.ofReal_one, one_mul] using he⟩

private theorem circle_endpoint_two : EndpointBound circleSumOperator 2 2 1 := by
  intro f hf
  let g := hf.toLp (f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ)
  have hc : fourierCoeff g = fourierCoeff (f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ) :=
    fourierCoeff_congr_ae hf.coeFn_toLp
  obtain ⟨hm, he⟩ := circle_parseval g
  have heq : eLpNorm (circleSumOperator f) 2 Measure.count =
      eLpNorm (f : AddCircle (1 : ℝ) →ₘ[circleMeasure] ℂ) 2 circleMeasure := by
    rw [eLpNorm_congr_ae (circle_sum_agreement f), ← hc, he,
      eLpNorm_congr_ae hf.coeFn_toLp]
  exact ⟨by rw [memLp_iff, heq]; exact hf.eLpNorm_lt_top,
    by simp only [ENNReal.ofReal_one, one_mul, heq, le_refl]⟩

/-- Hausdorff–Young on R/Z, with normalized measure and compatibility on all
Lp intersections, including arbitrary nonsmooth integrable functions. -/
theorem circle_hausdorff_young :
    Specs.ExpandedFA.PartIV.HausdorffYoung.CircleHausdorffYoung := by
  apply interpolation_assembly circleMeasure Measure.count fourierCoeff
  exact ⟨circleSumOperator, circle_endpoint_one, circle_endpoint_two,
    fun f _ => circle_sum_agreement f⟩

open scoped FourierTransform SchwartzMap ContDiff
open ExpandedFA.Fourier

/-- Compatibility of the integral and Plancherel transforms on the full L¹∩L².
Fubini identifies their pairings with Schwartz tests, which determine locally
integrable functions up to a.e. equality. -/
theorem euclidean_endpoint_compatibility (d : ℕ)
    (f : Lp ℂ 1 (volume : Measure (Euclidean d)))
    (g : Lp ℂ 2 (volume : Measure (Euclidean d)))
    (hfg : (f : Euclidean d → ℂ) =ᵐ[volume] g) :
    (𝓕 (f : Euclidean d → ℂ)) =ᵐ[volume] (𝓕 g : Lp ℂ 2 volume) := by
  have hp : ∀ φ : SchwartzMap (Euclidean d) ℂ,
      (∫ x, φ x * 𝓕 (f : Euclidean d → ℂ) x) =
        ∫ x, φ x * (𝓕 g : Lp ℂ 2 volume) x := by
    intro φ
    have hswap := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ (Euclidean d)) (μ := volume) (ν := volume)
      Real.continuous_fourierChar continuous_inner (L1.integrable_coeFn f) φ.integrable
    have hd := congrArg (fun u : TemperedDistribution (Euclidean d) ℂ => u φ)
      (Lp.fourier_toTemperedDistribution_eq g)
    calc
      _ = ∫ x, (𝓕 φ) x * f x := by
        rw [flip_innerₗ] at hswap
        change (∫ x, 𝓕 (f : Euclidean d → ℂ) x * φ x) =
          ∫ x, f x * 𝓕 (φ : Euclidean d → ℂ) x at hswap
        simpa only [SchwartzMap.fourier_coe, mul_comm] using hswap
      _ = ∫ x, (𝓕 φ) x * g x := by
        apply integral_congr_ae
        filter_upwards [hfg] with x hx
        rw [hx]
      _ = _ := by
        simpa only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
          smul_eq_mul] using hd
  apply ae_eq_of_integral_contDiff_smul_eq
    (Real.Lp.fourierTransform f).continuous.locallyIntegrable
    ((Lp.memLp (𝓕 g : Lp ℂ 2 volume)).locallyIntegrable (by norm_num))
  intro ψ hψ hcψ
  let φ := (hcψ.comp_left (show Complex.ofRealCLM 0 = 0 from rfl)).toSchwartzMap
    (show ContDiff ℝ ∞ (Complex.ofRealCLM ∘ ψ) by fun_prop)
  have h := hp φ
  change (∫ x, (ψ x : ℂ) * 𝓕 (f : Euclidean d → ℂ) x) =
    ∫ x, (ψ x : ℂ) * (𝓕 g : Lp ℂ 2 volume) x at h
  simpa only [Complex.real_smul, Real.Lp.fourierTransform_apply] using h

set_option backward.isDefEq.respectTransparency false in
private def euclideanOnePMap (d : ℕ) :
    (Euclidean d →ₘ[volume] ℂ) →ₗ.[ℂ] (Euclidean d →ₘ[volume] ℂ) where
  domain := Lp.LpSubmodule ℂ ℂ 1 volume
  toFun :=
    { toFun := fun f => AEEqFun.mk (Real.Lp.fourierTransformCLM (Euclidean d) ℂ f)
        (Real.Lp.fourierTransform f).continuous.aestronglyMeasurable
      map_add' := by
        intro f g
        simp only [map_add]
        exact (AEEqFun.mk_add_mk _ _ _ _).symm
      map_smul' := by
        intro c f
        simp only [map_smul]
        exact (AEEqFun.smul_mk _ _ _).symm }

private def euclideanTwoPMap (d : ℕ) :
    (Euclidean d →ₘ[volume] ℂ) →ₗ.[ℂ] (Euclidean d →ₘ[volume] ℂ) where
  domain := Lp.LpSubmodule ℂ ℂ 2 volume
  toFun := (Lp.LpSubmodule ℂ ℂ 2 volume).subtype.comp
    (Lp.fourierTransformₗᵢ (Euclidean d) ℂ).toLinearMap

private theorem euclidean_partial_compatibility (d : ℕ)
    (f : (euclideanOnePMap d).domain) (g : (euclideanTwoPMap d).domain)
    (hfg : (f : Euclidean d →ₘ[volume] ℂ) = g) :
    euclideanOnePMap d f = euclideanTwoPMap d g := by
  apply AEEqFun.ext
  exact (AEEqFun.coeFn_mk _ _).trans
    (euclidean_endpoint_compatibility d f g (by rw [hfg]))

private def euclideanSumOperator (d : ℕ) :
    SumSpace (volume : Measure (Euclidean d)) 1 2 →ₗ[ℂ] (Euclidean d →ₘ[volume] ℂ) :=
  ((euclideanOnePMap d).sup (euclideanTwoPMap d) (euclidean_partial_compatibility d)).toFun

private theorem euclidean_sum_one (d : ℕ) (f : Lp ℂ 1 (volume : Measure (Euclidean d)))
    (hf : (f : Euclidean d →ₘ[volume] ℂ) ∈ SumSpace volume 1 2) :
    euclideanSumOperator d ⟨f, hf⟩ = euclideanOnePMap d f := by
  exact ((LinearPMap.left_le_sup (euclideanOnePMap d) (euclideanTwoPMap d)
    (euclidean_partial_compatibility d)).2 (x := f) (y := ⟨f, hf⟩) rfl).symm

private theorem euclidean_sum_two (d : ℕ) (f : Lp ℂ 2 (volume : Measure (Euclidean d)))
    (hf : (f : Euclidean d →ₘ[volume] ℂ) ∈ SumSpace volume 1 2) :
    euclideanSumOperator d ⟨f, hf⟩ = euclideanTwoPMap d f := by
  exact ((LinearPMap.right_le_sup (euclideanOnePMap d) (euclideanTwoPMap d)
    (euclidean_partial_compatibility d)).2 (x := f) (y := ⟨f, hf⟩) rfl).symm

private theorem euclidean_endpoint_one (d : ℕ) :
    EndpointBound (euclideanSumOperator d) 1 ∞ 1 := by
  intro f hf
  let g : Lp ℂ 1 (volume : Measure (Euclidean d)) := ⟨f, hf⟩
  have he : eLpNorm (𝓕 (g : Euclidean d → ℂ)) ∞ volume ≤ ENNReal.ofReal ‖g‖ := by
    have hb := eLpNorm_le_of_ae_bound (p := (∞ : ℝ≥0∞)) (μ := volume)
      (Real.Lp.fourierTransform g).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x =>
        (Real.norm_fourier_le_integral_norm (g : Euclidean d → ℂ) x).trans_eq
          (L1.norm_eq_integral_norm g).symm))
    simpa only [Real.Lp.coe_fourierTransform, ENNReal.toReal_top, inv_zero,
      ENNReal.rpow_zero, one_mul] using hb
  have heq : eLpNorm (euclideanSumOperator d f) ∞ volume =
      eLpNorm (𝓕 (g : Euclidean d → ℂ)) ∞ volume := by
    rw [euclidean_sum_one d g f.property]
    exact eLpNorm_congr_ae (AEEqFun.coeFn_mk _ _)
  have hb : eLpNorm (euclideanSumOperator d f) ∞ volume ≤
      eLpNorm (f : Euclidean d →ₘ[volume] ℂ) 1 volume := by
    rw [heq]
    change eLpNorm (𝓕 (g : Euclidean d → ℂ)) ∞ volume ≤ eLpNorm g 1 volume
    simpa only [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top g)] using he
  exact ⟨hb.trans_lt hf.eLpNorm_lt_top,
    by simpa only [ENNReal.ofReal_one, one_mul] using hb⟩

private theorem euclidean_endpoint_two (d : ℕ) :
    EndpointBound (euclideanSumOperator d) 2 2 1 := by
  intro f hf
  let g : Lp ℂ 2 (volume : Measure (Euclidean d)) := ⟨f, hf⟩
  have heq : eLpNorm (euclideanSumOperator d f) 2 volume =
      eLpNorm (f : Euclidean d →ₘ[volume] ℂ) 2 volume := by
    rw [euclidean_sum_two d g f.property]
    change eLpNorm (𝓕 g : Lp ℂ 2 volume) 2 volume = eLpNorm g 2 volume
    rw [← Lp.enorm_def, ← Lp.enorm_def]
    simp only [enorm, nnnorm, Lp.norm_fourier_eq]
  exact ⟨by rw [memLp_iff, heq]; exact hf.eLpNorm_lt_top,
    by simp only [ENNReal.ofReal_one, one_mul, heq, le_refl]⟩

/-- Hausdorff–Young on R^d in every dimension, retaining the integral formula
on the full L¹ intersections and compatibility between all exponents. -/
theorem euclidean_hausdorff_young :
    Specs.ExpandedFA.PartIV.HausdorffYoung.EuclideanHausdorffYoung := by
  intro d
  apply interpolation_assembly volume volume integralFourier
  refine ⟨euclideanSumOperator d, euclidean_endpoint_one d, euclidean_endpoint_two d, ?_⟩
  intro f hf
  let g : Lp ℂ 1 (volume : Measure (Euclidean d)) := ⟨f, hf⟩
  rw [euclidean_sum_one d g f.property]
  exact (AEEqFun.coeFn_mk _ _).trans
    (Filter.Eventually.of_forall (fun x => (integralFourier_eq_native _ x).symm))

end ExpandedFA.PartIV.HausdorffYoung
