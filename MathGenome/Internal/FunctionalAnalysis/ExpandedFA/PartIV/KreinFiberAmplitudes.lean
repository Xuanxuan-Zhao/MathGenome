import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinFiberAmplitudes
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinSolutions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.DistributionPrimitive
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace Topology

namespace ExpandedFA.PartIV.KreinFiberAmplitudes
open KreinSpectralKernel

instance intervalMeasure_isFiniteMeasure (R : ℝ) : IsFiniteMeasure (intervalMeasure R) := by
  unfold intervalMeasure
  infer_instance

/-- A formula with no case distinction in the real spectral parameter. -/
theorem C_continuous_formula (ξ t : ℝ) :
    KreinSolutions.Specs.CValue ξ t =
      Real.cos (Real.sqrt (-ξ) * t) + Real.cosh (Real.sqrt ξ * t) - 1 := by
  by_cases hn : ξ < 0
  · simp [KreinSolutions.Specs.CValue, hn, Real.sqrt_eq_zero_of_nonpos hn.le]
  · have hneg : -ξ ≤ 0 := neg_nonpos.mpr (le_of_not_gt hn)
    by_cases hz : ξ = 0
    · simp [hz, KreinSolutions.Specs.CValue]
    · simp [KreinSolutions.Specs.CValue, hn, hz, Real.sqrt_eq_zero_of_nonpos hneg]

private theorem mul_dslope_zero {f : ℝ → ℝ} {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    t * dslope f 0 (a * t) = (f (a * t) - f 0) / a := by
  apply (eq_div_iff ha).2
  have h := sub_smul_dslope f 0 (a * t)
  simp only [sub_zero, smul_eq_mul] at h
  calc
    t * dslope f 0 (a * t) * a = (a * t) * dslope f 0 (a * t) := by ring
    _ = f (a * t) - f 0 := h

/-- Divided differences remove both apparent singularities at parameter zero. -/
theorem S_continuous_formula (ξ t : ℝ) :
    KreinSolutions.Specs.SValue ξ t = t *
      (dslope Real.sin 0 (Real.sqrt (-ξ) * t) +
       dslope Real.sinh 0 (Real.sqrt ξ * t) - 1) := by
  by_cases hn : ξ < 0
  · have ha : Real.sqrt (-ξ) ≠ 0 := Real.sqrt_ne_zero'.mpr (neg_pos.mpr hn)
    simp only [KreinSolutions.Specs.SValue, ite_eq_left hn,
      Real.sqrt_eq_zero_of_nonpos hn.le, zero_mul, dslope_same,
      Real.deriv_sinh, Real.cosh_zero, add_sub_cancel_right]
    simpa only [Real.sin_zero, sub_zero] using (mul_dslope_zero (f := Real.sin) ha t).symm
  · have hneg : -ξ ≤ 0 := neg_nonpos.mpr (le_of_not_gt hn)
    by_cases hz : ξ = 0
    · simp [hz, KreinSolutions.Specs.SValue, Real.deriv_sin, Real.deriv_sinh]
    · have ha : Real.sqrt ξ ≠ 0 := Real.sqrt_ne_zero'.mpr
        (lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hz))
      simp only [KreinSolutions.Specs.SValue, ite_eq_right hn, ite_eq_right hz,
        Real.sqrt_eq_zero_of_nonpos hneg, zero_mul, dslope_same,
        Real.deriv_sin, Real.cos_zero, add_sub_cancel_left]
      simpa only [Real.sinh_zero, sub_zero] using (mul_dslope_zero (f := Real.sinh) ha t).symm

private theorem continuous_dslope_sin : Continuous (dslope Real.sin 0) := by
  rw [← continuousOn_univ]
  exact (continuousOn_dslope (by simp)).2
    ⟨Real.continuous_sin.continuousOn, Real.differentiable_sin.differentiableAt⟩

private theorem continuous_dslope_sinh : Continuous (dslope Real.sinh 0) := by
  rw [← continuousOn_univ]
  exact (continuousOn_dslope (by simp)).2
    ⟨Real.continuous_sinh.continuousOn, Real.differentiable_sinh.differentiableAt⟩

/-- Joint continuity includes the genuine affine zero-parameter odd solution. -/
theorem continuous_solution (p : Bool) :
    Continuous (fun z : ℝ × ℝ => solution p z.1 z.2) := by
  cases p
  · simp only [solution, Bool.false_eq_true, ite_false]
    simp_rw [S_continuous_formula]
    exact continuous_snd.mul
      (((continuous_dslope_sin.comp
        ((Real.continuous_sqrt.comp continuous_fst.neg).mul continuous_snd)).add
       (continuous_dslope_sinh.comp
        ((Real.continuous_sqrt.comp continuous_fst).mul continuous_snd))).sub continuous_const)
  · simp only [solution, ite_true]
    simp_rw [C_continuous_formula]
    fun_prop

/-- The squared real solution norm on the indicated compact interval. -/
def solutionEnergy : Spec.SolutionEnergyType := Spec.solutionEnergyValue

theorem continuous_solutionEnergy : Spec.ContinuousSolutionEnergy := by
  intro p R
  exact continuous_parametric_integral_of_continuous
    ((continuous_solution p).pow 2) isCompact_Icc

/-- Its positivity uses initial data; in the odd case the derivative at zero
precludes a solution vanishing on a neighborhood of zero. -/
theorem positive_solutionEnergy : Spec.PositiveSolutionEnergy := by
  intro p R ξ hR
  have hc : Continuous (solution p ξ) :=
    (continuous_solution p).comp (continuous_const.prodMk continuous_id)
  have hi : Integrable (fun t => solution p ξ t ^ 2) (intervalMeasure R) :=
    (hc.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hn : 0 ≤ Spec.solutionEnergyValue p R ξ := integral_nonneg (fun t => sq_nonneg _)
  apply lt_of_le_of_ne hn
  intro hz
  have hae : (fun t => solution p ξ t ^ 2) =ᵐ[intervalMeasure R] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun t => sq_nonneg _) hi).mp hz.symm
  have hzero : ∀ t ∈ Icc (-R) R, solution p ξ t = 0 := by
    intro t ht
    have hh := Measure.eqOn_Icc_of_ae_eq volume (by linarith : -R ≠ R) hae
      (hc.pow 2).continuousOn continuousOn_const ht
    exact sq_eq_zero_iff.mp hh
  cases p
  · have hevent : solution false ξ =ᶠ[𝓝 (0 : ℝ)] fun _ => 0 := by
      filter_upwards [Ioo_mem_nhds (by linarith : -R < (0 : ℝ)) hR] with t ht
      exact hzero t ⟨ht.1.le, ht.2.le⟩
    have hd : deriv (solution false ξ) 0 = 0 := by
      rw [hevent.deriv_eq]
      exact deriv_const _ _
    have hinit := (KreinSolutions.initialData ξ).2.2.2
    change deriv (KreinSolutions.Specs.SValue ξ) 0 = 0 at hd
    rw [hinit] at hd
    exact one_ne_zero hd
  · have hinit := (KreinSolutions.initialData ξ).1
    have hh := hzero 0 ⟨by linarith, hR.le⟩
    change KreinSolutions.Specs.CValue ξ 0 = 0 at hh
    rw [hinit] at hh
    exact one_ne_zero hh

/-- Measurable normalization, with no choice of point values of an L² class. -/
def amplitudeFormula : Spec.AmplitudeFormulaType := Spec.amplitudeFormulaValue

theorem measurable_amplitudeFormula : Spec.MeasurableAmplitudeFormula := by
  intro p μ h hh
  have hh' : AEStronglyMeasurable (Function.uncurry h) (μ.prod (intervalMeasure 1)) :=
    hh.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  have hZ : AEStronglyMeasurable
      (fun z : ℝ × ℝ => (solution p z.1 z.2 : ℂ)) (μ.prod (intervalMeasure 1)) :=
    (Complex.continuous_ofReal.comp (continuous_solution p)).aestronglyMeasurable
  have hm := (hZ.smul hh').integral_prod_right'
  have hq : AEStronglyMeasurable (fun ξ => (Spec.solutionEnergyValue p 1 ξ : ℂ)⁻¹) μ :=
    (Complex.continuous_ofReal.comp (continuous_solutionEnergy p 1)).measurable.inv.aestronglyMeasurable
  exact hq.smul hm

theorem amplitudeFormula_recovers : Spec.AmplitudeFormulaRecovers := by
  intro p ξ h c hfactor
  have hint : (∫ t, (solution p ξ t : ℂ) • h t ∂intervalMeasure 1) =
      (Spec.solutionEnergyValue p 1 ξ : ℂ) • c := by
    calc
      (∫ t, (solution p ξ t : ℂ) • h t ∂intervalMeasure 1) =
          ∫ t, ((solution p ξ t ^ 2 : ℝ) : ℂ) • c ∂intervalMeasure 1 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae hfactor] with t ht
        rw [ht, smul_smul]
        congr 1
        push_cast
        ring
      _ = (Spec.solutionEnergyValue p 1 ξ : ℂ) • c := by
        rw [integral_smul_const, integral_complex_ofReal]
        rfl
  change (Spec.solutionEnergyValue p 1 ξ : ℂ)⁻¹ • _ = c
  rw [hint, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast (positive_solutionEnergy p 1 ξ zero_lt_one).ne'

/-- Tonelli's nonnegative energy is unchanged after extracting the amplitude
into the measure. The scalar kernel need not itself be measurable for this
identity; all integrals here are lower integrals. -/
theorem amplitude_energy_transfer : Spec.AmplitudeEnergyTransfer := by
  intro μ τ c hc h Z hfactor
  rw [amplitudeMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ μ
      (hc.enorm.pow_const 2) (ae_of_all _ fun ξ => by finiteness)]
  apply lintegral_congr_ae
  filter_upwards [hfactor] with ξ hξ
  calc
    (∫⁻ t, ‖h ξ t‖ₑ ^ 2 ∂τ) = ∫⁻ t, ‖Z ξ t • c ξ‖ₑ ^ 2 ∂τ :=
      lintegral_congr_ae (hξ.mono fun t ht => by
        change ‖h ξ t‖ₑ ^ 2 = ‖Z ξ t • c ξ‖ₑ ^ 2
        rw [ht])
    _ = ∫⁻ t, ‖c ξ‖ₑ ^ 2 * ‖Z ξ t‖ₑ ^ 2 ∂τ := by
      simp_rw [enorm_smul, mul_pow, mul_comm (‖Z ξ _‖ₑ ^ 2)]
    _ = ‖c ξ‖ₑ ^ 2 * ∫⁻ t, ‖Z ξ t‖ₑ ^ 2 ∂τ :=
      lintegral_const_mul' _ _ (by finiteness)

theorem factored_local_energy : Spec.FactoredLocalEnergy := by
  intro H _ _ _ p F G S M K c hc hfactor R hR
  have heq := amplitude_energy_transfer M.μ (intervalMeasure R) c hc K.h
    (fun ξ t => (solution p ξ t : ℂ))
    (hfactor.mono fun _ hξ => ae_restrict_of_ae hξ)
  have hnorm (ξ t : ℝ) : ‖(solution p ξ t : ℂ)‖ₑ ^ 2 =
      ENNReal.ofReal (|solution p ξ t| ^ 2) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _)]
  simp_rw [hnorm] at heq
  rw [← heq, K.energy R hR]
  exact ENNReal.ofReal_lt_top

/-- A strictly positive continuous weight with finite integral controls the
measure on a neighborhood of every point. This is the exact local-finiteness
step needed after proving continuity and positivity of the solution energy. -/
theorem locally_finite_of_positive_weight : Spec.LocalFinitenessCriterion := by
  intro X _ _ _ ν q hq hpos hint
  constructor
  intro x
  have hε : 0 < q x / 2 := half_pos (hpos x)
  have hε0 : ENNReal.ofReal (q x / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨{y | q x / 2 < q y},
    (isOpen_lt continuous_const hq).mem_nhds (by exact half_lt_self (hpos x)), ?_⟩
  apply lt_of_le_of_lt (measure_mono ?_)
    ((meas_ge_le_lintegral_div hq.measurable.ennreal_ofReal.aemeasurable
      hε0 ENNReal.ofReal_ne_top).trans_lt (ENNReal.div_lt_top hint.ne hε0))
  intro y hy
  exact ENNReal.ofReal_le_ofReal hy.le

/-- Local finiteness is a consequence of factorization and kernel energy;
no total-mass premise is used in either parity. -/
theorem factored_locally_finite : Spec.FactoredLocallyFinite := by
  intro H _ _ _ p F G S M K c hc hfactor
  apply locally_finite_of_positive_weight (amplitudeMeasure M.μ c)
    (Spec.solutionEnergyValue p 1) (continuous_solutionEnergy p 1)
    (fun ξ => positive_solutionEnergy p 1 ξ zero_lt_one)
  have he := factored_local_energy K c hc hfactor 1 zero_lt_one
  have heq (ξ : ℝ) : ENNReal.ofReal (Spec.solutionEnergyValue p 1 ξ) =
      ∫⁻ t, ENNReal.ofReal (|solution p ξ t| ^ 2) ∂intervalMeasure 1 := by
    have hz : Continuous (solution p ξ) :=
      (continuous_solution p).comp (continuous_const.prodMk continuous_id)
    have hi : Integrable (fun t => solution p ξ t ^ 2) (intervalMeasure 1) :=
      (hz.pow 2).continuousOn.integrableOn_compact isCompact_Icc
    simpa only [sq_abs, Spec.solutionEnergyValue] using ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun t => sq_nonneg (solution p ξ t))
  simpa only [heq] using he

/-- Extracting the amplitude preserves the full L² pairing, not merely its
formal algebraic expression. Integrability is transferred with the density. -/
theorem weighted_gram_pairing : Spec.WeightedGramPairing := by
  intro H _ _ μ U c hc x y a b hx hy
  have hw : AEMeasurable (fun ξ => ‖c ξ‖ₑ ^ 2) μ := hc.enorm.pow_const 2
  have hfin : ∀ᵐ ξ ∂μ, ‖c ξ‖ₑ ^ 2 < ∞ := ae_of_all _ fun ξ => by finiteness
  have hinner : (fun ξ => ⟪U x ξ, U y ξ⟫_ℂ) =ᵐ[μ]
      fun ξ => (‖c ξ‖ₑ ^ 2).toReal • (star (a ξ) * b ξ) := by
    filter_upwards [hx, hy] with ξ hx hy
    rw [hx, hy, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp only [ENNReal.toReal_pow, enorm, ENNReal.coe_toReal, coe_nnnorm,
      RCLike.real_smul_eq_coe_mul, ← RCLike.ofReal_pow, starRingEnd_apply]
    ring
  refine ⟨?_, ?_⟩
  · apply (integrable_withDensity_iff_integrable_smul₀' hw hfin).2
    exact (L2.integrable_inner (𝕜 := ℂ) (U x) (U y)).congr hinner
  · rw [amplitudeMeasure, integral_withDensity_eq_integral_toReal_smul₀ hw hfin]
    rw [← U.inner_map_map x y, L2.inner_def]
    exact integral_congr_ae hinner

theorem factored_test_transform : Spec.FactoredTestTransform := by
  intro H _ _ _ p F G S M K c hfactor f
  obtain ⟨R, hR, hb⟩ := f.property.2.1.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  have hs : tsupport f.val ⊆ Icc (-R) R := by
    simpa only [Real.closedBall_eq_Icc, zero_sub, zero_add] using hb
  have hfzero : ∀ t, t ∉ Icc (-R) R → f.val t = 0 := by
    intro t ht
    exact image_eq_zero_of_notMem_tsupport (fun h => ht (hs h))
  have hf : MemLp f.val 2 (intervalMeasure R) :=
    f.property.1.continuous.memLp_of_hasCompactSupport f.property.2.1
  let ff : Lp ℂ 2 (intervalMeasure R) := hf.toLp f.val
  have hinput : (∫ t, ff t • G.vectors t ∂intervalMeasure R) =
      KreinSymmetricOperator.Spec.testIntegral G.vectors f.val := by
    calc
      (∫ t, ff t • G.vectors t ∂intervalMeasure R) =
          ∫ t, f.val t • G.vectors t ∂intervalMeasure R :=
        integral_congr_ae (hf.coeFn_toLp.mono fun t ht =>
          congrArg (fun z : ℂ => z • G.vectors t) ht)
      _ = KreinSymmetricOperator.Spec.testIntegral G.vectors f.val :=
        setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun t ht => by rw [hfzero t ht, zero_smul])
  have hrep := K.represents R hR ff
  rw [hinput] at hrep
  filter_upwards [hrep, hfactor] with ξ hrep hfact
  calc
    M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors f.val) ξ =
        ∫ t, ff t • K.h ξ t ∂intervalMeasure R := hrep
    _ = ∫ t, (f.val t * (solution p ξ t : ℂ)) • c ξ ∂intervalMeasure R := by
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp, ae_restrict_of_ae hfact] with t hft ht
      rw [hft, ht, smul_smul]
    _ = (∫ t, f.val t * (solution p ξ t : ℂ) ∂intervalMeasure R) • c ξ :=
      integral_smul_const _ _
    _ = (∫ t, f.val t * (solution p ξ t : ℂ)) • c ξ := by
      congr 1
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun t ht => by rw [hfzero t ht, zero_mul])

theorem factored_gram_identity : Spec.FactoredGramIdentity := by
  intro H _ _ _ p F G S M K c hc hfactor f g
  exact weighted_gram_pairing M.μ M.U c hc
    (KreinSymmetricOperator.Spec.testIntegral G.vectors f.val)
    (KreinSymmetricOperator.Spec.testIntegral G.vectors g.val)
    (fun ξ => ∫ t, f.val t * (solution p ξ t : ℂ))
    (fun ξ => ∫ t, g.val t * (solution p ξ t : ℂ))
    (factored_test_transform K c hfactor f) (factored_test_transform K c hfactor g)

theorem integral_mem_coordinateFiber : Spec.FiberIntegral := by
  intro τ d h hh
  by_cases hi : Integrable h τ
  · intro n hn
    let ev : FiberSpace →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n
    change ev (∫ t, h t ∂τ) = 0
    rw [← ev.integral_comp_comm hi]
    calc
      (∫ t, ev (h t) ∂τ) = ∫ _ : ℝ, (0 : ℂ) ∂τ := by
        apply integral_congr_ae
        filter_upwards [hh] with t ht
        exact ht n hn
      _ = 0 := integral_zero _ _
  · rw [integral_undef hi]
    exact (coordinateFiber d).zero_mem

theorem amplitudeFormula_fiber : Spec.AmplitudeFormulaFiber := by
  intro p ξ d h hh
  apply (coordinateFiber d).smul_mem
  apply integral_mem_coordinateFiber
  filter_upwards [ae_restrict_of_ae hh] with t ht
  exact (coordinateFiber d).smul_mem _ ht

/-- The only remaining input is the almost-everywhere ODE classification.
Measurability comes from the normalization formula, not measurable choice. -/
theorem amplitudeData_of_ae_factorizable : Spec.AmplitudeAssembly := by
  intro H _ _ _ p F G S M K hclass
  let c : ℝ → FiberSpace := amplitudeFormula p K.h
  have hc : AEStronglyMeasurable c M.μ := measurable_amplitudeFormula p M.μ K.h K.measurable
  have hfactor : ∀ᵐ ξ ∂M.μ,
      K.h ξ =ᵐ[volume] fun t => (solution p ξ t : ℂ) • c ξ := by
    filter_upwards [hclass] with ξ hξ
    obtain ⟨a, ha⟩ := hξ
    have he : c ξ = a := amplitudeFormula_recovers p ξ (K.h ξ) a ha
    simpa only [he] using ha
  refine ⟨{
    c := c
    measurable := hc
    fiber := ?_
    factorization := hfactor
    locally_finite := factored_locally_finite K c hc hfactor
    local_energy := factored_local_energy K c hc hfactor
    gram_identity := factored_gram_identity K c hc hfactor }⟩
  filter_upwards [K.fiber_properties] with ξ hξ
  exact amplitudeFormula_fiber p ξ (M.multiplicity ξ) (K.h ξ) hξ.2.1

theorem wronskian : Spec.Wronskian := by
  intro ξ t
  have hsum := KreinSolutions.additionSum ξ t t
  have hdiff := KreinSolutions.additionDifference ξ t t
  simp only [sub_self, (KreinSolutions.initialData ξ).1] at hsum hdiff
  nlinarith

/-- All measurable-amplitude, measure and pairing conclusions are now reduced
to the genuine locally L² distributional ODE classification. -/
theorem amplitudeExistence_of_fiberODEClassification : Spec.AmplitudeReduction := by
  intro hODE H _ _ _ p F G S M K
  apply amplitudeData_of_ae_factorizable K
  filter_upwards [K.fiber_properties] with ξ hξ
  exact hODE p ξ (K.h ξ) hξ.1 hξ.2.2.1 hξ.2.2.2

/-! The distribution argument below is vector-valued. Applying the accepted
scalar kernel theorem to continuous coordinate evaluations gives a constant
in the original Hilbert space, without choosing a sequence of amplitudes. -/

open scoped ContDiff

private abbrev VectorDistribution := LineTest →L[ℂ] FiberSpace

private def testDerivative : LineTest →L[ℂ] LineTest :=
  TestFunction.lineDerivCLM ℂ (1 : ℝ)

private theorem testDerivative_apply (φ : LineTest) (t : ℝ) :
    testDerivative φ t = deriv (fun t => φ t) t :=
  DistributionPrimitive.lineDeriv_apply φ t

private def distributionDerivative (u : VectorDistribution) : VectorDistribution :=
  -u.comp testDerivative

private theorem vector_distribution_kernel (u : VectorDistribution)
    (hu : distributionDerivative u = 0) :
    ∃ a : FiberSpace, ∀ φ : LineTest, u φ = (∫ t : ℝ, φ t) • a := by
  obtain ⟨ρ, hρ⟩ := DistributionPrimitive.exists_normalized_test
    (𝕜 := ℂ) (Ω := ⊤) (by simp)
  refine ⟨u ρ, fun φ => ?_⟩
  apply lp.ext
  funext n
  let ev : FiberSpace →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℕ => ℂ) 2 n
  have hd : DistributionPrimitive.lineDerivative (ev.comp u) = 0 := by
    ext ψ
    have hh := congrArg (fun v : VectorDistribution => ev (v ψ)) hu
    simpa [DistributionPrimitive.lineDerivative, distributionDerivative,
      testDerivative] using hh
  obtain ⟨a, ha⟩ := (DistributionPrimitive.kernel ℂ ⊤ (by simp) (by exact ordConnected_univ)
    (ev.comp u)).mp hd
  have hval := ha ρ
  simp only [ContinuousLinearMap.comp_apply, hρ, mul_one] at hval
  change ev (u φ) = (∫ t : ℝ, φ t) * ev (u ρ)
  exact (ha φ).trans (by rw [hval, mul_comm])

private def testMultiplier (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) :
    LineTest →L[ℂ] LineTest :=
  TestFunction.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hf

private theorem testMultiplier_apply (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (φ : LineTest) (t : ℝ) : testMultiplier f hf φ t = φ t * f t := rfl

private theorem testMultiplier_derivative (f f' : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hf' : ContDiff ℝ ∞ f')
    (hd : ∀ t, HasDerivAt f (f' t) t) (φ : LineTest) :
    testDerivative (testMultiplier f hf φ) =
      testMultiplier f hf (testDerivative φ) + testMultiplier f' hf' φ := by
  ext t
  change deriv (fun t => φ t * f t) t = deriv (fun t => φ t) t * f t + φ t * f' t
  exact ((φ.contDiff.differentiable (by simp) t).hasDerivAt.mul (hd t)).deriv

private def distributionMultiplier (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (u : VectorDistribution) : VectorDistribution := u.comp (testMultiplier f hf)

private theorem distribution_product_rule (f f' : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hf' : ContDiff ℝ ∞ f')
    (hd : ∀ t, HasDerivAt f (f' t) t) (u : VectorDistribution) :
    distributionDerivative (distributionMultiplier f hf u) =
      distributionMultiplier f hf (distributionDerivative u) +
        distributionMultiplier f' hf' u := by
  ext1 φ
  have hh := congrArg (fun ψ : LineTest => u ψ)
    (testMultiplier_derivative f f' hf hf' hd φ)
  simp only [map_add] at hh
  simp only [distributionDerivative, distributionMultiplier,
    neg_apply, ContinuousLinearMap.comp_apply,
    add_apply]
  rw [hh]
  abel

private theorem C_contDiff (ξ : ℝ) : ContDiff ℝ ∞ (KreinSolutions.Specs.CValue ξ) := by
  unfold KreinSolutions.Specs.CValue
  split_ifs <;> fun_prop

private theorem S_contDiff (ξ : ℝ) : ContDiff ℝ ∞ (KreinSolutions.Specs.SValue ξ) := by
  unfold KreinSolutions.Specs.SValue
  split_ifs <;> fun_prop


private def complexC (ξ t : ℝ) : ℂ := KreinSolutions.Specs.CValue ξ t
private def complexS (ξ t : ℝ) : ℂ := KreinSolutions.Specs.SValue ξ t

private theorem complexC_smooth (ξ : ℝ) : ContDiff ℝ ∞ (complexC ξ) :=
  Complex.ofRealCLM.contDiff.comp (C_contDiff ξ)

private theorem complexS_smooth (ξ : ℝ) : ContDiff ℝ ∞ (complexS ξ) :=
  Complex.ofRealCLM.contDiff.comp (S_contDiff ξ)

private theorem complexC_deriv (ξ t : ℝ) :
    HasDerivAt (complexC ξ) ((ξ : ℂ) * complexS ξ t) t := by
  convert! (KreinSolutions.firstDerivatives ξ t).1.ofReal_comp using 1
  simp [complexS, Complex.ofReal_mul]

private theorem complexS_deriv (ξ t : ℝ) :
    HasDerivAt (complexS ξ) (complexC ξ t) t :=
  (KreinSolutions.firstDerivatives ξ t).2.ofReal_comp

private def multiplyC (ξ : ℝ) (u : VectorDistribution) : VectorDistribution :=
  distributionMultiplier (complexC ξ) (complexC_smooth ξ) u

private def multiplyS (ξ : ℝ) (u : VectorDistribution) : VectorDistribution :=
  distributionMultiplier (complexS ξ) (complexS_smooth ξ) u

private theorem distributionDerivative_C (ξ : ℝ) (u : VectorDistribution) :
    distributionDerivative (multiplyC ξ u) = multiplyC ξ (distributionDerivative u) +
      (ξ : ℂ) • multiplyS ξ u := by
  have hh := distribution_product_rule (complexC ξ)
    (fun t => (ξ : ℂ) * complexS ξ t) (complexC_smooth ξ)
    (contDiff_const.mul (complexS_smooth ξ)) (complexC_deriv ξ) u
  dsimp only [multiplyC]
  rw [hh]
  congr 1
  ext1 φ
  change u (testMultiplier _ _ φ) = (ξ : ℂ) • u (testMultiplier _ _ φ)
  rw [← map_smul]
  congr 1
  ext t
  change φ t * ((ξ : ℂ) * complexS ξ t) = (ξ : ℂ) * (φ t * complexS ξ t)
  ring

private theorem distributionDerivative_S (ξ : ℝ) (u : VectorDistribution) :
    distributionDerivative (multiplyS ξ u) = multiplyS ξ (distributionDerivative u) +
      multiplyC ξ u :=
  distribution_product_rule (complexS ξ) (complexC ξ)
    (complexS_smooth ξ) (complexC_smooth ξ) (complexS_deriv ξ) u

private theorem distributionDerivative_sub (u v : VectorDistribution) :
    distributionDerivative (u - v) = distributionDerivative u - distributionDerivative v := by
  ext1 φ
  simp only [distributionDerivative, ContinuousLinearMap.comp_apply, neg_apply, sub_apply]
  abel

private theorem distributionDerivative_smul (c : ℂ) (u : VectorDistribution) :
    distributionDerivative (c • u) = c • distributionDerivative u := by
  ext1 φ
  simp [distributionDerivative]

private theorem multiplyC_smul (ξ : ℝ) (c : ℂ) (u : VectorDistribution) :
    multiplyC ξ (c • u) = c • multiplyC ξ u := by
  ext1 φ
  rfl

private theorem multiplyS_smul (ξ : ℝ) (c : ℂ) (u : VectorDistribution) :
    multiplyS ξ (c • u) = c • multiplyS ξ u := by
  ext1 φ
  rfl

/-- The two constants of motion are actual vectors in the ambient ℓ². -/
private theorem distribution_two_solutions (ξ : ℝ) (u : VectorDistribution)
    (hODE : distributionDerivative (distributionDerivative u) = (ξ : ℂ) • u) :
    ∃ a b : FiberSpace, ∀ φ : LineTest,
      u φ = (∫ t : ℝ, φ t * complexC ξ t) • a +
        (∫ t : ℝ, φ t * complexS ξ t) • b := by
  let A := multiplyC ξ u - multiplyS ξ (distributionDerivative u)
  let B := multiplyC ξ (distributionDerivative u) - (ξ : ℂ) • multiplyS ξ u
  have hA : distributionDerivative A = 0 := by
    dsimp [A]
    rw [distributionDerivative_sub, distributionDerivative_C, distributionDerivative_S,
      hODE, multiplyS_smul]
    abel
  have hB : distributionDerivative B = 0 := by
    dsimp [B]
    rw [distributionDerivative_sub, distributionDerivative_smul,
      distributionDerivative_C, distributionDerivative_S, hODE, multiplyC_smul]
    module
  obtain ⟨a, ha⟩ := vector_distribution_kernel A hA
  obtain ⟨b, hb⟩ := vector_distribution_kernel B hB
  refine ⟨a, b, fun φ => ?_⟩
  have hinv : A (testMultiplier (complexC ξ) (complexC_smooth ξ) φ) +
      B (testMultiplier (complexS ξ) (complexS_smooth ξ) φ) = u φ := by
    dsimp [A, B, multiplyC, multiplyS, distributionMultiplier]
    simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply]
    have hcomm : testMultiplier (complexS ξ) (complexS_smooth ξ)
        (testMultiplier (complexC ξ) (complexC_smooth ξ) φ) =
        testMultiplier (complexC ξ) (complexC_smooth ξ)
          (testMultiplier (complexS ξ) (complexS_smooth ξ) φ) := by
      ext t
      simp only [testMultiplier_apply]
      ring
    rw [hcomm]
    have hwr : testMultiplier (complexC ξ) (complexC_smooth ξ)
          (testMultiplier (complexC ξ) (complexC_smooth ξ) φ) -
        (ξ : ℂ) • testMultiplier (complexS ξ) (complexS_smooth ξ)
          (testMultiplier (complexS ξ) (complexS_smooth ξ) φ) = φ := by
      ext t
      change φ t * complexC ξ t * complexC ξ t -
        (ξ : ℂ) * (φ t * complexS ξ t * complexS ξ t) = φ t
      have hw : complexC ξ t ^ 2 - (ξ : ℂ) * complexS ξ t ^ 2 = 1 := by
        dsimp only [complexC, complexS]
        exact_mod_cast wronskian ξ t
      calc
        _ = φ t * (complexC ξ t ^ 2 - (ξ : ℂ) * complexS ξ t ^ 2) := by ring
        _ = φ t := by rw [hw, mul_one]
    have hw := congrArg (fun ψ : LineTest => u ψ) hwr
    simp only [map_sub, map_smul] at hw
    rw [← hw]
    abel
  rw [ha, hb] at hinv
  exact hinv.symm


private theorem locallyIntegrable_of_local_square (h : ℝ → FiberSpace)
    (hh : ∀ n : ℕ, MemLp h 2 (intervalMeasure (n + 1))) :
    LocallyIntegrable h := by
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt |t|
  refine ⟨Icc (-(n + 1 : ℝ)) (n + 1), Icc_mem_nhds ?_ ?_, ?_⟩
  · have := neg_abs_le t
    linarith
  · have := le_abs_self t
    linarith
  · exact (hh n).integrable (by norm_num)

private def regularDistribution (h : ℝ → FiberSpace) : VectorDistribution :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.lsmul ℂ ℂ) volume h

private theorem regularDistribution_apply (h : ℝ → FiberSpace)
    (hh : LocallyIntegrable h) (φ : LineTest) :
    regularDistribution h φ = ∫ t : ℝ, φ t • h t :=
  TestFunction.integralAgainstBilinCLM_eq_integral (hh.locallyIntegrableOn _)

set_option maxHeartbeats 1000000 in
/-- Every actual locally integrable weak solution is a.e. a classical vector
solution, with constants in ℓ². The parameter may have either sign or be zero. -/
private theorem weakEquation_two_solutions (ξ : ℝ) (h : ℝ → FiberSpace)
    (hh : LocallyIntegrable h) (hODE : WeakEquation ξ h) :
    ∃ a b : FiberSpace,
      h =ᵐ[volume] fun t => complexC ξ t • a + complexS ξ t • b := by
  let u := regularDistribution h
  have hu : distributionDerivative (distributionDerivative u) = (ξ : ℂ) • u := by
    ext1 φ
    simp only [distributionDerivative, neg_apply, ContinuousLinearMap.comp_apply,
      neg_neg, smul_apply]
    dsimp only [u]
    simp_rw [regularDistribution_apply h hh, testDerivative_apply]
    exact hODE φ
  obtain ⟨a, b, hab⟩ := distribution_two_solutions ξ u hu
  refine ⟨a, b, ?_⟩
  have hg : Continuous (fun t => complexC ξ t • a + complexS ξ t • b) :=
    ((complexC_smooth ξ).continuous.smul continuous_const).add
      ((complexS_smooth ξ).continuous.smul continuous_const)
  apply ae_eq_of_integral_contDiff_smul_eq hh hg.locallyIntegrable
  intro f hf hs
  let φ : LineTest := ⟨fun t => (f t : ℂ),
    Complex.ofRealCLM.contDiff.comp hf, hs.comp_left (g := fun t : ℝ => (t : ℂ)) Complex.ofReal_zero, subset_univ _⟩
  have hiC : Integrable (fun t => φ t * complexC ξ t) :=
    (testMultiplier (complexC ξ) (complexC_smooth ξ) φ).continuous.integrable_of_hasCompactSupport
      (testMultiplier (complexC ξ) (complexC_smooth ξ) φ).hasCompactSupport
  have hiS : Integrable (fun t => φ t * complexS ξ t) :=
    (testMultiplier (complexS ξ) (complexS_smooth ξ) φ).continuous.integrable_of_hasCompactSupport
      (testMultiplier (complexS ξ) (complexS_smooth ξ) φ).hasCompactSupport
  calc
    (∫ t, f t • h t) = u φ := by
      rw [regularDistribution_apply h hh]
      rfl
    _ = (∫ t, φ t * complexC ξ t) • a + (∫ t, φ t * complexS ξ t) • b := hab φ
    _ = ∫ t, (φ t * complexC ξ t) • a + (φ t * complexS ξ t) • b := by
      rw [integral_add (hiC.smul_const a) (hiS.smul_const b),
        integral_smul_const, integral_smul_const]
    _ = ∫ t, f t • (complexC ξ t • a + complexS ξ t • b) := by
      congr 1
      funext t
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      simp only [smul_add, smul_smul]
      rfl


/-- Parity removes exactly the other fundamental solution. -/
theorem fiberODE_classification : Spec.FiberODEClassification := by
  intro p ξ h hlocal hpar hODE
  obtain ⟨a, b, hab⟩ := weakEquation_two_solutions ξ h
    (locallyIntegrable_of_local_square h hlocal) hODE
  let g : ℝ → FiberSpace := fun t => complexC ξ t • a + complexS ξ t • b
  have hg : Continuous g :=
    ((complexC_smooth ξ).continuous.smul continuous_const).add
      ((complexS_smooth ξ).continuous.smul continuous_const)
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hab
  have hgp : (fun t => g (-t)) = fun t => KreinSymmetricOperator.Spec.paritySign p • g t := by
    have hae : (fun t => g (-t)) =ᵐ[volume]
        (fun t => KreinSymmetricOperator.Spec.paritySign p • g t) := by
      filter_upwards [hab, hneg, hpar] with t ht hn hp
      exact hn.symm.trans (hp.trans (congrArg (fun x : FiberSpace =>
        KreinSymmetricOperator.Spec.paritySign p • x) ht))
    exact Measure.eq_of_ae_eq hae (hg.comp continuous_neg) (by fun_prop)
  have hC0 : complexC ξ 0 = 1 := by
    simp [complexC, (KreinSolutions.initialData ξ).1]
  have hS0 : complexS ξ 0 = 0 := by
    simp [complexS, (KreinSolutions.initialData ξ).2.2.1]
  cases p
  · have hz := congrFun hgp 0
    have haa : a = -a := by
      simpa [g, hC0, hS0, KreinSymmetricOperator.Spec.paritySign] using hz
    have ha : a = 0 := by
      have hh : (2 : ℂ) • a = 0 := by
        rw [two_smul]
        exact add_eq_zero_iff_eq_neg.mpr haa
      exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
    refine ⟨b, ?_⟩
    simpa only [ha, smul_zero, zero_add, solution, Bool.false_eq_true, ite_false,
      complexS] using hab
  · have hgd : HasDerivAt g b 0 := by
      have hd := ((complexC_deriv ξ 0).smul_const a).add
        ((complexS_deriv ξ 0).smul_const b)
      simpa only [hC0, hS0, mul_zero, zero_smul, one_smul, zero_add] using! hd
    have hgdneg : HasDerivAt (fun t => g (-t)) (-b) 0 := by
      have hd : HasDerivAt g b (-(0 : ℝ)) := by simpa only [neg_zero] using hgd
      convert! hd.scomp 0 (hasDerivAt_neg (0 : ℝ)) using 1; simp
    have hge : (fun t => g (-t)) = g := by
      simpa [KreinSymmetricOperator.Spec.paritySign] using hgp
    rw [hge] at hgdneg
    have hbb : -b = b := hgdneg.unique hgd
    have hb : b = 0 := by
      have hh : (2 : ℂ) • b = 0 := by
        rw [two_smul]
        exact add_eq_zero_iff_eq_neg.mpr hbb.symm
      exact (smul_eq_zero.mp hh).resolve_left (by norm_num)
    refine ⟨a, ?_⟩
    simpa only [hb, smul_zero, add_zero, solution, ite_true, complexC] using hab

/-- The complete unconditional amplitude construction, including the original
local-energy and absolutely integrable Gram conclusions. -/
theorem exists_amplitude : KreinSpectralKernel.Spec.AmplitudeExistence :=
  amplitudeExistence_of_fiberODEClassification fiberODE_classification

end ExpandedFA.PartIV.KreinFiberAmplitudes
