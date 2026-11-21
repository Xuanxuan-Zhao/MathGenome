import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.Bernstein
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.BernsteinExtremes
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Barycenters
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Approximation.IntervalPolynomials
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith

/-! Bernstein representation on the native compactified half-line.

Existence uses the accepted normalized closed-convex-hull theorem and
representing probabilities. The exponential coordinate is proved to be a
homeomorphism before transporting measures. Integer-time values give all
moments on [0,1], and polynomial density proves uniqueness among all finite
Borel measures. Dominated convergence computes the right limit, and the
finite-parameter alternative is obtained by removing the zero-mass endpoint.
-/

noncomputable section
namespace ExpandedFA.P1.Bernstein
open Set MeasureTheory Filter
open scoped Topology NNReal ENNReal

@[simp] theorem coordinate_top : exponentialCoordinate ∞ = 0 := by
  simp [exponentialCoordinate]

@[simp] theorem coordinate_coe (rate : ℝ≥0) :
    exponentialCoordinate (rate : ℝ≥0∞) = Real.exp (-(rate : ℝ)) := by
  change (EReal.exp (-((rate : ℝ) : EReal))).toReal = _
  rw [← EReal.coe_neg, EReal.exp_coe, ENNReal.toReal_ofReal (Real.exp_pos _).le]

theorem coordinate_mem (rate : ℝ≥0∞) : exponentialCoordinate rate ∈ Icc (0 : ℝ) 1 := by
  induction rate using ENNReal.recTopCoe with
  | top => simp
  | coe rate => simp only [coordinate_coe]; exact ⟨(Real.exp_pos _).le,
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr rate.coe_nonneg)⟩

theorem kernel_interpretation : Specs.ExpandedFA.P1.Bernstein.KernelInterpretation := by
  constructor
  · intro t rate
    simp only [laplaceKernel, coordinate_coe]
    exact (Real.exp_mul _ _).symm
  · intro t
    by_cases ht : t = 0
    · simp [laplaceKernel, ht]
    · simp [laplaceKernel, ht, Real.zero_rpow (NNReal.coe_ne_zero.mpr ht)]

theorem exp_neg_ne_top (rate : ℝ≥0∞) : EReal.exp (-(rate : EReal)) ≠ ∞ := by
  apply (not_congr EReal.exp_eq_top_iff).mpr
  apply (not_congr EReal.neg_eq_top_iff).mpr
  exact EReal.coe_ennreal_ne_bot rate

theorem coordinate_continuous : Continuous exponentialCoordinate := by
  apply continuous_iff_continuousAt.mpr
  intro rate
  exact ContinuousAt.comp (f := fun r : ℝ≥0∞ => EReal.exp (-(r : EReal)))
    (ENNReal.continuousAt_toReal (exp_neg_ne_top rate))
    ((ENNReal.continuous_exp.comp continuous_coe_ennreal_ereal.neg).continuousAt)

abbrev UnitParameter := Icc (0 : ℝ) 1

def coordinateMap (rate : ℝ≥0∞) : UnitParameter := ⟨exponentialCoordinate rate, coordinate_mem rate⟩

theorem coordinateMap_bijective : Function.Bijective coordinateMap := by
  constructor
  · intro rate κ h
    have he : EReal.exp (-(rate : EReal)) = EReal.exp (-(κ : EReal)) :=
      (ENNReal.toReal_eq_toReal_iff' (exp_neg_ne_top rate) (exp_neg_ne_top κ)).mp
        (congrArg (fun r : UnitParameter => (r : ℝ)) h)
    exact EReal.coe_ennreal_injective (neg_injective (EReal.exp_strictMono.injective he))
  · intro r
    by_cases hr : (r : ℝ) = 0
    · exact ⟨∞, Subtype.ext (by simpa [coordinateMap] using hr.symm)⟩
    · let rate : ℝ≥0 := ⟨-Real.log r, neg_nonneg.mpr (Real.log_nonpos r.property.1 r.property.2)⟩
      refine ⟨(rate : ℝ≥0∞), Subtype.ext ?_⟩
      change exponentialCoordinate (rate : ℝ≥0∞) = (r : ℝ)
      rw [coordinate_coe]
      change Real.exp (- -Real.log r) = _
      rw [neg_neg, Real.exp_log (lt_of_le_of_ne r.property.1 (Ne.symm hr))]

/-- The parameter identification is a homeomorphism on the original order topology. -/
def parameterHomeomorph : ℝ≥0∞ ≃ₜ UnitParameter :=
  Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective coordinateMap coordinateMap_bijective)
    (coordinate_continuous.subtype_mk _)

@[simp] theorem parameterHomeomorph_apply (rate : ℝ≥0∞) :
    (parameterHomeomorph rate : ℝ) = exponentialCoordinate rate := rfl

theorem kernel_continuous (t : ℝ≥0) : Continuous (laplaceKernel t) :=
  (Real.continuous_rpow_const t.coe_nonneg).comp coordinate_continuous

theorem kernel_integrable (ν : Measure ℝ≥0∞) [IsFiniteMeasure ν] (t : ℝ≥0) :
    Integrable (laplaceKernel t) ν :=
  (kernel_continuous t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Recover the actual compactified rate from an exponential function. -/
def exponentialParameter (e : exponentials) : ℝ≥0∞ :=
  parameterHomeomorph.symm ⟨e.val 1, (exponential_membership e.property).2.1 1⟩

theorem exponentialParameter_continuous : Continuous exponentialParameter :=
  parameterHomeomorph.symm.continuous.comp
    (((continuous_apply 1).comp continuous_subtype_val).subtype_mk _)

theorem kernel_exponentialParameter (e : exponentials) (t : ℝ≥0) :
    laplaceKernel t (exponentialParameter e) = e.val t := by
  obtain ⟨r, hr, he⟩ := exponentials_eq_image.subset e.property
  have hc : exponentialCoordinate (exponentialParameter e) = e.val 1 :=
    congrArg Subtype.val (parameterHomeomorph.apply_symm_apply _)
  rw [laplaceKernel, hc, ← he]
  simp [powerFunction]

theorem normalized_representation (f : FunctionSpace) (hf : f ∈ normalizedFunctions) :
    ∃ ν : Measure ℝ≥0∞, IsProbabilityMeasure ν ∧ f = laplaceTransform ν := by
  have hsep : ∀ x y : FunctionSpace, x ≠ y →
      ∃ ℓ : FunctionSpace →L[ℝ] ℝ, ℓ x ≠ ℓ y := by
    intro x y hxy
    have : ∃ t, x t ≠ y t := Function.ne_iff.mp hxy
    obtain ⟨t, ht⟩ := this
    exact ⟨ContinuousLinearMap.proj t, ht⟩
  have hC : IsCompact (closure (convexHull ℝ exponentials)) :=
    closed_convex_hull ▸ normalized_compact
  have hfC : f ∈ closure (convexHull ℝ exponentials) := closed_convex_hull ▸ hf
  let : MeasurableSpace exponentials := borel exponentials
  let : BorelSpace exponentials := ⟨rfl⟩
  obtain ⟨μ, hμ, _hreg, htest⟩ := Barycenters.representing_probability ℝ FunctionSpace
    hsep exponentials exponentials_compact hC f hfC
  let := hμ
  let ν := μ.map exponentialParameter
  have hν : IsProbabilityMeasure ν := inferInstance
  refine ⟨ν, hν, funext fun t => ?_⟩
  change f t = ∫ rate, laplaceKernel t rate ∂ν
  rw [MeasureTheory.integral_map exponentialParameter_continuous.measurable.aemeasurable
    (kernel_continuous t).aestronglyMeasurable]
  simpa only [kernel_exponentialParameter, ContinuousLinearMap.proj_apply] using
    (htest (ContinuousLinearMap.proj t)).2

theorem completelyMonotone_all {f : FunctionSpace} (hf : CompletelyMonotone f)
    (hs : List ℝ≥0) (t : ℝ≥0) : 0 ≤ alternatingDifference hs f t := by
  by_cases hz : 0 ∈ hs
  · rw [difference_zero_of_mem hs f hz t]
  · apply hf hs _ t
    intro h hh
    exact pos_iff_ne_zero.mpr (fun heq => hz (heq ▸ hh))

theorem representation_exists (f : FunctionSpace) (hf : CompletelyMonotone f) :
    ∃ ν : Measure ℝ≥0∞, IsFiniteMeasure ν ∧ f = laplaceTransform ν := by
  have hnonneg : ∀ t, 0 ≤ f t := fun t => completelyMonotone_all hf [] t
  have hbound : ∀ t, f t ≤ f 0 := by
    intro t
    have := completelyMonotone_all hf [t] 0
    simpa only [difference_cons, difference_nil, zero_add, sub_nonneg] using this
  by_cases hzero : f 0 = 0
  · refine ⟨0, inferInstance, funext fun t => ?_⟩
    simp only [laplaceTransform, integral_zero_measure]
    exact le_antisymm (hzero ▸ hbound t) (hnonneg t)
  · have hpos : 0 < f 0 := lt_of_le_of_ne (hnonneg 0) (Ne.symm hzero)
    have hnorm : (fun t => f t / f 0) ∈ normalizedFunctions := by
      apply (normalized_iff_positive _).mpr
      refine ⟨div_self hzero, fun hs hh t => ?_⟩
      rw [difference_div]
      exact div_nonneg (hf hs hh t) hpos.le
    obtain ⟨μ, hμ, hrepr⟩ := normalized_representation _ hnorm
    let := hμ
    let c : ℝ≥0 := ⟨f 0, hpos.le⟩
    refine ⟨c • μ, inferInstance, funext fun t => ?_⟩
    change f t = ∫ rate, laplaceKernel t rate ∂(c • μ)
    rw [integral_smul_nnreal_measure]
    have heq := congrFun hrepr t
    change f t / f 0 = ∫ rate, laplaceKernel t rate ∂μ at heq
    change f t = f 0 * _
    rw [← heq, mul_div_cancel₀ _ hzero]

/-- Integration is a continuous linear functional for the supremum norm. -/
def compactIntegral (μ : Measure UnitParameter) [IsFiniteMeasure μ] :
    C(UnitParameter, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun g => ∫ r, g r ∂μ
      map_add' := fun g h => integral_add
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (h.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c g => integral_smul c _ }
    (μ.real univ) (fun g => by
      simpa [mul_comm] using norm_integral_le_of_norm_le_const (μ := μ)
        (Filter.Eventually.of_forall fun r => ContinuousMap.norm_coe_le_norm g r))

theorem measure_eq_of_moments (μ ν : Measure UnitParameter)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hmom : ∀ n : ℕ, (∫ r, (r : ℝ) ^ n ∂μ) = ∫ r, (r : ℝ) ^ n ∂ν) : μ = ν := by
  have hi (p : Polynomial ℝ) (η : Measure UnitParameter) [IsFiniteMeasure η] :
      Integrable (fun r : UnitParameter => p.eval (r : ℝ)) η :=
    (p.toContinuousMapOn _).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hp (p : Polynomial ℝ) :
      (∫ r : UnitParameter, p.eval (r : ℝ) ∂μ) = ∫ r : UnitParameter, p.eval (r : ℝ) ∂ν := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [Polynomial.eval_add]
      rw [integral_add (hi p μ) (hi q μ), integral_add (hi p ν) (hi q ν), hp, hq]
    | monomial n c => simp only [Polynomial.eval_monomial, integral_const_mul, hmom]
  have hclosed : IsClosed {g : C(UnitParameter, ℝ) |
      compactIntegral μ g = compactIntegral ν g} :=
    isClosed_eq (compactIntegral μ).continuous (compactIntegral ν).continuous
  have hpoly : (polynomialFunctions (Icc (0 : ℝ) 1) : Set C(UnitParameter, ℝ)) ⊆
      {g | compactIntegral μ g = compactIntegral ν g} := by
    intro g hg
    rw [polynomialFunctions_coe] at hg
    obtain ⟨p, rfl⟩ := hg
    exact hp p
  have heq (g : C(UnitParameter, ℝ)) : (∫ r, g r ∂μ) = ∫ r, g r ∂ν :=
    closure_minimal hpoly hclosed (continuousMap_mem_polynomialFunctions_closure 0 1 g)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  exact heq g.toContinuousMap

theorem laplaceTransform_injective (μ ν : Measure ℝ≥0∞)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : laplaceTransform μ = laplaceTransform ν) : μ = ν := by
  apply parameterHomeomorph.toMeasurableEquiv.measurableEmbedding.map_injective
  apply measure_eq_of_moments
  intro n
  rw [integral_map_equiv, integral_map_equiv]
  change (∫ rate, exponentialCoordinate rate ^ n ∂μ) =
    ∫ rate, exponentialCoordinate rate ^ n ∂ν
  have hn := congrFun h (n : ℝ≥0)
  simpa only [laplaceTransform, laplaceKernel, NNReal.coe_natCast,
    Real.rpow_natCast, parameterHomeomorph_apply] using hn

theorem representation : Specs.ExpandedFA.P1.Bernstein.Representation := by
  intro f hf
  obtain ⟨ν, hν, heq⟩ := representation_exists f hf
  refine ⟨ν, ⟨hν, heq⟩, ?_⟩
  rintro μ ⟨hμ, hμeq⟩
  let := hμ
  let := hν
  exact laplaceTransform_injective μ ν (hμeq.symm.trans heq)

@[simp] theorem kernel_zero (rate : ℝ≥0∞) : laplaceKernel 0 rate = 1 := by
  simp [laplaceKernel]

@[simp] theorem transform_zero (ν : Measure ℝ≥0∞) : laplaceTransform ν 0 = ν.real univ := by
  simp [laplaceTransform]

theorem kernel_norm_le_one (t : ℝ≥0) (rate : ℝ≥0∞) : ‖laplaceKernel t rate‖ ≤ 1 := by
  change ‖exponentialCoordinate rate ^ (t : ℝ)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (coordinate_mem rate).1 _)]
  exact Real.rpow_le_one (coordinate_mem rate).1 (coordinate_mem rate).2 t.coe_nonneg

theorem kernel_right_limit (rate : ℝ≥0∞) :
    Tendsto (fun t : ℝ≥0 => laplaceKernel t rate) (𝓝[>] 0)
      (𝓝 (({∞}ᶜ : Set ℝ≥0∞).indicator (fun _ => (1 : ℝ)) rate)) := by
  induction rate using ENNReal.recTopCoe with
  | top =>
    rw [indicator_of_notMem (show (∞ : ℝ≥0∞) ∉ ({∞}ᶜ : Set ℝ≥0∞) by simp)]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [kernel_interpretation.2]
    exact (ite_eq_right (ne_of_gt ht)).symm
  | coe rate =>
    have hc : Continuous (fun t : ℝ≥0 => Real.exp (-(rate : ℝ) * (t : ℝ))) :=
      Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)
    simpa only [kernel_interpretation.1, mem_compl_iff, mem_singleton_iff,
      ENNReal.coe_ne_top, not_false_eq_true, indicator_of_mem, NNReal.coe_zero,
      mul_zero, Real.exp_zero] using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

theorem transform_right_limit (ν : Measure ℝ≥0∞) [IsFiniteMeasure ν] :
    Tendsto (laplaceTransform ν) (𝓝[>] 0) (𝓝 (ν.real {∞}ᶜ)) := by
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := ν)
    (l := 𝓝[>] (0 : ℝ≥0)) (F := fun t rate => laplaceKernel t rate)
    (f := ({∞}ᶜ : Set ℝ≥0∞).indicator (fun _ => (1 : ℝ)))
    (fun _ => (1 : ℝ))
    (Eventually.of_forall fun t => (kernel_continuous t).aestronglyMeasurable)
    (Eventually.of_forall fun t => Eventually.of_forall fun rate => kernel_norm_le_one t rate)
    (integrable_const 1) (Eventually.of_forall kernel_right_limit)
  have hi : (∫ rate, ({∞}ᶜ : Set ℝ≥0∞).indicator (fun _ => (1 : ℝ)) rate ∂ν) =
      ν.real {∞}ᶜ := integral_indicator_one (measurableSet_singleton ∞).compl
  rwa [hi] at hlim

theorem measure_endpoint_mass (ν : Measure ℝ≥0∞) [IsFiniteMeasure ν] :
    ∃ L : ℝ, Tendsto (laplaceTransform ν) (𝓝[>] (0 : ℝ≥0)) (𝓝 L) ∧
      ν.real {∞} = laplaceTransform ν 0 - L := by
  refine ⟨ν.real {∞}ᶜ, transform_right_limit ν, ?_⟩
  rw [transform_zero]
  linarith [measureReal_add_measureReal_compl (μ := ν) (measurableSet_singleton ∞)]

theorem endpoint_mass : Specs.ExpandedFA.P1.Bernstein.EndpointMass := by
  intro f ν _ heq
  rw [heq]
  exact measure_endpoint_mass ν

/-- Inclusion of finite parameters into the original compactification. -/
def liftFiniteMeasure (ν : Measure ℝ≥0) : Measure ℝ≥0∞ :=
  ν.map ((↑) : ℝ≥0 → ℝ≥0∞)

instance (ν : Measure ℝ≥0) [IsFiniteMeasure ν] : IsFiniteMeasure (liftFiniteMeasure ν) :=
  inferInstanceAs (IsFiniteMeasure (ν.map ((↑) : ℝ≥0 → ℝ≥0∞)))

theorem lift_transform (ν : Measure ℝ≥0) :
    laplaceTransform (liftFiniteMeasure ν) = finiteLaplaceTransform ν := by
  funext t
  rw [laplaceTransform, liftFiniteMeasure,
    integral_map measurable_coe_nnreal_ennreal.aemeasurable
      (kernel_continuous t).aestronglyMeasurable]
  simp only [kernel_interpretation.1, finiteLaplaceTransform]

@[simp] theorem lift_mass_top (ν : Measure ℝ≥0) : liftFiniteMeasure ν {∞} = 0 := by
  rw [liftFiniteMeasure, Measure.map_apply measurable_coe_nnreal_ennreal (measurableSet_singleton ∞)]
  change ν {r : ℝ≥0 | (r : ℝ≥0∞) = ∞} = 0
  simp only [ENNReal.coe_ne_top, ofPred_false, measure_empty]

theorem finiteTransform_injective (μ ν : Measure ℝ≥0) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : finiteLaplaceTransform μ = finiteLaplaceTransform ν) : μ = ν := by
  apply ENNReal.isOpenEmbedding_coe.measurableEmbedding.map_injective
  apply laplaceTransform_injective
  change laplaceTransform (liftFiniteMeasure μ) = laplaceTransform (liftFiniteMeasure ν)
  simpa only [lift_transform] using h

theorem finiteTransform_right_continuous (ν : Measure ℝ≥0) [IsFiniteMeasure ν] :
    Tendsto (finiteLaplaceTransform ν) (𝓝[>] 0) (𝓝 (finiteLaplaceTransform ν 0)) := by
  rw [← lift_transform]
  have hm : (liftFiniteMeasure ν).real {∞} = 0 := by simp [Measure.real]
  have hc := measureReal_add_measureReal_compl (μ := liftFiniteMeasure ν)
    (measurableSet_singleton ∞)
  rw [hm, zero_add] at hc
  simpa only [transform_zero, hc] using transform_right_limit (liftFiniteMeasure ν)

theorem classical_representation : Specs.ExpandedFA.P1.Bernstein.ClassicalRepresentation := by
  intro f hf
  constructor
  · intro hcont
    obtain ⟨μ, hμ, heq⟩ := representation_exists f hf
    let := hμ
    have hlimit : Tendsto (laplaceTransform μ) (𝓝[>] 0) (𝓝 (f 0)) := by rwa [← heq]
    have hmass : μ.real {∞}ᶜ = f 0 := tendsto_nhds_unique (transform_right_limit μ) hlimit
    have hzero : μ {∞} = 0 := by
      apply (measureReal_eq_zero_iff).mp
      have htotal : μ.real univ = f 0 := by simpa only [transform_zero] using (congrFun heq 0).symm
      linarith [measureReal_add_measureReal_compl (μ := μ) (measurableSet_singleton ∞)]
    let ν := μ.map ENNReal.toNNReal
    have hν : IsFiniteMeasure ν := inferInstance
    have hlift : liftFiniteMeasure ν = μ := by
      rw [liftFiniteMeasure, Measure.map_map measurable_coe_nnreal_ennreal ENNReal.measurable_toNNReal]
      have hae : ∀ᵐ rate ∂μ, rate ≠ ∞ := by
        rw [ae_iff]
        simpa only [not_not, ofPred_eq_eq_singleton] using hzero
      calc
        μ.map (((↑) : ℝ≥0 → ℝ≥0∞) ∘ ENNReal.toNNReal) = μ.map id := by
          apply Measure.map_congr
          filter_upwards [hae] with rate hr
          exact ENNReal.coe_toNNReal hr
        _ = μ := Measure.map_id
    have hrepr : f = finiteLaplaceTransform ν := by rw [← lift_transform, hlift]; exact heq
    refine ⟨ν, ⟨hν, hrepr⟩, ?_⟩
    rintro η ⟨hη, hηeq⟩
    let := hη
    let := hν
    exact finiteTransform_injective η ν (hηeq.symm.trans hrepr)
  · rintro ⟨ν, ⟨hν, heq⟩, _⟩
    let := hν
    rw [heq]
    exact finiteTransform_right_continuous ν

end ExpandedFA.P1.Bernstein
