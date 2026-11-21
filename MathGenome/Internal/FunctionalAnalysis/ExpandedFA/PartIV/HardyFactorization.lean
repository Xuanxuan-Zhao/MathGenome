import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyFactorization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HardyInnerOuter
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.BlaschkeProducts
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.Herglotz
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Measure.Decomposition.IntegralRNDeriv

noncomputable section
open MeasureTheory Filter Set Complex Metric
open scoped Topology Real ENNReal
namespace ExpandedFA.PartIV.HardyFactorization
open HardyDiskSpec HardyLogModulus

lemma disk_eq_unitDisk : disk = PositiveHarmonic.unitDisk := by
  ext z
  simp [disk, PositiveHarmonic.unitDisk]

lemma zero_mem_disk : (0 : ℂ) ∈ disk := by simp [disk]

/-- A primitive of the logarithmic derivative constructs a global analytic
logarithm on the disk, without imposing a principal-branch condition. -/
lemma exists_holomorphic_log {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F disk)
    (hn : ∀ z ∈ disk, F z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L disk ∧
      ∀ z ∈ disk, Complex.exp (L z) = F z := by
  have hder : DifferentiableOn ℂ (fun z => deriv F z / F z) disk :=
    (hF.deriv isOpen_ball).div hF hn
  obtain ⟨L, hL0, hL⟩ := hder.isExactOn_ball.with_val_at 0 (Complex.log (F 0))
  let G : ℂ → ℂ := fun z => F z * Complex.exp (-L z)
  have hG (z : ℂ) (hz : z ∈ disk) : HasDerivAt G 0 z := by
    have hd := ((hF.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt).mul
      ((hL z hz).neg.cexp)
    convert hd using 1
    field_simp [hn z hz]
    ring
  have hconst : ∀ z ∈ disk, G z = G 0 := by
    intro z hz
    apply isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
      (fun z hz => (hG z hz).differentiableAt.differentiableWithinAt)
      (fun z hz => (hG z hz).deriv) hz zero_mem_disk
  have hG0 : G 0 = 1 := by
    dsimp [G]
    rw [hL0, Complex.exp_neg, Complex.exp_log (hn 0 zero_mem_disk)]
    exact mul_inv_cancel₀ (hn 0 zero_mem_disk)
  refine ⟨L, fun z hz => (hL z hz).differentiableAt.differentiableWithinAt, ?_⟩
  intro z hz
  have hg := (hconst z hz).trans hG0
  dsimp [G] at hg
  rw [Complex.exp_neg] at hg
  exact (eq_of_div_eq_one (by simpa [div_eq_mul_inv] using hg)).symm

theorem factorization : Spec.Factorization := HardyInnerOuter.factorization

theorem uniqueness : Spec.Uniqueness := HardyInnerOuter.uniqueness

theorem outer_formula : Spec.OuterFormula := HardyInnerOuter.outer_formula

theorem zero_multiplicity : Spec.ZeroMultiplicity := BlaschkeProducts.canonical_orders

lemma singularFactor_norm (μ : Measure _root_.Circle) [IsFiniteMeasure μ]
    {c : ℂ} (hc : ‖c‖ = 1) {z : ℂ} (hz : z ∈ disk) :
    ‖singularFactor μ c z‖ = Real.exp (-PositiveHarmonic.poissonExtension μ z) := by
  rw [singularFactor, norm_mul, hc, one_mul, Complex.norm_exp, Complex.neg_re,
    Herglotz.herglotzTransform_re μ 0 (disk_eq_unitDisk ▸ hz)]

lemma singularFactor_nonzero (μ : Measure _root_.Circle) {c : ℂ} (hc : ‖c‖ = 1)
    (z : ℂ) : singularFactor μ c z ≠ 0 := by
  apply mul_ne_zero _ (Complex.exp_ne_zero _)
  intro he
  simp [he] at hc

lemma singularFactor_holomorphic (μ : Measure _root_.Circle) [IsFiniteMeasure μ]
    (c : ℂ) : DifferentiableOn ℂ (singularFactor μ c) disk := by
  exact (((Herglotz.differentiableOn_herglotzTransform μ 0).mono
    (by rw [disk_eq_unitDisk])).neg.cexp).const_mul c

lemma singularFactor_bound (μ : Measure _root_.Circle) [IsFiniteMeasure μ]
    {c : ℂ} (hc : ‖c‖ = 1) {z : ℂ} (hz : z ∈ disk) :
    ‖singularFactor μ c z‖ ≤ 1 := by
  rw [singularFactor_norm μ hc hz, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (PositiveHarmonic.poissonExtension_nonneg μ (disk_eq_unitDisk ▸ hz))

/-- All finite positive measures give bounded zero-free analytic exponentials.
Innerness is a separate conclusion requiring singularity. -/
lemma singularFactor_hardy (μ : Measure _root_.Circle) [IsFiniteMeasure μ]
    {c : ℂ} (hc : ‖c‖ = 1) :
    ∃ s : H2, ZeroFree s ∧ Set.EqOn (eval s) (singularFactor μ c) disk ∧
      ∀ z ∈ disk, ‖eval s z‖ ≤ 1 := by
  obtain ⟨s, hs, _⟩ := BlaschkeProducts.hardy_of_bound_one
    (singularFactor_holomorphic μ c) (fun _ hz => singularFactor_bound μ hc hz)
  exact ⟨s, fun z hz => (hs hz).symm ▸ singularFactor_nonzero μ hc z,
    hs, fun z hz => (hs hz).symm ▸ singularFactor_bound μ hc hz⟩

/-- Herglotz produces a finite positive measure from any zero-free inner
function. Singularity will be established separately, not assumed here. -/
lemma zero_free_positive_representation (s : H2) (hs : IsInner s) (hn : ZeroFree s) :
    ∃ (μ : Measure _root_.Circle) (c : ℂ), IsFiniteMeasure μ ∧ ‖c‖ = 1 ∧
      Set.EqOn (eval s) (singularFactor μ c) disk := by
  obtain ⟨L, hL, he⟩ := exists_holomorphic_log
    (HardyDisk.analytic_evaluation s).differentiableOn hn
  have hpos : Herglotz.NonnegativeHolomorphic (fun z => -L z) := by
    refine ⟨disk_eq_unitDisk ▸ hL.neg, ?_⟩
    intro z hz
    have hz' : z ∈ disk := disk_eq_unitDisk.symm ▸ hz
    have hb := BlaschkeProducts.inner_bound s hs z hz'
    rw [← he z hz', Complex.norm_exp, Real.exp_le_one_iff] at hb
    simpa using hb
  obtain ⟨⟨μ, d⟩, hμ, _⟩ := Herglotz.representation _ hpos
  refine ⟨μ, Complex.exp (-(Complex.I * (d : ℂ))), hμ.1, ?_, ?_⟩
  · simp [Complex.norm_exp]
  · intro z hz
    have heq := hμ.2.2 z (disk_eq_unitDisk ▸ hz)
    have htr : Herglotz.herglotzTransform μ d z =
        Complex.I * (d : ℂ) + Herglotz.herglotzTransform μ 0 z := by
      simp [Herglotz.herglotzTransform]
    rw [htr] at heq
    rw [← he z hz, singularFactor, ← Complex.exp_add]
    congr 1
    linear_combination -heq

/-- Even without assuming singularity, the finite positive measure and phase
are uniquely determined by the zero-free exponential. -/
lemma positive_parameters_unique {μ ν : Measure _root_.Circle}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {c d : ℂ}
    (hc : ‖c‖ = 1) (hd : ‖d‖ = 1)
    (he : Set.EqOn (singularFactor μ c) (singularFactor ν d) disk) :
    μ = ν ∧ c = d := by
  have hμν : μ = ν := by
    apply PositiveHarmonic.poissonExtension_injective
    intro z hz
    have hz' : z ∈ disk := disk_eq_unitDisk.symm ▸ hz
    have h := congrArg norm (he hz')
    rw [singularFactor_norm μ hc hz', singularFactor_norm ν hd hz',
      Real.exp_eq_exp] at h
    exact neg_injective h
  subst ν
  refine ⟨rfl, ?_⟩
  have h0 := he zero_mem_disk
  exact mul_right_cancel₀ (Complex.exp_ne_zero _) h0

/-- The two circle models, with their actual normalized Haar measures. -/
def circleEquiv : BoundaryCircle ≃ₜ _root_.Circle :=
  AddCircle.homeomorphCircle (by positivity : 2 * π ≠ 0)

lemma coe_circleEquiv (t : BoundaryCircle) : (circleEquiv t : ℂ) = circlePoint t := by
  simp [circleEquiv, AddCircle.homeomorphCircle_apply, circlePoint]

lemma circleEquiv_measurePreserving :
    MeasurePreserving circleEquiv circleMeasure PositiveHarmonic.circleHaar := by
  refine ⟨circleEquiv.continuous.measurable, ?_⟩
  rw [PositiveHarmonic.circleHaar_eq_map]
  congr 1
  funext t
  exact AddCircle.homeomorphCircle_apply _ t

lemma circleEquiv_symm_measurePreserving :
    MeasurePreserving circleEquiv.symm PositiveHarmonic.circleHaar circleMeasure :=
  MeasurePreserving.symm circleEquiv.toMeasurableEquiv circleEquiv_measurePreserving

/-- Density measures are genuine positive measures, not signed formal integrals. -/
def densityMeasure (g : _root_.Circle → ℝ) : Measure _root_.Circle :=
  PositiveHarmonic.circleHaar.withDensity (fun ζ => ENNReal.ofReal (g ζ))

lemma densityMeasure_finite {g : _root_.Circle → ℝ}
    (hg : Integrable g PositiveHarmonic.circleHaar) : IsFiniteMeasure (densityMeasure g) := by
  apply isFiniteMeasure_withDensity
  exact ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hg.hasFiniteIntegral).ne

lemma densityMeasure_absolutelyContinuous (g : _root_.Circle → ℝ) :
    densityMeasure g ≪ PositiveHarmonic.circleHaar := withDensity_absolutelyContinuous _ _

lemma densityMeasure_zero_iff {g : _root_.Circle → ℝ}
    (hg : Integrable g PositiveHarmonic.circleHaar)
    (hn : ∀ᵐ ζ ∂PositiveHarmonic.circleHaar, 0 ≤ g ζ) :
    densityMeasure g = 0 ↔ g =ᵐ[PositiveHarmonic.circleHaar] 0 := by
  rw [densityMeasure, withDensity_eq_zero_iff hg.aemeasurable.ennreal_ofReal]
  constructor
  · intro h
    filter_upwards [h, hn] with ζ hζ hnζ
    simpa using le_antisymm (ENNReal.ofReal_eq_zero.mp hζ) hnζ
  · intro h
    filter_upwards [h] with ζ hζ
    simp [hζ]

/-- Transfer an integrable density, including its Herglotz integral, between
the two circle models. -/
lemma herglotz_density {g : _root_.Circle → ℝ}
    (hg : Integrable g PositiveHarmonic.circleHaar)
    (hn : ∀ᵐ ζ ∂PositiveHarmonic.circleHaar, 0 ≤ g ζ)
    {z : ℂ} (_hz : z ∈ disk) :
    Herglotz.herglotzTransform (densityMeasure g) 0 z =
      logarithmicIntegral (g ∘ circleEquiv) z := by
  simp only [Herglotz.herglotzTransform, ofReal_zero, mul_zero, zero_add, densityMeasure]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hg.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ ζ : _root_.Circle, (((ζ : ℂ) + z) / ((ζ : ℂ) - z)) * (g ζ : ℂ)
        ∂PositiveHarmonic.circleHaar := by
      apply integral_congr_ae
      filter_upwards [hn] with ζ hζ
      simp [ENNReal.toReal_ofReal hζ, mul_comm]
    _ = _ := by
      rw [← circleEquiv_measurePreserving.integral_comp circleEquiv.measurableEmbedding]
      simp only [logarithmicIntegral, coe_circleEquiv, Function.comp_apply]

lemma poisson_density {g : _root_.Circle → ℝ}
    (hg : Integrable g PositiveHarmonic.circleHaar)
    (hn : ∀ᵐ ζ ∂PositiveHarmonic.circleHaar, 0 ≤ g ζ)
    {z : ℂ} (hz : z ∈ disk) :
    PositiveHarmonic.poissonExtension (densityMeasure g) z =
      poissonLog (g ∘ circleEquiv) z := by
  let := densityMeasure_finite hg
  rw [← Herglotz.herglotzTransform_re _ 0 (disk_eq_unitDisk ▸ hz),
    herglotz_density hg hn hz]
  exact logarithmicIntegral_re
    (circleEquiv_measurePreserving.integrable_comp_of_integrable hg) hz

/-- Positivity of the difference of Poisson integrals is equivalent to measure
order; existence and uniqueness of positive harmonic representation prove the
nontrivial direction. -/
lemma measure_le_of_poisson_le (μ ν : Measure _root_.Circle)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hle : ∀ z ∈ PositiveHarmonic.unitDisk,
      PositiveHarmonic.poissonExtension ν z ≤ PositiveHarmonic.poissonExtension μ z) :
    ν ≤ μ := by
  have hh : PositiveHarmonic.NonnegativeHarmonic (fun z =>
      PositiveHarmonic.poissonExtension μ z - PositiveHarmonic.poissonExtension ν z) :=
    ⟨(PositiveHarmonic.poissonExtension_harmonic μ).sub
      (PositiveHarmonic.poissonExtension_harmonic ν), fun z hz => sub_nonneg.mpr (hle z hz)⟩
  obtain ⟨ρ, hρ, _⟩ := PositiveHarmonic.representation _ hh
  let := hρ.1
  have heq : μ = ν + ρ := by
    apply PositiveHarmonic.poissonExtension_injective
    intro z hz
    simp only [PositiveHarmonic.poissonExtension]
    rw [integral_add_measure
      (PositiveHarmonic.integrable_circlePoissonKernel ν hz)
      (PositiveHarmonic.integrable_circlePoissonKernel ρ hz)]
    change PositiveHarmonic.poissonExtension μ z =
      PositiveHarmonic.poissonExtension ν z + PositiveHarmonic.poissonExtension ρ z
    rw [← hρ.2.2.1 z hz]
    ring
  rw [heq]
  exact Measure.le_add_right le_rfl

lemma singularFactor_add (μ ν : Measure _root_.Circle)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : ℂ) {z : ℂ} (hz : z ∈ disk) :
    singularFactor (μ + ν) c z = singularFactor μ 1 z * singularFactor ν c z := by
  have hμ := PositiveHarmonic.integrable_circleHerglotzKernel μ (disk_eq_unitDisk ▸ hz)
  have hν := PositiveHarmonic.integrable_circleHerglotzKernel ν (disk_eq_unitDisk ▸ hz)
  have hsum : Herglotz.herglotzTransform (μ + ν) 0 z =
      Herglotz.herglotzTransform μ 0 z + Herglotz.herglotzTransform ν 0 z := by
    simp only [Herglotz.herglotzTransform_eq_integral, ofReal_zero, mul_zero, zero_add]
    exact integral_add_measure hμ hν
  simp only [singularFactor, hsum, neg_add, Complex.exp_add, one_mul]
  ring

lemma singularFactor_density {g : _root_.Circle → ℝ}
    (hg : Integrable g PositiveHarmonic.circleHaar)
    (hn : ∀ᵐ ζ ∂PositiveHarmonic.circleHaar, 0 ≤ g ζ)
    (c : ℂ) {z : ℂ} (hz : z ∈ disk) :
    singularFactor (densityMeasure g) c z =
      exponentialFactor (fun t => -g (circleEquiv t)) c z := by
  rw [singularFactor, herglotz_density hg hn hz, exponentialFactor]
  congr 2
  simp only [logarithmicIntegral, Function.comp_apply, ofReal_neg, mul_neg]
  rw [integral_neg]

/-- An inner Herglotz exponential has no absolutely continuous measure part.
The boundary product identity detects that part without presupposing a
boundary differentiation theorem for measures. -/
lemma measure_singular_of_inner {μ : Measure _root_.Circle} [IsFiniteMeasure μ]
    {c : ℂ} (hc : ‖c‖ = 1) {s : H2} (hs : IsInner s)
    (he : Set.EqOn (eval s) (singularFactor μ c) disk) :
    μ ⟂ₘ PositiveHarmonic.circleHaar := by
  let : IsProbabilityMeasure PositiveHarmonic.circleHaar :=
    PositiveHarmonic.circleHaar_probability
  let g : _root_.Circle → ℝ := fun ζ => (μ.rnDeriv PositiveHarmonic.circleHaar ζ).toReal
  have hg : Integrable g PositiveHarmonic.circleHaar := Measure.integrable_toReal_rnDeriv
  have hgn : ∀ᵐ ζ ∂PositiveHarmonic.circleHaar, 0 ≤ g ζ :=
    Eventually.of_forall fun _ => ENNReal.toReal_nonneg
  have hν : densityMeasure g =
      PositiveHarmonic.circleHaar.withDensity (μ.rnDeriv PositiveHarmonic.circleHaar) := by
    apply withDensity_congr_ae
    filter_upwards [μ.rnDeriv_lt_top PositiveHarmonic.circleHaar] with ζ hζ
    exact ENNReal.ofReal_toReal hζ.ne
  let ρ := μ.singularPart PositiveHarmonic.circleHaar
  have hsum : densityMeasure g + ρ = μ := by
    rw [hν]
    exact μ.rnDeriv_add_singularPart PositiveHarmonic.circleHaar
  let h : BoundaryCircle → ℝ := fun t => -g (circleEquiv t)
  have hh : Integrable h circleMeasure :=
    (circleEquiv_measurePreserving.integrable_comp_of_integrable hg).neg
  have hhn : ∀ᵐ t ∂circleMeasure, h t ≤ 0 := by
    filter_upwards [circleEquiv_measurePreserving.quasiMeasurePreserving.ae hgn] with t ht
    exact neg_nonpos.mpr ht
  have hexp : Integrable (fun t => Real.exp (2 * h t)) circleMeasure := by
    apply (integrable_const (1 : ℝ)).mono'
      (hh.aestronglyMeasurable.const_mul 2).aemeasurable.exp.aestronglyMeasurable
    filter_upwards [hhn] with t ht
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    linarith
  obtain ⟨o, ho, hbo⟩ := exponential_boundary_modulus hh hexp (c := 1) (by simp)
  obtain ⟨v, _, hv, hbv⟩ := singularFactor_hardy ρ hc
  let := densityMeasure_finite hg
  have hp : ∀ z ∈ disk, eval s z = eval o z * eval v z := by
    intro z hz
    rw [he hz, ← hsum, singularFactor_add _ _ c hz, ho hz, hv hz,
      singularFactor_density hg hgn 1 hz]
  have hbprod := boundary_mul_of_eval_mul hp
  have hbv' := BlaschkeProducts.boundary_norm_le_one hbv
  have hzero : g ∘ circleEquiv =ᵐ[circleMeasure] 0 := by
    filter_upwards [hbprod, hbo, hbv', hs.2, hhn] with t hpt hot hvt hst hht
    have hnorm := congrArg norm hpt
    rw [hst, norm_mul, hot] at hnorm
    have hpos : 0 < Real.exp (h t) := Real.exp_pos _
    have hle : 1 ≤ Real.exp (h t) := by nlinarith
    have hnonneg : 0 ≤ h t := Real.one_le_exp_iff.mp hle
    have hval : h t = 0 := le_antisymm hht hnonneg
    simpa [h, Function.comp_def] using neg_eq_zero.mp hval
  have hgzero : g =ᵐ[PositiveHarmonic.circleHaar] 0 := by
    filter_upwards [circleEquiv_symm_measurePreserving.quasiMeasurePreserving.ae hzero] with ζ hζ
    simpa only [Function.comp_apply, circleEquiv.apply_symm_apply, Pi.zero_apply] using hζ
  have hνzero := (densityMeasure_zero_iff hg hgn).mpr hgzero
  have hμ : μ = ρ := by simpa [hνzero] using hsum.symm
  rw [hμ]
  exact μ.mutuallySingular_singularPart PositiveHarmonic.circleHaar

/-- Conversely singularity forces the Hardy boundary modulus to be one.
Logarithmic majorization and order of Poisson extensions detect a nonzero
absolutely continuous boundary logarithm if that modulus were smaller. -/
lemma inner_of_measure_singular {μ : Measure _root_.Circle} [IsFiniteMeasure μ]
    (hμ : μ ⟂ₘ PositiveHarmonic.circleHaar) {c : ℂ} (hc : ‖c‖ = 1)
    {s : H2} (he : Set.EqOn (eval s) (singularFactor μ c) disk) : IsInner s := by
  have hb : ∀ z ∈ disk, ‖eval s z‖ ≤ 1 := by
    intro z hz
    rw [he hz]
    exact singularFactor_bound μ hc hz
  have hs0 : s ≠ 0 := by
    intro h
    have hne := singularFactor_nonzero μ hc 0
    rw [← he zero_mem_disk, h] at hne
    exact hne (by simp [HardyDiskSpec.eval])
  obtain ⟨hlog, hbnz⟩ := boundary_log_integrable s hs0
  have hbb := BlaschkeProducts.boundary_norm_le_one hb
  have hln : ∀ᵐ t ∂circleMeasure, 0 ≤ -boundaryLog s t := by
    filter_upwards [hbb] with t ht
    exact neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) ht)
  let g : _root_.Circle → ℝ := fun ζ => -boundaryLog s (circleEquiv.symm ζ)
  have hg := circleEquiv_symm_measurePreserving.integrable_comp_of_integrable
    (g := fun t => -boundaryLog s t) hlog.neg
  change Integrable g PositiveHarmonic.circleHaar at hg
  have hgn := circleEquiv_symm_measurePreserving.quasiMeasurePreserving.ae hln
  change (∀ᵐ ζ ∂PositiveHarmonic.circleHaar, 0 ≤ g ζ) at hgn
  let := densityMeasure_finite hg
  have hgle : densityMeasure g ≤ μ := by
    apply measure_le_of_poisson_le
    intro z hz
    have hz' : z ∈ disk := disk_eq_unitDisk.symm ▸ hz
    rw [poisson_density hg hgn hz']
    have hp : poissonLog (g ∘ circleEquiv) z = -poissonLog (boundaryLog s) z := by
      simp only [poissonLog, Function.comp_apply, g, circleEquiv.symm_apply_apply, mul_neg]
      rw [integral_neg]
    rw [hp]
    have hsn : eval s z ≠ 0 := by
      rw [he hz']
      exact singularFactor_nonzero μ hc z
    have hm := log_majorization s hs0 z hz' hsn
    rw [he hz', singularFactor_norm μ hc hz', Real.log_exp] at hm
    linarith
  have hνzero : densityMeasure g = 0 :=
    Measure.eq_zero_of_absolutelyContinuous_of_mutuallySingular
      (densityMeasure_absolutelyContinuous g) (hμ.mono hgle le_rfl)
  have hgzero := (densityMeasure_zero_iff hg hgn).mp hνzero
  have hlogzero : (fun t => -boundaryLog s t) =ᵐ[circleMeasure] 0 := by
    filter_upwards [circleEquiv_measurePreserving.quasiMeasurePreserving.ae hgzero] with t ht
    simpa only [g, circleEquiv.symm_apply_apply, Pi.zero_apply] using ht
  refine ⟨⟨1, hb⟩, ?_⟩
  filter_upwards [hlogzero, hbnz] with t ht hn
  exact Real.eq_one_of_pos_of_log_eq_zero (norm_pos_iff.mpr hn) (neg_eq_zero.mp ht)

/-- Zero-free inner functions correspond exactly to singular positive
Herglotz measures, with a unique unimodular phase. -/
theorem zero_free_representation : Spec.ZeroFreeRepresentation := by
  intro s hs hn
  obtain ⟨μ, c, hμ, hc, he⟩ := zero_free_positive_representation s hs hn
  let := hμ
  refine ⟨(μ, c), ⟨⟨hμ, measure_singular_of_inner hc hs he⟩, hc, he⟩, ?_⟩
  rintro ⟨ν, d⟩ ⟨hν, hd, hde⟩
  let := hν.1
  have hp := positive_parameters_unique hd hc (fun _ hz => (hde hz).symm.trans (he hz))
  exact Prod.ext hp.1 hp.2

theorem singular_converse : Spec.SingularConverse := by
  intro μ hμ c hc
  let := hμ.1
  obtain ⟨s, hn, he, _⟩ := singularFactor_hardy μ hc
  exact ⟨s, inner_of_measure_singular hμ.2 hc he, hn, he⟩

/-- Division means the analytic extension across all zeros, supplied by the
canonical Blaschke theorem; no pointwise division by zero occurs. -/
theorem inner_representation : Spec.InnerRepresentation := by
  intro i hi
  obtain ⟨s, hs, hn, hprod, _⟩ := BlaschkeProducts.zero_free_quotient i hi
  obtain ⟨⟨μ, c⟩, ⟨hμ, hc, he⟩, _⟩ := zero_free_representation s hs hn
  refine ⟨μ, c, hμ, hc, ?_⟩
  intro z hz
  rw [hprod z hz, he hz]

/-- The canonical Blaschke multiplier is an isometry, so it can be cancelled
as an operator even when the point of evaluation is a zero. -/
theorem inner_measure_uniqueness : Spec.InnerMeasureUniqueness := by
  intro i hi μ ν c d hμ hν hc hd hprodμ hprodν
  let := hμ.1
  let := hν.1
  obtain ⟨s, _, hs, _⟩ := singularFactor_hardy μ hc
  obtain ⟨t, _, ht, _⟩ := singularFactor_hardy ν hd
  obtain ⟨b, hb, hbe⟩ := BlaschkeProducts.canonical_inner i hi
  have hbs : Beurling.innerMul b hb s = i := by
    apply HardyDisk.evaluation_injective
    intro z hz
    calc
      eval (Beurling.innerMul b hb s) z = eval b z * eval s z :=
        Beurling.innerMul_evaluation b hb s z hz
      _ = BlaschkeProducts.canonicalProduct i z * singularFactor μ c z := by
        rw [hbe hz, hs hz]
      _ = eval i z := (hprodμ z hz).symm
  have hbt : Beurling.innerMul b hb t = i := by
    apply HardyDisk.evaluation_injective
    intro z hz
    calc
      eval (Beurling.innerMul b hb t) z = eval b z * eval t z :=
        Beurling.innerMul_evaluation b hb t z hz
      _ = BlaschkeProducts.canonicalProduct i z * singularFactor ν d z := by
        rw [hbe hz, ht hz]
      _ = eval i z := (hprodν z hz).symm
  have hst : s = t := (Beurling.innerMul b hb).injective (hbs.trans hbt.symm)
  apply positive_parameters_unique hc hd
  intro z hz
  rw [← hs hz, ← ht hz, hst]

end ExpandedFA.PartIV.HardyFactorization
