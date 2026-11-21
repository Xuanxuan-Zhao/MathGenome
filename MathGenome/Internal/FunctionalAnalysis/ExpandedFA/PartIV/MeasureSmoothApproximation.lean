import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.MeasureSmoothApproximation
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.MeasureAtomicApproximation
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp

noncomputable section

namespace ExpandedFA.PartIV.MeasureSmoothApproximation

open Set MeasureTheory Filter
open scoped Topology ZeroAtInfty
open ExpandedFA.FunctionSpaces.ScalarRieszMarkovSpec
open ExpandedFA.PartIV.MeasureSmoothApproximationSpec

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

/-- Taking the measure of an `L¹` density is well defined on a.e. classes and
is scalar-linear for both scalar fields. -/
def densityLinear {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (𝕜 : Type*) [RCLike 𝕜] : Lp 𝕜 1 μ →ₗ[𝕜] VectorMeasure X 𝕜 where
  toFun u := μ.withDensityᵥ u
  map_add' u v := by
    exact (WithDensityᵥEq.congr_ae (Lp.coeFn_add u v)).trans
      (withDensityᵥ_add (L1.integrable_coeFn u) (L1.integrable_coeFn v))
  map_smul' c u := by
    exact (WithDensityᵥEq.congr_ae (Lp.coeFn_smul c u)).trans (withDensityᵥ_smul u c)

/-- No positive-dimensional hypothesis is used in the full variation formula. -/
theorem variation_density {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {𝕜 : Type*} [RCLike 𝕜] (u : X → 𝕜) (hu : Integrable u μ) :
    (μ.withDensityᵥ u).variation = μ.withDensity (fun x => ‖u x‖ₑ) :=
  Measure.variation_withDensityᵥ hu

theorem density_finite {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {𝕜 : Type*} [RCLike 𝕜] (u : X → 𝕜) (hu : Integrable u μ) :
    IsFiniteMeasure (μ.withDensityᵥ u).variation := by
  constructor
  rw [variation_density μ u hu, withDensity_apply _ MeasurableSet.univ]
  simpa only [setLIntegral_univ] using hasFiniteIntegral_iff_enorm.mp hu.hasFiniteIntegral

theorem integrable_simple_mul {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {𝕜 : Type*} [RCLike 𝕜] {u : X → 𝕜} (hu : Integrable u μ)
    (g : SimpleFunc X 𝕜) : Integrable (fun x => g x * u x) μ := by
  obtain ⟨C, hC⟩ := g.exists_forall_norm_le
  exact hu.bdd_mul g.aestronglyMeasurable (Eventually.of_forall hC)

/-- The native scalar vector-measure integral agrees with the ordinary product
integral for simple tests. -/
theorem scalarIntegral_density_simple {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {𝕜 : Type*} [RCLike 𝕜] (u : X → 𝕜) (hu : Integrable u μ)
    (g : SimpleFunc X 𝕜) :
    scalarIntegral (μ.withDensityᵥ u) g = ∫ x, g x * u x ∂μ := by
  have : IsFiniteMeasure (μ.withDensityᵥ u).variation := density_finite μ u hu
  induction g using SimpleFunc.induction with
  | @const c s hs =>
    change scalarIntegral (μ.withDensityᵥ u) (s.indicator (fun _ => c)) = _
    rw [scalarIntegral, VectorMeasure.integral_indicator_const _ hs,
      ContinuousLinearMap.mul_apply', withDensityᵥ_apply hu hs]
    rw [← integral_const_mul]
    simp_rw [SimpleFunc.piecewise_apply, SimpleFunc.const_apply]
    rw [← integral_indicator hs]
    congr 1
    ext x
    by_cases hx : x ∈ s <;> simp [hx]
  | @add f g hdisj hf hg =>
    have hfint := f.integrable_of_isFiniteMeasure (μ := (μ.withDensityᵥ u).variation)
    have hgint := g.integrable_of_isFiniteMeasure (μ := (μ.withDensityᵥ u).variation)
    change scalarIntegral (μ.withDensityᵥ u) (f + g) = _
    rw [scalarIntegral, VectorMeasure.integral_add hfint hgint]
    change scalarIntegral (μ.withDensityᵥ u) f + scalarIntegral (μ.withDensityᵥ u) g = _
    rw [hf, hg, ← integral_add (integrable_simple_mul hu f) (integrable_simple_mul hu g)]
    congr 1
    ext x
    simp [add_mul]

/-- The multiplication pairing for `u dx` is the ordinary Bochner integral,
with no conjugation. Bounded measurable tests suffice. -/
theorem scalarIntegral_density_of_bounded {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {𝕜 : Type*} [RCLike 𝕜] (u f : X → 𝕜)
    (hu : Integrable u μ) (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) :
    scalarIntegral (μ.withDensityᵥ u) f = ∫ x, f x * u x ∂μ := by
  have : IsFiniteMeasure (μ.withDensityᵥ u).variation := density_finite μ u hu
  let g n := SimpleFunc.approxOn f hf univ 0 (mem_univ _) n
  have hg n x : ‖g n x‖ ≤ 2 * C := by
    calc
      ‖g n x‖ ≤ ‖f x‖ + ‖f x‖ := SimpleFunc.norm_approxOn_zero_le hf (mem_univ _) x n
      _ ≤ 2 * C := by linarith [hC x]
  have hlim x : Tendsto (fun n => g n x) atTop (𝓝 (f x)) :=
    SimpleFunc.tendsto_approxOn hf (mem_univ _) (by simp)
  have hleft : Tendsto (fun n => scalarIntegral (μ.withDensityᵥ u) (g n)) atTop
      (𝓝 (scalarIntegral (μ.withDensityᵥ u) f)) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => 2 * C)
      (fun n => (g n).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall (hg n)) (Eventually.of_forall hlim)
  have hright : Tendsto (fun n => ∫ x, g n x * u x ∂μ) atTop
      (𝓝 (∫ x, f x * u x ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => 2 * C * ‖u x‖)
    · intro n
      exact (g n).aestronglyMeasurable.mul hu.aestronglyMeasurable
    · exact hu.norm.const_mul _
    · intro n
      exact Eventually.of_forall fun x => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hg n x) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (hlim x).mul tendsto_const_nhds
  simp_rw [scalarIntegral_density_simple μ u hu] at hleft
  exact tendsto_nhds_unique hleft hright

theorem densityLinear_variation_mass {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {𝕜 : Type*} [RCLike 𝕜] (u : Lp 𝕜 1 μ) :
    (densityLinear μ 𝕜 u).variation.real univ = ‖u‖ := by
  rw [Measure.real, densityLinear, LinearMap.coe_mk, AddHom.coe_mk,
    variation_density μ u (L1.integrable_coeFn u),
    withDensity_apply _ MeasurableSet.univ]
  simpa using (L1.norm_def u).symm

theorem intoClosure_measurableEmbedding {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) : MeasurableEmbedding (intoClosure Ω) := by
  exact ⟨Set.inclusion_injective subset_closure, measurable_inclusion subset_closure,
    fun _ hs => MeasurableSet.image_inclusion subset_closure hΩ.measurableSet hs⟩

/-- Extension by zero preserves the complete variation measure, not just an
upper bound for its total mass. -/
theorem variation_closureDensity {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) {𝕜 : Type*} [RCLike 𝕜] (u : Ω → 𝕜)
    (hu : Integrable u) :
    (closureDensity Ω u).variation =
      ((volume : Measure Ω).withDensity (fun x => ‖u x‖ₑ)).map (intoClosure Ω) := by
  rw [closureDensity, (intoClosure_measurableEmbedding hΩ).variation_map,
    openDensity, variation_density volume u hu]

theorem closureDensity_mass {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) {𝕜 : Type*} [RCLike 𝕜] (u : Ω → 𝕜) (hu : Integrable u) :
    (closureDensity Ω u).variation.real univ = ∫ x, ‖u x‖ := by
  rw [Measure.real, variation_closureDensity hΩ u hu,
    Measure.map_apply (intoClosure_measurableEmbedding hΩ).measurable MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ]
  simpa only [setLIntegral_univ] using
    (integral_norm_eq_lintegral_enorm hu.aestronglyMeasurable).symm

/-- Integration against the closure measure is exactly the expected product
pairing on the open set. -/
theorem scalarIntegral_closureDensity {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) [CompactSpace (closure Ω)] {𝕜 : Type*} [RCLike 𝕜]
    (u : Ω → 𝕜) (hu : Integrable u) (f : C(closure Ω, 𝕜)) :
    scalarIntegral (closureDensity Ω u) f =
      ∫ x : Ω, f (intoClosure Ω x) * u x := by
  unfold closureDensity scalarIntegral
  rw [(intoClosure_measurableEmbedding hΩ).integral_map_vectorMeasure]
  apply scalarIntegral_density_of_bounded volume u _ hu
    (f.continuous.measurable.comp (intoClosure_measurableEmbedding hΩ).measurable) ‖f‖
  exact fun x => f.norm_coe_le_norm _

/-- The actual scalar-linear map used in the isometric embedding. -/
def closureDensityLinear {d : ℕ} (Ω : Set (Euclidean d))
    (𝕜 : Type*) [RCLike 𝕜] :
    Lp 𝕜 1 (volume : Measure Ω) →ₗ[𝕜] VectorMeasure (closure Ω) 𝕜 :=
  (VectorMeasure.mapₗ (R := 𝕜) (intoClosure Ω)).comp (densityLinear volume 𝕜)

theorem closureDensityLinear_mass {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) {𝕜 : Type*} [RCLike 𝕜]
    (u : Lp 𝕜 1 (volume : Measure Ω)) :
    (closureDensityLinear Ω 𝕜 u).variation.real univ = ‖u‖ := by
  change (closureDensity Ω u).variation.real univ = ‖u‖
  rw [Measure.real, variation_closureDensity hΩ u (L1.integrable_coeFn u),
    Measure.map_apply (intoClosure_measurableEmbedding hΩ).measurable MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ]
  simpa using (L1.norm_def u).symm

theorem closureDensityLinear_injective {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) (𝕜 : Type*) [RCLike 𝕜] :
    Function.Injective (closureDensityLinear Ω 𝕜) := by
  intro u v huv
  have hz : closureDensityLinear Ω 𝕜 (u - v) = 0 := by
    rw [map_sub, huv, sub_self]
  have hn : ‖u - v‖ = 0 := by
    rw [← closureDensityLinear_mass hΩ (u - v), hz]
    simp
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

/-- Isometric embedding of both real and complex `L¹(Ω)` into the scalar
Radon measures on the closure, including empty and zero-dimensional domains. -/
theorem l1_embedding : L1Embedding := by
  intro d Ω hΩ hb 𝕜 _
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
  refine ⟨closureDensityLinear Ω 𝕜, fun _ => rfl, ?_,
    closureDensityLinear_injective hΩ 𝕜⟩
  intro u
  have : IsFiniteMeasure ((volume : Measure Ω).withDensityᵥ u).variation :=
    density_finite volume u (L1.integrable_coeFn u)
  have : IsFiniteMeasure (closureDensityLinear Ω 𝕜 u).variation := by
    change IsFiniteMeasure (((volume : Measure Ω).withDensityᵥ u).map (intoClosure Ω)).variation
    infer_instance
  exact ⟨MeasureAtomicApproximation.finiteScalarRadon_of_finite _,
    closureDensityLinear_mass hΩ u⟩

theorem smoothDensity_integrable {d : ℕ} {Ω : Set (Euclidean d)}
    {𝕜 : Type*} [RCLike 𝕜] (u : SmoothDensity Ω 𝕜) (hΩ : IsOpen Ω) :
    Integrable (fun x : Ω => u x) := by
  exact (integrableOn_iff_comap_subtypeVal hΩ.measurableSet).mp
    (u.smooth.continuous.integrable_of_hasCompactSupport u.compact).integrableOn

def zeroDensity {d : ℕ} (Ω : Set (Euclidean d)) (𝕜 : Type*) [RCLike 𝕜] :
    SmoothDensity Ω 𝕜 where
  toFun := 0
  smooth := contDiff_const
  compact := HasCompactSupport.zero
  support_subset := by simp

def scaleDensity {d : ℕ} {Ω : Set (Euclidean d)} {𝕜 : Type*} [RCLike 𝕜]
    (c : ℝ) (u : SmoothDensity Ω 𝕜) : SmoothDensity Ω 𝕜 where
  toFun x := c • u x
  smooth := ContDiff.const_smul c u.smooth
  compact := u.compact.smul_left (f := fun _ => c)
  support_subset := (tsupport_smul_subset_right (fun _ => c) u).trans u.support_subset

@[simp] theorem closureDensity_zero {d : ℕ} (Ω : Set (Euclidean d))
    (𝕜 : Type*) [RCLike 𝕜] :
    closureDensity Ω (fun x => zeroDensity Ω 𝕜 x) = 0 := by
  change ((volume : Measure Ω).withDensityᵥ (0 : Ω → 𝕜)).map (intoClosure Ω) = 0
  rw [withDensityᵥ_zero, VectorMeasure.map_zero]

@[simp] theorem closureDensity_scale {d : ℕ} (Ω : Set (Euclidean d))
    {𝕜 : Type*} [RCLike 𝕜] (c : ℝ) (u : SmoothDensity Ω 𝕜) :
    closureDensity Ω (fun x => scaleDensity c u x) =
      c • closureDensity Ω (fun x => u x) := by
  exact congrArg (fun ν : VectorMeasure Ω 𝕜 => ν.map (intoClosure Ω))
    (withDensityᵥ_smul' (μ := (volume : Measure Ω)) (fun x : Ω => u x) c)
      |>.trans (VectorMeasure.map_smul c)

theorem finiteScalarRadon_closureDensity {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {𝕜 : Type*} [RCLike 𝕜]
    (u : SmoothDensity Ω 𝕜) :
    FiniteScalarRadon (closureDensity Ω (fun x => u x)) := by
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
  have : IsFiniteMeasure ((volume : Measure Ω).withDensityᵥ (fun x : Ω => u x)).variation :=
    density_finite volume _ (smoothDensity_integrable u hΩ)
  change FiniteScalarRadon (((volume : Measure Ω).withDensityᵥ (fun x : Ω => u x)).map (intoClosure Ω))
  exact MeasureAtomicApproximation.finiteScalarRadon_of_finite _

/-- Exact normalization for any contractive smooth weak-star approximation.
The finite initial segment is discarded only when the target norm is positive;
zero target measures use the constant zero sequence. -/
theorem normalize_smooth_approximation {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) {𝕜 : Type} [RCLike 𝕜]
    (μ : VectorMeasure (closure Ω) 𝕜) (hμ : FiniteScalarRadon μ)
    (u : ℕ → SmoothDensity Ω 𝕜)
    (hle : ∀ n, (∫ x : Ω, ‖u n x‖) ≤ μ.variation.real univ)
    (hconv : ∀ f : C(closure Ω, 𝕜),
      Tendsto (fun n => scalarIntegral (closureDensity Ω (fun x => u n x)) f)
        atTop (𝓝 (scalarIntegral μ f))) :
    ∃ v : ℕ → SmoothDensity Ω 𝕜,
      (∀ n, Integrable (fun x : Ω => v n x) ∧
        FiniteScalarRadon (closureDensity Ω (fun x => v n x)) ∧
        (∫ x : Ω, ‖v n x‖) = μ.variation.real univ) ∧
      ∀ f : C(closure Ω, 𝕜),
        Tendsto (fun n => scalarIntegral (closureDensity Ω (fun x => v n x)) f)
          atTop (𝓝 (scalarIntegral μ f)) := by
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
  have : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  by_cases hzero : μ.variation.real univ = 0
  · have hv : μ.variation = 0 := Measure.measure_univ_eq_zero.mp (by
      have h := congrArg ENNReal.ofReal hzero
      simpa only [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _),
        ENNReal.ofReal_zero] using h)
    have hμzero : μ = 0 := VectorMeasure.variation_eq_zero.mp hv
    refine ⟨fun _ => zeroDensity Ω 𝕜, ?_, ?_⟩
    · intro n
      refine ⟨smoothDensity_integrable (zeroDensity Ω 𝕜) hΩ,
        finiteScalarRadon_closureDensity hΩ hb _, ?_⟩
      simp [zeroDensity, hzero]
    · intro f
      simp [hμzero, scalarIntegral]
  · have hpos : 0 < μ.variation.real univ :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hzero)
    let ν n := closureDensity Ω (fun x => u n x)
    have hν n : FiniteScalarRadon (ν n) := finiteScalarRadon_closureDensity hΩ hb (u n)
    have hm n : (ν n).variation.real univ = ∫ x : Ω, ‖u n x‖ :=
      closureDensity_mass hΩ _ (smoothDensity_integrable (u n) hΩ)
    have hmass := MeasureAtomicApproximation.variation_mass_tendsto μ ν hν
      (fun n => (hm n).trans_le (hle n)) hconv
    obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 hmass).1 0 hpos)
    let c n := μ.variation.real univ / (ν (n + N)).variation.real univ
    have hνpos n : 0 < (ν (n + N)).variation.real univ :=
      hN (n + N) (Nat.le_add_left N n)
    have hc n : 0 ≤ c n := (div_pos hpos (hνpos n)).le
    refine ⟨fun n => scaleDensity (c n) (u (n + N)), ?_, ?_⟩
    · intro n
      refine ⟨smoothDensity_integrable (scaleDensity _ _) hΩ,
        finiteScalarRadon_closureDensity hΩ hb _, ?_⟩
      calc
        (∫ x : Ω, ‖scaleDensity (c n) (u (n + N)) x‖) =
            c n * ∫ x : Ω, ‖u (n + N) x‖ := by
          change (∫ x : Ω, ‖c n • u (n + N) x‖) = _
          simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc n)]
          exact integral_const_mul _ _
        _ = μ.variation.real univ := by
          rw [← hm]
          exact div_mul_cancel₀ _ (hνpos n).ne'
    · intro f
      have hscale : Tendsto c atTop (𝓝 1) := by
        have h : Tendsto
            (fun n => μ.variation.real univ / (ν (n + N)).variation.real univ)
            atTop (𝓝 (μ.variation.real univ / μ.variation.real univ)) :=
          tendsto_const_nhds.div (hmass.comp (tendsto_add_atTop_nat N)) hzero
        simpa only [div_self hzero] using h
      have hpair := (hconv f).comp (tendsto_add_atTop_nat N)
      have h := hscale.smul hpair
      simpa only [closureDensity_scale, scalarIntegral,
        VectorMeasure.integral_smul_vectorMeasure, one_smul,
        Function.comp_apply] using h

/-- A nonnegative integral-one smooth density can be placed arbitrarily near
any point of the closure. Its entire closed support lies in the open set.
The construction also works in dimension zero. -/
theorem exists_local_probability_bump {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) (a : closure Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : SmoothDensity Ω ℝ,
      (∀ x, 0 ≤ u x) ∧ (∫ x : Ω, u x) = 1 ∧
      tsupport (u : Euclidean d → ℝ) ⊆ Metric.ball (a : Euclidean d) ε := by
  obtain ⟨b, hbΩ, hbε⟩ := Metric.mem_closure_iff.mp a.property ε hε
  have hnb : Ω ∩ Metric.ball (a : Euclidean d) ε ∈ 𝓝 b :=
    (hΩ.inter Metric.isOpen_ball).mem_nhds ⟨hbΩ, by simpa [dist_comm] using hbε⟩
  obtain ⟨r, hr, hrs⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnb
  let φ : ContDiffBump b :=
    { rIn := r / 2
      rOut := r
      rIn_pos := half_pos hr
      rIn_lt_rOut := half_lt_self hr }
  let u : SmoothDensity Ω ℝ :=
    { toFun := φ.normed volume
      smooth := φ.contDiff_normed
      compact := φ.hasCompactSupport_normed
      support_subset := by
        rw [φ.tsupport_normed_eq]
        exact hrs.trans inter_subset_left }
  refine ⟨u, φ.nonneg_normed, ?_, ?_⟩
  · rw [integral_subtype hΩ.measurableSet]
    calc
      (∫ x in Ω, u x) = ∫ x, u x := by
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro x hx
        exact image_eq_zero_of_notMem_tsupport (fun h => hx (u.support_subset h))
      _ = 1 := φ.integral_normed
  · change tsupport (φ.normed volume) ⊆ Metric.ball (a : Euclidean d) ε
    rw [φ.tsupport_normed_eq]
    exact hrs.trans inter_subset_right

/-- A probability bump averages a continuous test with error bounded by its
oscillation on the bump's support. -/
theorem probability_bump_error {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) [CompactSpace (closure Ω)] {𝕜 : Type*} [RCLike 𝕜]
    (a : closure Ω) (u : SmoothDensity Ω ℝ) (hnonneg : ∀ x, 0 ≤ u x)
    (hmass : (∫ x : Ω, u x) = 1) (f : C(closure Ω, 𝕜)) (η : ℝ)
    (hosc : ∀ x : Ω, (x : Euclidean d) ∈ tsupport (u : Euclidean d → ℝ) →
      ‖f (intoClosure Ω x) - f a‖ ≤ η) :
    ‖(∫ x : Ω, u x • f (intoClosure Ω x)) - f a‖ ≤ η := by
  have hu := smoothDensity_integrable u hΩ
  have hcont : Continuous (fun x : Ω => f (intoClosure Ω x)) :=
    f.continuous.comp (continuous_inclusion subset_closure)
  have hi : Integrable (fun x : Ω => u x • f (intoClosure Ω x)) :=
    hu.smul_bdd ‖f‖ hcont.aestronglyMeasurable
      (Eventually.of_forall fun x => f.norm_coe_le_norm _)
  have hc := hu.smul_const (f a)
  have hid : (∫ x : Ω, u x • (f (intoClosure Ω x) - f a)) =
      (∫ x : Ω, u x • f (intoClosure Ω x)) - f a := by
    simp_rw [smul_sub]
    rw [integral_sub hi hc, integral_smul_const, hmass, one_smul]
  rw [← hid]
  calc
    ‖∫ x : Ω, u x • (f (intoClosure Ω x) - f a)‖ ≤ ∫ x : Ω, η * u x := by
      apply norm_integral_le_of_norm_le (hu.const_mul η)
      apply Eventually.of_forall
      intro x
      by_cases hx : (x : Euclidean d) ∈ tsupport (u : Euclidean d → ℝ)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnonneg x), mul_comm η]
        exact mul_le_mul_of_nonneg_left (hosc x hx) (hnonneg x)
      · have hz : u x = 0 := image_eq_zero_of_notMem_tsupport hx
        simp [hz]
    _ = η := by rw [integral_const_mul, hmass, mul_one]

/-- Every point of the closure is a sequential weak-star limit of nonnegative
integral-one smooth densities supported in the open set. -/
theorem smooth_probability_dirac_approximation {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (a : closure Ω) :
    ∃ u : ℕ → SmoothDensity Ω ℝ,
      (∀ n, (∀ x, 0 ≤ u n x) ∧ (∫ x : Ω, u n x) = 1) ∧
      ∀ (𝕜 : Type) [RCLike 𝕜] (f : C(closure Ω, 𝕜)),
        Tendsto (fun n => ∫ x : Ω, u n x • f (intoClosure Ω x))
          atTop (𝓝 (f a)) := by
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
  have hε (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose u hnonneg hmass hsupp using
    fun n => exists_local_probability_bump hΩ a (hε n)
  refine ⟨u, fun n => ⟨hnonneg n, hmass n⟩, ?_⟩
  intro 𝕜 _ f
  apply Metric.tendsto_atTop.mpr
  intro ε hε'
  obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp f.continuous.continuousAt
    (ε / 2) (half_pos hε')
  have hrad : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hrad).2 δ hδ)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  apply lt_of_le_of_lt (probability_bump_error hΩ a (u n) (hnonneg n) (hmass n) f (ε / 2) ?_)
    (half_lt_self hε')
  intro x hx
  have hx' : dist (intoClosure Ω x) a < δ :=
    (hsupp n hx).trans (hN n hn)
  simpa only [dist_eq_norm] using (hfδ hx').le

def sumDensity {d : ℕ} {Ω : Set (Euclidean d)} {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} (s : Finset ι) (φ : ι → SmoothDensity Ω ℝ) (c : ι → 𝕜) :
    SmoothDensity Ω 𝕜 where
  toFun x := ∑ a ∈ s, φ a x • c a
  smooth := ContDiff.sum fun a _ => (φ a).smooth.smul_const (c a)
  compact := by
    have h := HasCompactSupport.finset_sum
      (s := s) (f := fun a x => φ a x • c a)
      (fun a _ => (φ a).compact.smul_right (f' := fun _ => c a))
    convert h using 1
    ext x
    simp only [Finset.sum_apply]
  support_subset := by
    classical
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
      simp_rw [Finset.sum_insert ha]
      exact (tsupport_add _ _).trans (union_subset
        ((tsupport_smul_subset_left (φ a) (fun _ => c a)).trans (φ a).support_subset) ih)

theorem sumDensity_l1_le {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) {𝕜 : Type*} [RCLike 𝕜] {ι : Type*}
    (s : Finset ι) (φ : ι → SmoothDensity Ω ℝ) (c : ι → 𝕜)
    (hnonneg : ∀ a ∈ s, ∀ x, 0 ≤ φ a x)
    (hmass : ∀ a ∈ s, (∫ x : Ω, φ a x) = 1) :
    (∫ x : Ω, ‖sumDensity s φ c x‖) ≤ ∑ a ∈ s, ‖c a‖ := by
  have hi a : Integrable (fun x : Ω => ‖φ a x • c a‖) :=
    ((smoothDensity_integrable (φ a) hΩ).smul_const (c a)).norm
  calc
    (∫ x : Ω, ‖sumDensity s φ c x‖) ≤ ∫ x : Ω, ∑ a ∈ s, ‖φ a x • c a‖ := by
      apply integral_mono (smoothDensity_integrable (sumDensity s φ c) hΩ).norm
        (integrable_finsetSum s fun a _ => hi a)
      exact fun x => norm_sum_le _ _
    _ = ∑ a ∈ s, ∫ x : Ω, ‖φ a x • c a‖ := integral_finsetSum _ (fun a _ => hi a)
    _ = ∑ a ∈ s, ‖c a‖ := by
      apply Finset.sum_congr rfl
      intro a ha
      simp_rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnonneg a ha _)]
      rw [integral_mul_const, hmass a ha, one_mul]

theorem scalarIntegral_partition {K 𝕜 : Type*} [MeasurableSpace K] [RCLike 𝕜]
    (μ : VectorMeasure K 𝕜) [IsFiniteMeasure μ.variation]
    (q : SimpleFunc K K) (f : K → 𝕜) :
    scalarIntegral μ (fun x => f (q x)) =
      ∑ a ∈ q.range, f a * μ (q ⁻¹' {a}) := by
  classical
  have he : (fun x => f (q x)) = fun x =>
      ∑ a ∈ q.range, (q ⁻¹' {a}).indicator (fun _ => f a) x := by
    ext x
    simp [Set.indicator_apply, eq_comm]
  rw [he, scalarIntegral, VectorMeasure.integral_finsetSum _ (fun a _ =>
    (integrable_const (f a)).indicator (q.measurableSet_fiber a))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [VectorMeasure.integral_indicator_const _ (q.measurableSet_fiber a)]
  rfl

theorem partition_mass_bound {K 𝕜 : Type*} [MeasurableSpace K] [RCLike 𝕜]
    (μ : VectorMeasure K 𝕜) [IsFiniteMeasure μ.variation] (q : SimpleFunc K K) :
    (∑ a ∈ q.range, ‖μ (q ⁻¹' {a})‖) ≤ μ.variation.real univ := by
  calc
    _ ≤ ∑ a ∈ q.range, μ.variation.real (q ⁻¹' {a}) :=
      Finset.sum_le_sum fun a _ => VectorMeasure.norm_measure_le_variation
    _ = μ.variation.real univ := by
      unfold Measure.real
      rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top _ _),
        q.sum_range_measure_preimage_singleton]

theorem sumDensity_pairing {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) [CompactSpace (closure Ω)] {𝕜 : Type*} [RCLike 𝕜]
    {ι : Type*} (s : Finset ι) (φ : ι → SmoothDensity Ω ℝ) (c : ι → 𝕜)
    (f : C(closure Ω, 𝕜)) :
    scalarIntegral (closureDensity Ω (fun x => sumDensity s φ c x)) f =
      ∑ a ∈ s, (∫ x : Ω, φ a x • f (intoClosure Ω x)) * c a := by
  rw [scalarIntegral_closureDensity hΩ _ (smoothDensity_integrable (sumDensity s φ c) hΩ)]
  simp_rw [sumDensity, Finset.mul_sum]
  have hi a : Integrable (fun x : Ω => φ a x • f (intoClosure Ω x)) :=
    (smoothDensity_integrable (φ a) hΩ).smul_bdd ‖f‖
      (f.continuous.comp (continuous_inclusion subset_closure)).aestronglyMeasurable
      (Eventually.of_forall fun x => f.norm_coe_le_norm _)
  have he a x : f (intoClosure Ω x) * (φ a x • c a) =
      (φ a x • f (intoClosure Ω x)) * c a := by
    rw [mul_smul_comm, smul_mul_assoc]
  simp_rw [he]
  rw [integral_finsetSum _ (fun a _ => (hi a).mul_const (c a))]
  apply Finset.sum_congr rfl
  intro a ha
  exact integral_mul_const _ _

theorem sumDensity_error {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) [CompactSpace (closure Ω)] {𝕜 : Type*} [RCLike 𝕜]
    (μ : VectorMeasure (closure Ω) 𝕜) [IsFiniteMeasure μ.variation]
    (q : SimpleFunc (closure Ω) (closure Ω)) (φ : closure Ω → SmoothDensity Ω ℝ)
    (hnonneg : ∀ a, ∀ x, 0 ≤ φ a x) (hmass : ∀ a, (∫ x : Ω, φ a x) = 1)
    (f : C(closure Ω, 𝕜)) {η : ℝ} (hη : 0 ≤ η)
    (hosc : ∀ a ∈ q.range, ∀ x : Ω,
      (x : Euclidean d) ∈ tsupport (φ a : Euclidean d → ℝ) →
      ‖f (intoClosure Ω x) - f a‖ ≤ η) :
    ‖scalarIntegral (closureDensity Ω (fun x =>
        sumDensity q.range φ (fun a => μ (q ⁻¹' {a})) x)) f -
      scalarIntegral μ (fun x => f (q x))‖ ≤ η * μ.variation.real univ := by
  rw [sumDensity_pairing hΩ, scalarIntegral_partition, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a ∈ q.range,
        ‖(∫ x : Ω, φ a x • f (intoClosure Ω x)) - f a‖ * ‖μ (q ⁻¹' {a})‖ := by
      simp_rw [← sub_mul, ← norm_mul]
      exact norm_sum_le _ _
    _ ≤ ∑ a ∈ q.range, η * ‖μ (q ⁻¹' {a})‖ := by
      apply Finset.sum_le_sum
      intro a ha
      exact mul_le_mul_of_nonneg_right
        (probability_bump_error hΩ a (φ a) (hnonneg a) (hmass a) f η (hosc a ha))
        (norm_nonneg _)
    _ = η * ∑ a ∈ q.range, ‖μ (q ⁻¹' {a})‖ := (Finset.mul_sum _ _ _).symm
    _ ≤ η * μ.variation.real univ :=
      mul_le_mul_of_nonneg_left (partition_mass_bound μ q) hη

/-- Smoothing a finite quantization preserves its weak-star limit. The bump
radius is independent of the continuous test. -/
theorem quantized_smooth_tendsto {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) [CompactSpace (closure Ω)] {𝕜 : Type*} [RCLike 𝕜]
    (μ : VectorMeasure (closure Ω) 𝕜) [IsFiniteMeasure μ.variation]
    (q : ℕ → SimpleFunc (closure Ω) (closure Ω))
    (hq : ∀ x, Tendsto (fun n => q n x) atTop (𝓝 x))
    (φ : ℕ → closure Ω → SmoothDensity Ω ℝ)
    (hnonneg : ∀ n a x, 0 ≤ φ n a x)
    (hmass : ∀ n a, (∫ x : Ω, φ n a x) = 1)
    (hsupp : ∀ n a, tsupport (φ n a : Euclidean d → ℝ) ⊆
      Metric.ball (a : Euclidean d) (1 / ((n : ℝ) + 1))) :
    ∀ f : C(closure Ω, 𝕜), Tendsto (fun n => scalarIntegral
      (closureDensity Ω (fun x => sumDensity (q n).range (φ n)
        (fun a => μ (q n ⁻¹' {a})) x)) f) atTop (𝓝 (scalarIntegral μ f)) := by
  let u n := sumDensity (q n).range (φ n) (fun a => μ (q n ⁻¹' {a}))
  intro f
  have hquant : Tendsto (fun n => scalarIntegral μ (fun x => f (q n x))) atTop
      (𝓝 (scalarIntegral μ f)) :=
    VectorMeasure.tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
      (fun n => (f.continuous.measurable.comp (q n).measurable).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun x => f.norm_coe_le_norm _)
      (Eventually.of_forall fun x => (f.continuous.tendsto x).comp (hq x))
  have herr : Tendsto (fun n =>
      scalarIntegral (closureDensity Ω (fun x => u n x)) f -
        scalarIntegral μ (fun x => f (q n x))) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε'
    let η := ε / (μ.variation.real univ + 1)
    have hM : 0 ≤ μ.variation.real univ := ENNReal.toReal_nonneg
    have hden : 0 < μ.variation.real univ + 1 := by positivity
    have hη : 0 < η := div_pos hε' hden
    obtain ⟨δ, hδ, hfδ⟩ := f.uniform_continuity η hη
    have hrad : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_order.mp hrad).2 δ hδ)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_zero_right]
    apply lt_of_le_of_lt (sumDensity_error hΩ μ (q n) (φ n)
      (hnonneg n) (hmass n) f hη.le ?_) ?_
    · intro a ha x hx
      have hx' : dist (intoClosure Ω x) a < δ :=
        (hsupp n a hx).trans (hN n hn)
      simpa only [dist_eq_norm] using (hfδ hx').le
    · dsimp [η]
      rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
      nlinarith
  have h := herr.add hquant
  simpa only [sub_add_cancel, zero_add] using h

/-- The scalar closure approximation is obtained from finite quantization,
positive probability bumps, and exact normalization. No disjoint-support or
point-mass singularity assertion is needed. -/
theorem closure_approximation : ClosureApproximation := by
  intro d Ω hΩ hb 𝕜 _ μ hμ
  classical
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
  have : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  obtain ⟨q, hq⟩ :=
    (stronglyMeasurable_id : StronglyMeasurable (id : closure Ω → closure Ω))
  have hε (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose φ hnonneg hmass hsupp using
    fun n (a : closure Ω) => exists_local_probability_bump hΩ a (hε n)
  let u n := sumDensity (q n).range (φ n) (fun a => μ (q n ⁻¹' {a}))
  apply normalize_smooth_approximation hΩ hb μ hμ u
  · intro n
    exact (sumDensity_l1_le hΩ _ _ _ (fun a _ => hnonneg n a)
      (fun a _ => hmass n a)).trans (partition_mass_bound μ (q n))
  · exact quantized_smooth_tendsto hΩ μ q hq φ hnonneg hmass hsupp

/-- Positive measures use positive cell masses, so no normalization is needed:
the smooth densities already have exactly the required mass. -/
theorem positive_closure_approximation : PositiveClosureApproximation := by
  intro d Ω hΩ hb μ hfin hradon
  classical
  have : IsFiniteMeasure μ := hfin
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
  obtain ⟨q, hq⟩ :=
    (stronglyMeasurable_id : StronglyMeasurable (id : closure Ω → closure Ω))
  have hε (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
  choose φ hnonneg hmass hsupp using
    fun n (a : closure Ω) => exists_local_probability_bump hΩ a (hε n)
  let u n := sumDensity (q n).range (φ n) (fun a => μ.real (q n ⁻¹' {a}))
  have hunonneg n x : 0 ≤ u n x := by
    exact Finset.sum_nonneg fun a ha => mul_nonneg (hnonneg n a x) ENNReal.toReal_nonneg
  refine ⟨u, ?_, ?_⟩
  · intro n
    refine ⟨smoothDensity_integrable (u n) hΩ, hunonneg n, ?_⟩
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (hunonneg n _)]
    change (∫ x : Ω, ∑ a ∈ (q n).range, φ n a x * μ.real (q n ⁻¹' {a})) = _
    rw [integral_finsetSum _ (fun a _ =>
      (smoothDensity_integrable (φ n a) hΩ).mul_const _)]
    simp_rw [integral_mul_const, hmass, one_mul]
    unfold Measure.real
    rw [← ENNReal.toReal_sum (fun a _ => measure_ne_top _ _),
      (q n).sum_range_measure_preimage_singleton]
  · intro 𝕜 _ f
    let ν : VectorMeasure (closure Ω) 𝕜 := μ.withDensityᵥ (fun _ => 1)
    have : IsFiniteMeasure ν.variation := density_finite μ _ (integrable_const _)
    have hνcell n a : ν (q n ⁻¹' {a}) = (μ.real (q n ⁻¹' {a}) : 𝕜) := by
      rw [withDensityᵥ_apply (integrable_const _) ((q n).measurableSet_fiber a),
        integral_const]
      simp [Algebra.smul_def]
    have huCast n : (fun x : Ω => (u n x : 𝕜)) =
        fun x : Ω => sumDensity (q n).range (φ n) (fun a => ν (q n ⁻¹' {a})) x := by
      ext x
      simp [u, sumDensity, hνcell, Algebra.smul_def]
    have hp n : scalarIntegral (closureDensity Ω (fun x : Ω => (u n x : 𝕜))) f =
        ∫ x : Ω, (u n x : 𝕜) * f (intoClosure Ω x) := by
      have hui : Integrable (fun x : Ω => (u n x : 𝕜)) := by
        exact (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).integrable_comp
          (smoothDensity_integrable (u n) hΩ)
      rw [scalarIntegral_closureDensity hΩ _ hui]
      simp only [mul_comm]
    have hrep : scalarIntegral ν f = ∫ x, f x ∂μ := by
      rw [scalarIntegral_density_of_bounded μ _ f (integrable_const _)
        f.continuous.measurable ‖f‖ (fun x => f.norm_coe_le_norm x)]
      simp
    have h := quantized_smooth_tendsto hΩ ν q hq φ hnonneg hmass hsupp f
    simpa only [← huCast, hp, hrep] using h

/-- A function vanishing at infinity on the open set extends continuously to
the metric closure, by uniform continuity and completeness of the scalar field. -/
theorem exists_continuous_extension {d : ℕ} (Ω : Set (Euclidean d))
    {𝕜 : Type*} [RCLike 𝕜] (f : C₀(Ω, 𝕜)) :
    ∃ F : C(closure Ω, 𝕜), ∀ x, F (intoClosure Ω x) = f x := by
  have hi : IsUniformInducing (intoClosure Ω) :=
    (show Isometry (intoClosure Ω) from fun _ _ => rfl).isUniformInducing
  have hd : DenseRange (intoClosure Ω) :=
    (denseRange_inclusion_iff subset_closure).mpr subset_rfl
  exact ⟨⟨(hi.isDenseInducing hd).extend f,
    (uniformContinuous_uniformly_extend hi hd (ZeroAtInftyContinuousMap.uniformContinuous f)).continuous⟩,
    uniformly_extend_of_ind hi hd (ZeroAtInftyContinuousMap.uniformContinuous f)⟩

theorem finiteScalarRadon_openDensity {d : ℕ} {Ω : Set (Euclidean d)}
    (hΩ : IsOpen Ω) {𝕜 : Type*} [RCLike 𝕜] (u : SmoothDensity Ω 𝕜) :
    FiniteScalarRadon (openDensity Ω (fun x => u x)) := by
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have : IsFiniteMeasure (openDensity Ω (fun x => u x)).variation :=
    density_finite volume _ (smoothDensity_integrable u hΩ)
  exact ⟨measure_lt_top _ _,
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
      inferInstance⟩

/-- Pushforward under the open inclusion preserves variation and all `C₀`
pairings, reducing the open-set assertion to the closure assertion. -/
theorem open_approximation : OpenApproximation := by
  intro d Ω hΩ hb 𝕜 _ μ hμ
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
  have : IsFiniteMeasure μ.variation := ⟨hμ.1⟩
  let ν := μ.map (intoClosure Ω)
  have hν : FiniteScalarRadon ν := MeasureAtomicApproximation.finiteScalarRadon_of_finite _
  have hmass : ν.variation.real univ = μ.variation.real univ := by
    rw [Measure.real, Measure.real, (intoClosure_measurableEmbedding hΩ).variation_map,
      Measure.map_apply (intoClosure_measurableEmbedding hΩ).measurable MeasurableSet.univ,
      preimage_univ]
  obtain ⟨u, hu, hconv⟩ := closure_approximation d Ω hΩ hb 𝕜 ν hν
  refine ⟨u, fun n => ⟨(hu n).1, finiteScalarRadon_openDensity hΩ _,
    (hu n).2.2.trans hmass⟩, ?_⟩
  intro f
  obtain ⟨F, hF⟩ := exists_continuous_extension Ω f
  have hpair (ρ : VectorMeasure Ω 𝕜) :
      scalarIntegral (ρ.map (intoClosure Ω)) F = scalarIntegral ρ f := by
    unfold scalarIntegral
    rw [(intoClosure_measurableEmbedding hΩ).integral_map_vectorMeasure]
    congr 1
    ext x
    exact hF x
  simpa only [closureDensity, hpair, ν] using hconv F

theorem positive_open_approximation : PositiveOpenApproximation := by
  intro d Ω hΩ hb μ hfin hradon
  have : IsFiniteMeasure μ := hfin
  have : CompactSpace (closure Ω) := isCompact_iff_compactSpace.mp
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hb.closure)
  let ν := μ.map (intoClosure Ω)
  have hν : ExpandedFA.FunctionSpaces.PositiveRadonRepresentationSpec.PositiveRadon ν :=
    (ExpandedFA.FunctionSpaces.PositiveRadonRepresentation.positiveRadon_iff_regular _).mpr
      inferInstance
  have hmass : ν.real univ = μ.real univ := by
    rw [Measure.real, Measure.real,
      Measure.map_apply (intoClosure_measurableEmbedding hΩ).measurable MeasurableSet.univ,
      preimage_univ]
  obtain ⟨u, hu, hconv⟩ := positive_closure_approximation d Ω hΩ hb ν inferInstance hν
  refine ⟨u, fun n => ⟨(hu n).1, (hu n).2.1, (hu n).2.2.trans hmass⟩, ?_⟩
  intro 𝕜 _ f
  obtain ⟨F, hF⟩ := exists_continuous_extension Ω f
  have hrep : (∫ x, F x ∂ν) = ∫ x, f x ∂μ := by
    rw [integral_map (intoClosure_measurableEmbedding hΩ).measurable.aemeasurable
      F.continuous.aestronglyMeasurable]
    exact integral_congr_ae (Eventually.of_forall hF)
  simpa only [hF, hrep] using hconv 𝕜 F

theorem open_dual_approximation_of_representation (𝕜 : Type) [RCLike 𝕜]
    (representation : ScalarRepresentation.{0} 𝕜) : OpenDualApproximation 𝕜 := by
  intro d Ω hΩ hb L
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  obtain ⟨μ, hμ, hrep, hnorm, _⟩ := representation (↥Ω) L
  obtain ⟨u, hu, hconv⟩ := open_approximation d Ω hΩ hb 𝕜 μ hμ
  refine ⟨u, fun n => ⟨(hu n).1, (hu n).2.2.trans hnorm.symm⟩, ?_⟩
  intro f
  have hp n : scalarIntegral (openDensity Ω (fun x => u n x)) f =
      ∫ x : Ω, f x * u n x :=
    scalarIntegral_density_of_bounded volume _ f (hu n).1 f.continuous.measurable ‖f‖
      (fun x => f.toBCF.norm_coe_le_norm x)
  simpa only [hp, ← (hrep f).2] using hconv f

theorem real_open_dual_approximation : RealOpenDualApproximation :=
  open_dual_approximation_of_representation ℝ
    ExpandedFA.FunctionSpaces.ScalarRieszMarkov.real_representation

theorem complex_open_dual_approximation : ComplexOpenDualApproximation :=
  open_dual_approximation_of_representation ℂ
    ExpandedFA.FunctionSpaces.ScalarRieszMarkov.complex_representation

end ExpandedFA.PartIV.MeasureSmoothApproximation
