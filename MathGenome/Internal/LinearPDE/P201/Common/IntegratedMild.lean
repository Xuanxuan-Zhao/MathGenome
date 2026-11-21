import MathGenome.Internal.LinearPDE.P201Specs.Common.IntegratedMild
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.InhomogeneousEvolution
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open Filter Topology Set MeasureTheory
open scoped NNReal
namespace P201.Common.IntegratedMild
open ExpandedFA ExpandedFA.Semigroups
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X

/-- Both bounded graph-coordinate maps, for use with Bochner integration. -/
def graphInclusion (A : Unbounded.Operator 𝕜 X X) : Unbounded.GraphDomain A →L[𝕜] X :=
  (ClassicalEvolution.graphFst A).mkContinuous 1 (fun x => by
    change ‖(Unbounded.GraphDomain.toDomain A x : X)‖ ≤
      1 * (‖(Unbounded.GraphDomain.toDomain A x : X)‖ + ‖A _‖)
    rw [one_mul]
    exact le_add_of_nonneg_right (norm_nonneg _))

def graphGenerator (A : Unbounded.Operator 𝕜 X X) : Unbounded.GraphDomain A →L[𝕜] X :=
  (ClassicalEvolution.graphSnd A).mkContinuous 1 (fun x => by
    change ‖A (Unbounded.GraphDomain.toDomain A x)‖ ≤
      1 * (‖(Unbounded.GraphDomain.toDomain A x : X)‖ + ‖A _‖)
    rw [one_mul]
    exact le_add_of_nonneg_left (norm_nonneg _))

/-- The sum graph norm controls and is controlled by the product norm. -/
theorem complete_graphDomain (A : Unbounded.Operator 𝕜 X X) (hA : A.IsClosed) :
    CompleteSpace (Unbounded.GraphDomain A) := by
  let F := (graphInclusion A).prod (graphGenerator A)
  have hF : AntilipschitzWith 2 F := by
    apply F.antilipschitz_of_bound
    intro x
    change ‖(Unbounded.GraphDomain.toDomain A x : X)‖ + ‖A _‖ ≤
      (2 : ℝ) * max ‖(Unbounded.GraphDomain.toDomain A x : X)‖ ‖A _‖
    calc
      _ ≤ max ‖(Unbounded.GraphDomain.toDomain A x : X)‖ ‖A (Unbounded.GraphDomain.toDomain A x)‖ +
          max ‖(Unbounded.GraphDomain.toDomain A x : X)‖ ‖A (Unbounded.GraphDomain.toDomain A x)‖ :=
        add_le_add (le_max_left _ _) (le_max_right _ _)
      _ = _ := by dsimp only [Unbounded.GraphDomain.toDomain]; ring
  have hrange : range F = (A.graph : Set (X × X)) := by
    ext p
    constructor
    · rintro ⟨x, rfl⟩
      exact A.mem_graph _
    · intro hp
      obtain ⟨x, hx, hy⟩ := A.mem_graph_iff.mp hp
      exact ⟨x, Prod.ext hx hy⟩
  apply (hF.isUniformInducing F.uniformContinuous).completeSpace
  rw [hrange]
  exact hA.isComplete

theorem graph_complete : Expected.GraphComplete := by
  intro 𝕜 X _ _ _ _ S
  exact complete_graphDomain (Generator S) S.generator_graph_closed

/-- A graph-valued orbit primitive, with membership proved by the exact
one-sided difference quotient theorem, rather than by commuting A and ∫. -/
def graphOrbitIntegralLinear (S : C0Semigroup 𝕜 X) (h : ℝ≥0) :
    X →ₗ[𝕜] Unbounded.GraphDomain (Generator S) where
  toFun x := (⟨S.integratedOperator h x, S.integratedOperator_mem_domain h x⟩ :
    (Generator S).domain)
  map_add' x y := Subtype.ext ((S.integratedOperator h).map_add x y)
  map_smul' c x := Subtype.ext ((S.integratedOperator h).map_smul c x)

@[simp] theorem graphOrbitIntegralLinear_coe (S : C0Semigroup 𝕜 X) (h : ℝ≥0) (x : X) :
    (Unbounded.GraphDomain.toDomain _ (graphOrbitIntegralLinear S h x) : X) =
      orbitIntegral S h x := rfl

@[simp] theorem graphOrbitIntegralLinear_generator (S : C0Semigroup 𝕜 X)
    (h : ℝ≥0) (x : X) :
    Generator S (Unbounded.GraphDomain.toDomain _ (graphOrbitIntegralLinear S h x)) =
      S.operators h x - x := by
  exact generator_limit_unique S _ _ _
    (generator_has_limit S _) (S.integratedOperator_hasGeneratorLimit h x)

/-- Explicit uniform sum-graph estimate, using any common ambient bound M. -/
theorem graphOrbitIntegralLinear_bound (S : C0Semigroup 𝕜 X) (T : ℝ≥0)
    (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ s : ℝ≥0, s ≤ T → ‖S.operators s‖ ≤ M)
    (h : ℝ≥0) (hh : h ≤ T) (x : X) :
    ‖graphOrbitIntegralLinear S h x‖ ≤ (M * (T : ℝ) + M + 1) * ‖x‖ := by
  rw [Unbounded.GraphDomain.norm_eq, graphOrbitIntegralLinear_coe,
    graphOrbitIntegralLinear_generator]
  have hJ : ‖orbitIntegral S h x‖ ≤ M * (T : ℝ) * ‖x‖ := by
    calc
      _ ≤ (M * ‖x‖) * |(h : ℝ) - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
          rw [uIoc_of_le h.coe_nonneg] at hs
          exact ((S.operators s.toNNReal).le_opNorm x).trans
            (mul_le_mul_of_nonneg_right (hbound _ (by
              exact (Real.toNNReal_le_toNNReal hs.2).trans (by simpa using hh))) (norm_nonneg x)))
      _ ≤ (M * ‖x‖) * (T : ℝ) := by
        rw [sub_zero, abs_of_nonneg h.coe_nonneg]
        exact mul_le_mul_of_nonneg_left hh (mul_nonneg hM (norm_nonneg x))
      _ = _ := by ring
  have hS : ‖S.operators h x - x‖ ≤ M * ‖x‖ + ‖x‖ :=
    (norm_sub_le _ _).trans (add_le_add
      (((S.operators h).le_opNorm x).trans
        (mul_le_mul_of_nonneg_right (hbound h hh) (norm_nonneg x))) le_rfl)
  calc
    _ ≤ M * (T : ℝ) * ‖x‖ + (M * ‖x‖ + ‖x‖) := add_le_add hJ hS
    _ = _ := by ring

def graphOrbitIntegral (S : C0Semigroup 𝕜 X) (h : ℝ≥0) :
    X →L[𝕜] Unbounded.GraphDomain (Generator S) := by
  apply (graphOrbitIntegralLinear S h).mkContinuousOfExistsBound
  obtain ⟨M, hM, hbound⟩ := S.bounded_on_interval h
  exact ⟨_, graphOrbitIntegralLinear_bound S h M (by linarith) hbound h le_rfl⟩

@[simp] theorem graphOrbitIntegral_apply (S : C0Semigroup 𝕜 X) (h : ℝ≥0) (x : X) :
    graphOrbitIntegral S h x = graphOrbitIntegralLinear S h x := rfl

theorem orbit_integral_regularity : Expected.OrbitIntegralRegularity := by
  intro 𝕜 X _ _ _ _ S
  refine ⟨graphOrbitIntegral S, ?_, ?_, ?_⟩
  · intro h x
    rw [graphOrbitIntegral_apply]
    exact ⟨graphOrbitIntegralLinear_coe S h x, graphOrbitIntegralLinear_generator S h x⟩
  · intro x
    apply continuous_iff_continuousAt.mpr
    intro h
    apply (ClassicalEvolution.tendsto_graph_iff _).mpr
    simp only [graphOrbitIntegral_apply, graphOrbitIntegralLinear_coe,
      graphOrbitIntegralLinear_generator]
    constructor
    · exact ((continuous_iff_continuousAt.mpr
        (fun r : ℝ => (S.hasDerivAt_integral x r).continuousAt)).comp
        NNReal.continuous_coe).continuousAt
    · exact ((S.continuous_orbit x).sub continuous_const).continuousAt
  · intro T
    obtain ⟨M, hM, hbound⟩ := S.bounded_on_interval T
    refine ⟨M * (T : ℝ) + M + 1, by positivity, fun h hh => ?_⟩
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro x
    rw [graphOrbitIntegral_apply]
    exact graphOrbitIntegralLinear_bound S T M (by linarith) hbound h hh x

theorem mild_continuous (S : C0Semigroup 𝕜 X) (T : ℝ≥0) (x₀ : X)
    {f : ℝ → X} (hf : IntegrableOn f (Icc 0 (T : ℝ))) :
    ContinuousOn (mildSolution S x₀ f) (Icc 0 (T : ℝ)) :=
  InhomogeneousEvolution.solution_continuousOn S T x₀ hf

omit [CompleteSpace X] in
/-- A strongly continuous, locally uniformly bounded family acts jointly
continuously. This does not assume continuity in operator norm. -/
theorem continuous_family_action {Y : Type*} [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    (L : ℝ≥0 → X →L[𝕜] Y) (hc : ∀ x, Continuous (fun h => L h x))
    (hb : ∀ T : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ≥0, h ≤ T → ‖L h‖ ≤ C) :
    Continuous (fun p : ℝ≥0 × X => L p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨C, _, hC⟩ := hb (p.1 + 1)
  have hbound : ∀ᶠ q : ℝ≥0 × X in 𝓝 p, ‖L q.1‖ ≤ C := by
    filter_upwards [continuous_fst.continuousAt.eventually
      (gt_mem_nhds (show p.1 < p.1 + 1 by simp))] with q hq
    exact hC q.1 hq.le
  have hz : Tendsto (fun q : ℝ≥0 × X => L q.1 (q.2 - p.2)) (𝓝 p) (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [hbound] with q hq
      exact ((L q.1).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
    · have hv : Tendsto (fun q : ℝ≥0 × X => q.2) (𝓝 p) (𝓝 p.2) :=
        continuous_snd.tendsto p
      simpa only [sub_self, norm_zero, mul_zero] using
        (tendsto_const_nhds (x := C)).mul (hv.sub_const p.2).norm
  have hx : Tendsto (fun q : ℝ≥0 × X => L q.1 p.2) (𝓝 p) (𝓝 (L p.1 p.2)) :=
    ((hc p.2).tendsto p.1).comp (continuous_fst.tendsto p)
  change Tendsto _ (𝓝 p) (𝓝 (L p.1 p.2))
  simpa only [Function.comp_def, map_sub, sub_add_cancel, zero_add] using hz.add hx

/-- Bochner integration occurs in the complete sum-graph space. Applying its
two bounded coordinate maps justifies the unbounded-generator calculation. -/
theorem convolution_graph_integral (S : C0Semigroup 𝕜 X) (T : ℝ≥0)
    {f : ℝ → X} (hf : IntegrableOn f (Icc 0 (T : ℝ)))
    {t : ℝ} (ht : t ∈ Icc 0 (T : ℝ)) :
    ∃ z : Unbounded.GraphDomain (Generator S),
      (Unbounded.GraphDomain.toDomain _ z : X) =
        ∫ r in (0 : ℝ)..t, orbitIntegral S (t-r).toNNReal (f r) ∧
      Generator S (Unbounded.GraphDomain.toDomain _ z) =
        (∫ r in (0 : ℝ)..t, S.operators (t-r).toNNReal (f r)) -
          primitive (𝕜 := 𝕜) f t := by
  let : CompleteSpace (Unbounded.GraphDomain (Generator S)) := graph_complete S
  let : NormedSpace ℝ (Unbounded.GraphDomain (Generator S)) :=
    NormedSpace.restrictScalars ℝ 𝕜 _
  let : IsScalarTower ℝ 𝕜 (Unbounded.GraphDomain (Generator S)) :=
    IsScalarTower.restrictScalars ℝ 𝕜 _
  obtain ⟨J, hJ, hc, hb⟩ := orbit_integral_regularity S
  have haction := continuous_family_action J hc hb
  let K : ℝ → Unbounded.GraphDomain (Generator S) := fun r => J (t-r).toNNReal (f r)
  obtain ⟨C, hC, hbound⟩ := hb T
  have hKi : IntegrableOn K (Icc 0 (T : ℝ)) := by
    apply (hf.norm.const_mul C).mono'
      (haction.comp_aestronglyMeasurable
        ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.prodMk
          hf.aestronglyMeasurable))
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    apply ((J (t-r).toNNReal).le_opNorm (f r)).trans
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    apply hbound
    simpa only [Real.toNNReal_coe] using
      Real.toNNReal_le_toNNReal (show t-r ≤ (T : ℝ) by linarith [ht.2, hr.1])
  have hKt : IntervalIntegrable K volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).mpr
      (hKi.mono_set (Icc_subset_Icc le_rfl ht.2))
  refine ⟨∫ r in (0 : ℝ)..t, K r, ?_, ?_⟩
  · change graphInclusion (Generator S) (∫ r in (0 : ℝ)..t, K r) = _
    rw [← (graphInclusion (Generator S)).intervalIntegral_comp_comm hKt]
    apply intervalIntegral.integral_congr
    intro r _
    exact (hJ _ _).1
  · change graphGenerator (Generator S) (∫ r in (0 : ℝ)..t, K r) = _
    rw [← (graphGenerator (Generator S)).intervalIntegral_comp_comm hKt]
    have he : (fun r => graphGenerator (Generator S) (K r)) =
        fun r => S.operators (t-r).toNNReal (f r) - f r := by
      funext r
      exact (hJ _ _).2
    rw [he, intervalIntegral.integral_sub
      (InhomogeneousEvolution.kernel_intervalIntegrable S T hf ht)
      ((InhomogeneousEvolution.forcing_intervalIntegrable hf).mono_set (by
        simpa only [uIcc_of_le ht.1, uIcc_of_le T.coe_nonneg] using
          Icc_subset_Icc le_rfl ht.2))]
    rfl

/-- Bochner Fubini on the triangle 0 ≤ s ≤ r ≤ t, with arbitrary L¹
forcing. Only strong continuity of the action is used for measurability. -/
theorem convolution_primitive (S : C0Semigroup 𝕜 X) (T : ℝ≥0)
    {f : ℝ → X} (hf : IntegrableOn f (Icc 0 (T : ℝ)))
    {t : ℝ} (ht : t ∈ Icc 0 (T : ℝ)) :
    (∫ r in (0 : ℝ)..t, ∫ s in (0 : ℝ)..r,
      S.operators (r-s).toNNReal (f s)) =
      ∫ s in (0 : ℝ)..t, orbitIntegral S (t-s).toNNReal (f s) := by
  classical
  let μ : Measure ℝ := volume.restrict (Icc 0 t)
  let M : ℝ := InhomogeneousEvolutionSpec.intervalBound S T
  let F : ℝ × ℝ → X := fun p =>
    S.operators (p.1-p.2).toNNReal (f p.2)
  let H : ℝ × ℝ → X := {p | p.2 ≤ p.1}.indicator F
  have hft : Integrable f μ := hf.mono_set (Icc_subset_Icc le_rfl ht.2)
  have hmeas : AEStronglyMeasurable H (μ.prod μ) := by
    apply AEStronglyMeasurable.indicator _
      (measurableSet_le measurable_snd measurable_fst)
    exact (InhomogeneousEvolution.continuous_action S).comp_aestronglyMeasurable
      ((continuous_real_toNNReal.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable.prodMk
        hft.aestronglyMeasurable.comp_snd)
  have hi : Integrable H (μ.prod μ) := by
    apply ((hft.norm.comp_snd μ).const_mul M).mono' hmeas
    have hp : ∀ᵐ p : ℝ × ℝ ∂μ.prod μ, p.1 ∈ Icc 0 t ∧ p.2 ∈ Icc 0 t := by
      exact (Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)).and
        (Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Icc))
    filter_upwards [hp] with p hp
    by_cases h : p.2 ≤ p.1
    · simp only [H, indicator, mem_ofPred_eq, h, ↓reduceIte]
      exact InhomogeneousEvolution.kernel_norm_le S T (hp.1.2.trans ht.2) hp.2.1 (f p.2)
    · simp only [H, indicator, mem_ofPred_eq, h, ↓reduceIte, norm_zero]
      exact mul_nonneg (InhomogeneousEvolution.intervalBound_nonneg S T) (norm_nonneg _)
  have hleft (r : ℝ) (hr : r ∈ Icc 0 t) :
      (∫ s, H (r,s) ∂μ) = ∫ s in (0 : ℝ)..r, F (r,s) := by
    have he : (fun s => H (r,s)) = (Iic r).indicator (fun s => F (r,s)) := rfl
    have hset : Iic r ∩ Icc (0 : ℝ) t = Icc 0 r := by
      ext s
      constructor
      · rintro ⟨hsr, hs0, _⟩
        exact ⟨hs0, hsr⟩
      · rintro ⟨hs0, hsr⟩
        exact ⟨hsr, hs0, hsr.trans hr.2⟩
    rw [he, integral_indicator measurableSet_Iic]
    change (∫ s, F (r,s) ∂(volume.restrict (Icc 0 t)).restrict (Iic r)) = _
    rw [Measure.restrict_restrict measurableSet_Iic, hset,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr.1]
  have hright (s : ℝ) (hs : s ∈ Icc 0 t) :
      (∫ r, H (r,s) ∂μ) = ∫ r in s..t, F (r,s) := by
    have he : (fun r => H (r,s)) = (Ici s).indicator (fun r => F (r,s)) := rfl
    have hset : Ici s ∩ Icc (0 : ℝ) t = Icc s t := by
      ext r
      constructor
      · rintro ⟨hsr, _, hrt⟩
        exact ⟨hsr, hrt⟩
      · rintro ⟨hsr, hrt⟩
        exact ⟨hsr, hs.1.trans hsr, hrt⟩
    rw [he, integral_indicator measurableSet_Ici]
    change (∫ r, F (r,s) ∂(volume.restrict (Icc 0 t)).restrict (Ici s)) = _
    rw [Measure.restrict_restrict measurableSet_Ici, hset,
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2]
  have hshift (s : ℝ) (hs : s ∈ Icc 0 t) :
      (∫ r in s..t, F (r,s)) = orbitIntegral S (t-s).toNNReal (f s) := by
    rw [orbitIntegral, Real.coe_toNNReal _ (sub_nonneg.mpr hs.2)]
    have he := intervalIntegral.integral_comp_sub_right
      (fun r : ℝ => S.operators r.toNNReal (f s)) s (a := s) (b := t)
    simpa only [sub_self, F] using he
  calc
    _ = ∫ r, ∫ s, H (r,s) ∂μ ∂μ := by
      rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
      exact (hleft r hr).symm
    _ = ∫ s, ∫ r, H (r,s) ∂μ ∂μ := integral_integral_swap hi
    _ = ∫ s in (0 : ℝ)..t, orbitIntegral S (t-s).toNNReal (f s) := by
      rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact (hright s hs).trans (hshift s hs)

/-- Any two continuous solutions of the integrated equation coincide. The
primitive of their difference solves the homogeneous classical equation. -/
theorem integrated_unique (S : C0Semigroup 𝕜 X) (T : ℝ≥0) (x₀ : X)
    (f u v : ℝ → X) (hu : IsIntegratedSolution S T x₀ f u)
    (hv : IsIntegratedSolution S T x₀ f v) : EqOn u v (Icc 0 (T : ℝ)) := by
  obtain ⟨huc, hue⟩ := hu
  obtain ⟨hvc, hve⟩ := hv
  let d : ℝ → X := fun r => u r - v r
  let e : ℝ → X := InhomogeneousEvolution.extendForcing T d
  have hec : Continuous e := InhomogeneousEvolution.extendForcing_continuous T (huc.sub hvc)
  let w : ℝ → X := fun r => ∫ s in (0 : ℝ)..r, e s
  have hwd (r : ℝ) : HasDerivAt w (e r) r :=
    intervalIntegral.integral_hasDerivAt_right (hec.intervalIntegrable _ _)
      hec.aestronglyMeasurable.stronglyMeasurableAtFilter hec.continuousAt
  have hwc : Continuous w := continuous_iff_continuousAt.mpr
    (fun r => (hwd r).continuousAt)
  have hw0 : w 0 = 0 := by simp [w]
  have hw_eq (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      w r = primitive (𝕜 := 𝕜) u r - primitive (𝕜 := 𝕜) v r := by
    have hui : IntervalIntegrable u volume 0 r := (huc.mono (Icc_subset_Icc le_rfl hr.2)).intervalIntegrable_of_Icc hr.1
    have hvi : IntervalIntegrable v volume 0 r := (hvc.mono (Icc_subset_Icc le_rfl hr.2)).intervalIntegrable_of_Icc hr.1
    rw [primitive, primitive, ← intervalIntegral.integral_sub hui hvi]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le hr.1] at hs
    exact InhomogeneousEvolution.extendForcing_eq T d
      ⟨hs.1, hs.2.trans hr.2⟩
  have hgraph (r : ℝ) (hr : r ∈ Icc 0 (T : ℝ)) :
      ∃ h : w r ∈ (Generator S).domain, Generator S ⟨w r, h⟩ = d r := by
    obtain ⟨hu, heu⟩ := hue r hr
    obtain ⟨hv, hev⟩ := hve r hr
    have hmem : w r ∈ (Generator S).domain := by
      rw [hw_eq r hr]
      exact (Generator S).domain.sub_mem hu hv
    refine ⟨hmem, ?_⟩
    have heq : Generator S ⟨w r, hmem⟩ =
        Generator S ⟨primitive (𝕜 := 𝕜) u r, hu⟩ -
          Generator S ⟨primitive (𝕜 := 𝕜) v r, hv⟩ := by
      rw [← (Generator S).map_sub]
      congr 1
      exact Subtype.ext (hw_eq r hr)
    rw [heq]
    dsimp [d]
    rw [heu, hev]
    abel
  have hw_zero : EqOn w (fun _ => 0) (Icc 0 (T : ℝ)) := by
    intro t ht
    have hc : ContinuousOn (fun r : ℝ => S.operators (t - r).toNNReal (w r))
        (Icc 0 t) :=
      ((InhomogeneousEvolution.continuous_action S).comp
        ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).prodMk hwc)).continuousOn
    have hd : ∀ r ∈ Ico (0 : ℝ) t, HasDerivWithinAt
        (fun q : ℝ => S.operators (t - q).toNNReal (w q)) 0 (Ici r) r := by
      intro r hr
      have hrT : r ∈ Icc 0 (T : ℝ) := ⟨hr.1, hr.2.le.trans ht.2⟩
      obtain ⟨hm, he⟩ := hgraph r hrT
      apply InhomogeneousEvolution.comparison_hasDeriv_right S w hr.2 hm
      rw [he, ← InhomogeneousEvolution.extendForcing_eq T d hrT]
      exact (hwd r).hasDerivWithinAt
    have he := constant_of_has_deriv_right_zero hc hd t ⟨ht.1, le_rfl⟩
    simpa only [sub_self, Real.toNNReal_zero, C0Semigroup.zero_apply, hw0, map_zero] using he
  intro t ht
  obtain ⟨hu, heu⟩ := hue t ht
  obtain ⟨hv, hev⟩ := hve t ht
  have heq : primitive (𝕜 := 𝕜) u t = primitive (𝕜 := 𝕜) v t :=
    sub_eq_zero.mp ((hw_eq t ht).symm.trans (hw_zero ht))
  have hA : Generator S ⟨primitive (𝕜 := 𝕜) u t, hu⟩ =
      Generator S ⟨primitive (𝕜 := 𝕜) v t, hv⟩ :=
    congrArg _ (Subtype.ext heq)
  rw [heu, hev, hA]

/-- Existence in the integrated class, with the primitive formed in X and
its domain membership established through the graph-space integral. -/
theorem mild_isIntegrated (S : C0Semigroup 𝕜 X) (T : ℝ≥0) (x₀ : X)
    {f : ℝ → X} (hf : IntegrableOn f (Icc 0 (T : ℝ))) :
    IsIntegratedSolution S T x₀ f (mildSolution S x₀ f) := by
  refine ⟨mild_continuous S T x₀ hf, ?_⟩
  intro t ht
  obtain ⟨z, hz, hAz⟩ := convolution_graph_integral S T hf ht
  have hprim : primitive (𝕜 := 𝕜) (mildSolution S x₀ f) t =
      orbitIntegral S t.toNNReal x₀ + (Unbounded.GraphDomain.toDomain _ z : X) := by
    unfold primitive mildSolution InhomogeneousEvolutionSpec.solution
    rw [intervalIntegral.integral_add
      ((S.continuous_real_orbit x₀).intervalIntegrable _ _)
      ((InhomogeneousEvolution.convolution_continuousOn S T hf).mono
        (Icc_subset_Icc le_rfl ht.2) |>.intervalIntegrable_of_Icc ht.1)]
    rw [convolution_primitive S T hf ht, hz, orbitIntegral,
      Real.coe_toNNReal _ ht.1]
  have hmemJ : orbitIntegral S t.toNNReal x₀ ∈ (Generator S).domain :=
    S.integratedOperator_mem_domain t.toNNReal x₀
  have hmem : primitive (𝕜 := 𝕜) (mildSolution S x₀ f) t ∈ (Generator S).domain := by
    rw [hprim]
    exact (Generator S).domain.add_mem hmemJ (Unbounded.GraphDomain.toDomain _ z).2
  refine ⟨hmem, ?_⟩
  have hA : Generator S ⟨primitive (𝕜 := 𝕜) (mildSolution S x₀ f) t, hmem⟩ =
      (S.operators t.toNNReal x₀ - x₀) +
        ((∫ r in (0 : ℝ)..t, S.operators (t-r).toNNReal (f r)) -
          primitive (𝕜 := 𝕜) f t) := by
    have heq : (⟨primitive (𝕜 := 𝕜) (mildSolution S x₀ f) t, hmem⟩ :
        (Generator S).domain) =
        ⟨orbitIntegral S t.toNNReal x₀, hmemJ⟩ + Unbounded.GraphDomain.toDomain _ z :=
      Subtype.ext hprim
    rw [heq, (Generator S).map_add, hAz]
    congr 1
    exact graphOrbitIntegralLinear_generator S t.toNNReal x₀
  rw [hA]
  unfold mildSolution InhomogeneousEvolutionSpec.solution
  abel

/-- The integrated predicate depends only on values in the time slab. -/
theorem integrated_congr (S : C0Semigroup 𝕜 X) (T : ℝ≥0) (x₀ : X)
    (f u v : ℝ → X) (hu : IsIntegratedSolution S T x₀ f u)
    (hv : ContinuousOn v (Icc 0 (T : ℝ))) (heq : EqOn v u (Icc 0 (T : ℝ))) :
    IsIntegratedSolution S T x₀ f v := by
  refine ⟨hv, ?_⟩
  intro t ht
  have hp : primitive (𝕜 := 𝕜) v t = primitive (𝕜 := 𝕜) u t := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ht.1] at hs
    exact heq ⟨hs.1, hs.2.trans ht.2⟩
  obtain ⟨hm, hu⟩ := hu.2 t ht
  have hm' : primitive (𝕜 := 𝕜) v t ∈ (Generator S).domain := hp ▸ hm
  refine ⟨hm', ?_⟩
  have hA : Generator S ⟨primitive (𝕜 := 𝕜) v t, hm'⟩ =
      Generator S ⟨primitive (𝕜 := 𝕜) u t, hm⟩ := congrArg _ (Subtype.ext hp)
  rw [heq ht, hA]
  exact hu

/-- Full existence, uniqueness, and agreement of the formula and integrated
definitions for the original L¹ data on a positive finite time interval. -/
theorem integrated_well_posedness : Expected.IntegratedWellPosedness := by
  intro 𝕜 X _ _ _ _ S T _ x₀ f hf
  have hsol := mild_isIntegrated S T x₀ hf
  refine ⟨fun t ht => InhomogeneousEvolution.kernel_intervalIntegrable S T hf ht,
    InhomogeneousEvolution.solution_zero S x₀ f, hsol, ?_⟩
  intro u
  constructor
  · intro hu
    exact ⟨hu.1, integrated_unique S T x₀ f u (mildSolution S x₀ f) hu hsol⟩
  · rintro ⟨hc, heq⟩
    exact integrated_congr S T x₀ f (mildSolution S x₀ f) u hsol hc heq

end P201.Common.IntegratedMild
