import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SmoothBoundaryDivergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.HausdorffGraphArea
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.EuclideanHausdorffNormalization
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Sobolev.SobolevTraceAndKernel
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.SmoothPartitionOfUnity
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
The compact real smooth divergence theorem on bounded C² domains.
The accepted graph-area and normalization theorems give exact measure
identities. No pending Green formula implementation is imported.
-/

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Topology
open scoped ENNReal

namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions ExpandedFA.Sobolev

/-- The displayed C²-chart hypothesis implies the accepted C¹ predicate. -/
theorem isC1Domain_of_c2_charts {d : ℕ} (Ω : Opens (Domain d))
    (hcharts : ∀ x ∈ frontier (Ω : Set (Domain d)),
      ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
        x ∈ Φ.source ∧ Φ x i = 0 ∧
        ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
        ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) :
    C1Extension.IsC1Domain Ω := by
  intro x hx
  obtain ⟨i, Φ, hxΦ, hz, hΦ, hΦinv, hside⟩ := hcharts x hx
  exact ⟨i, Φ, hxΦ, hz, hΦ.of_le (by norm_num), hΦinv.of_le (by norm_num), hside⟩

/-- Boundedness gives exactly the compactness needed by the accepted trace
surface-measure finiteness theorem. -/
theorem compact_frontier_of_bounded {d : ℕ} (Ω : Opens (Domain d))
    (hbounded : Bornology.IsBounded (Ω : Set (Domain d))) :
    IsCompact (frontier (Ω : Set (Domain d))) :=
  hbounded.isCompact_closure.of_isClosed_subset
    isClosed_frontier frontier_subset_closure

/-- Coordinate derivatives are honest integrable functions in ambient
Lebesgue measure, and hence also on the supplied open domain. -/
theorem integrable_coordinate_derivative {d : ℕ} {f : Domain d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcompact : HasCompactSupport f) (j : Fin d) :
    Integrable (fun x => fderiv ℝ f x (coordinateVector j)) :=
  ((hf.continuous_fderiv (by simp)).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hcompact.fderiv_apply ℝ (coordinateVector j))

theorem integrableOn_coordinate_derivative {d : ℕ} (Ω : Opens (Domain d))
    {f : Domain d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hcompact : HasCompactSupport f) (j : Fin d) :
    IntegrableOn (fun x => fderiv ℝ f x (coordinateVector j)) (Ω : Set (Domain d)) :=
  (integrable_coordinate_derivative hf hcompact j).integrableOn

/-- The normalized boundary integral is integrable for every a.e. bounded
measurable component of the supplied normal. This uses finiteness already
proved for the existing surface measure, without a new measure convention. -/
theorem integrable_boundary_product {d : ℕ} (Ω : Opens (Domain d))
    (hbounded : Bornology.IsBounded (Ω : Set (Domain d)))
    (hΩ : C1Extension.IsC1Domain Ω) {f ν : Domain d → ℝ}
    (hf : Continuous f) (hcompact : HasCompactSupport f)
    (hν : AEStronglyMeasurable ν (Trace.surfaceMeasure Ω))
    (hνbound : ∀ᵐ x ∂Trace.surfaceMeasure Ω, |ν x| ≤ 1) :
    Integrable (fun x => f x * ν x) (Trace.surfaceMeasure Ω) := by
  have : IsFiniteMeasure (Trace.surfaceMeasure Ω) :=
    ⟨(Trace.surfaceMeasure_univ_lt_top Ω hΩ (compact_frontier_of_bounded Ω hbounded))⟩
  exact (hf.integrable_of_hasCompactSupport hcompact).mul_bdd hν
    (by simpa only [Real.norm_eq_abs] using hνbound)

/-- The raw graph formula with exactly the normalized surface coefficient
fixed in the trace specification. -/
theorem normalized_weighted_graph_area
    (n : ℕ) (U : Set (HausdorffGraphArea.E n)) (g : HausdorffGraphArea.E n → ℝ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (s : Set (HausdorffGraphArea.E n)) (hs : MeasurableSet s) (hsU : s ⊆ U)
    (h : HausdorffGraphArea.E (n + 1) → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ y in HausdorffGraphArea.graphMap g '' s, h y
      ∂(volume (Metric.ball (0 : HausdorffGraphArea.E n) (1 / 2 : ℝ)) •
        (Measure.hausdorffMeasure (n : ℝ) : Measure (HausdorffGraphArea.E (n + 1))))) =
      ∫⁻ x in s, ENNReal.ofReal (HausdorffGraphArea.graphJacobian g x) *
        h (HausdorffGraphArea.graphMap g x) ∂volume := by
  rw [setLIntegral_smul_measure, HausdorffGraphArea.weighted_graph_area n U g hU hg s hs hsU h hh,
    ← setLIntegral_smul_measure, EuclideanHausdorff.normalization n]

/-- Exact Euclidean-to-coordinate-space normalization of full-dimensional
Hausdorff measure, including dimension zero. The transport is a measurable
bijection and preserves the existing Lebesgue volumes. -/
theorem normalized_comap_hausdorff
    (n : ℕ) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (1 / 2 : ℝ)) •
      Measure.comap (WithLp.toLp 2 : Domain n → EuclideanSpace ℝ (Fin n))
        (Measure.hausdorffMeasure (n : ℝ)) = (volume : Measure (Domain n)) := by
  rw [← Measure.comap_smul, EuclideanHausdorff.normalization n,
    ← (PiLp.volume_preserving_toLp (Fin n)).map_eq]
  exact (MeasurableEquiv.toLp 2 (Domain n)).measurableEmbedding.comap_map volume


/-- The canonical graph is continuous on the domain on which its height is. -/
theorem continuousOn_graphMap {n : ℕ} {U : Set (HausdorffGraphArea.E n)}
    {g : HausdorffGraphArea.E n → ℝ} (hg : ContinuousOn g U) :
    ContinuousOn (HausdorffGraphArea.graphMap g) U := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n + 1) => ℝ)).comp_continuousOn
  apply continuousOn_pi.mpr
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.lastCases_last] using hg
  · simpa only [Fin.lastCases_castSucc] using (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).continuousOn

/-- The canonical square-root area factor is continuous wherever the height
function is C¹ on an open set. -/
theorem continuousOn_graphJacobian {n : ℕ} {U : Set (HausdorffGraphArea.E n)}
    {g : HausdorffGraphArea.E n → ℝ} (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U) :
    ContinuousOn (HausdorffGraphArea.graphJacobian g) U := by
  apply Real.continuous_sqrt.comp_continuousOn
  apply continuousOn_const.add
  apply continuousOn_finsetSum
  intro i _
  exact ((hg.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).pow 2

/-- A measure-level version of the normalized graph formula. It allows
subsequent Bochner integral transport without separate positive/negative parts. -/
theorem normalized_graph_measure
    (n : ℕ) (U : Set (HausdorffGraphArea.E n)) (g : HausdorffGraphArea.E n → ℝ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (s : Set (HausdorffGraphArea.E n)) (hs : MeasurableSet s) (hsU : s ⊆ U) :
    ((volume.restrict s).withDensity
      (fun x => ENNReal.ofReal (HausdorffGraphArea.graphJacobian g x))).map
        (HausdorffGraphArea.graphMap g) =
      (volume (Metric.ball (0 : HausdorffGraphArea.E n) (1 / 2 : ℝ)) •
        (Measure.hausdorffMeasure (n : ℝ) : Measure (HausdorffGraphArea.E (n + 1)))).restrict
          (HausdorffGraphArea.graphMap g '' s) := by
  have hΓ : AEMeasurable (HausdorffGraphArea.graphMap g) (volume.restrict s) :=
    ((continuousOn_graphMap hg.continuousOn).mono hsU).aemeasurable hs
  have hJ : AEMeasurable (fun x => ENNReal.ofReal (HausdorffGraphArea.graphJacobian g x))
      (volume.restrict s) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      ((continuousOn_graphJacobian hU hg).mono hsU)).aemeasurable hs
  apply Measure.ext_of_lintegral
  intro h hh
  rw [lintegral_map' hh.aemeasurable
    (hΓ.mono_ac (withDensity_absolutelyContinuous _ _))]
  calc
    _ = ∫⁻ x in s, ENNReal.ofReal (HausdorffGraphArea.graphJacobian g x) *
        h (HausdorffGraphArea.graphMap g x) ∂volume := by
      simpa only [Pi.mul_apply, Function.comp_apply] using
        lintegral_withDensity_eq_lintegral_mul₀ hJ (hh.comp_aemeasurable hΓ)
    _ = _ := (normalized_weighted_graph_area
      n U g hU hg s hs hsU h hh).symm

/-- The signed real graph formula follows from the full measure equality;
its integrand may be merely a.e. strongly measurable for surface measure. -/
theorem normalized_graph_integral
    (n : ℕ) (U : Set (HausdorffGraphArea.E n)) (g : HausdorffGraphArea.E n → ℝ)
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (s : Set (HausdorffGraphArea.E n)) (hs : MeasurableSet s) (hsU : s ⊆ U)
    (h : HausdorffGraphArea.E (n + 1) → ℝ)
    (hh : AEStronglyMeasurable h
      ((volume (Metric.ball (0 : HausdorffGraphArea.E n) (1 / 2 : ℝ)) •
        (Measure.hausdorffMeasure (n : ℝ) : Measure (HausdorffGraphArea.E (n + 1)))).restrict
          (HausdorffGraphArea.graphMap g '' s))) :
    (∫ y in HausdorffGraphArea.graphMap g '' s, h y
      ∂(volume (Metric.ball (0 : HausdorffGraphArea.E n) (1 / 2 : ℝ)) •
        (Measure.hausdorffMeasure (n : ℝ) : Measure (HausdorffGraphArea.E (n + 1))))) =
      ∫ x in s, HausdorffGraphArea.graphJacobian g x * h (HausdorffGraphArea.graphMap g x)
        ∂volume := by
  have hΓ : AEMeasurable (HausdorffGraphArea.graphMap g) (volume.restrict s) :=
    ((continuousOn_graphMap hg.continuousOn).mono hsU).aemeasurable hs
  have hJ : AEMeasurable (fun x => ENNReal.ofReal (HausdorffGraphArea.graphJacobian g x))
      (volume.restrict s) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      ((continuousOn_graphJacobian hU hg).mono hsU)).aemeasurable hs
  have hmap := normalized_graph_measure n U g hU hg s hs hsU
  rw [← hmap] at hh ⊢
  rw [integral_map (hΓ.mono_ac (withDensity_absolutelyContinuous _ _)) hh,
    integral_withDensity_eq_integral_toReal_smul₀ hJ
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [ENNReal.toReal_ofReal (Real.sqrt_nonneg _), smul_eq_mul,
      HausdorffGraphArea.graphJacobian]

/-- The pushforward of the frozen surface measure is exactly normalized
Euclidean Hausdorff measure restricted to the coordinate image of the frontier. -/
theorem map_surfaceMeasure {d : ℕ} (Ω : Opens (Domain d)) :
    (Trace.surfaceMeasure Ω).map
      (WithLp.toLp 2 : Domain d → EuclideanSpace ℝ (Fin d)) =
      (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d - 1))) (1 / 2 : ℝ)) •
        (Measure.hausdorffMeasure (d - 1 : ℕ) : Measure (EuclideanSpace ℝ (Fin d)))).restrict
          ((WithLp.toLp 2 : Domain d → EuclideanSpace ℝ (Fin d)) ''
            frontier (Ω : Set (Domain d))) := by
  let e := MeasurableEquiv.toLp 2 (Domain d)
  change (Trace.surfaceMeasure Ω).map e = _
  rw [Trace.surfaceMeasure,
    show (WithLp.toLp 2 : Domain d → EuclideanSpace ℝ (Fin d)) = e from rfl,
    Measure.map_smul,
    e.measurableEmbedding.restrict_comap, e.measurableEmbedding.map_comap,
    Set.range_eq_univ.mpr e.surjective, Measure.restrict_univ, Measure.restrict_smul]
  exact e.measurable.aemeasurable


/-- The interior part of localization: compact ambient derivatives have zero
integral, by the library's Haar-measure integration by parts with the constant 1. -/
theorem integral_coordinate_derivative_eq_zero {d : ℕ} {f : Domain d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcompact : HasCompactSupport f) (j : Fin d) :
    (∫ x, fderiv ℝ f x (coordinateVector j)) = 0 := by
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Domain d)))
    (f := fun _ : Domain d => (1 : ℝ)) (g := f) (v := coordinateVector j)
    (by simp)
    (by simpa only [one_mul] using integrable_coordinate_derivative hf hcompact j)
    (by simpa only [one_mul] using hf.continuous.integrable_of_hasCompactSupport hcompact)
    (fun _ _ => differentiableAt_const _)
    (fun x _ => hf.differentiable (by simp) x)
  simpa using h

/-- An interior-supported summand satisfies the desired identity on every
open domain, with any normal data and without boundary regularity assumptions. -/
theorem divergence_of_tsupport_subset {d : ℕ} (Ω : Opens (Domain d))
    (ν : Fin d → Domain d → ℝ) {f : Domain d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcompact : HasCompactSupport f)
    (hsupport : tsupport f ⊆ (Ω : Set (Domain d))) (j : Fin d) :
    (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
      ∫ x, f x * ν j x ∂Trace.surfaceMeasure Ω := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => image_eq_zero_of_notMem_tsupport
      (fun hd => hx (hsupport (tsupport_fderiv_apply_subset ℝ (coordinateVector j) hd)))),
    integral_coordinate_derivative_eq_zero hf hcompact j]
  symm
  apply integral_eq_zero_of_ae
  filter_upwards [Trace.surfaceMeasure_ae_frontier Ω] with x hx
  have hxΩ : x ∉ (Ω : Set (Domain d)) := (Ω.isOpen.frontier_eq ▸ hx).2
  simp only [image_eq_zero_of_notMem_tsupport (fun h => hxΩ (hsupport h)), zero_mul,
    Pi.zero_apply]

open Filter


theorem definingFunction_eq_zero_on_frontier {d : ℕ} (Ω U : Opens (Domain d))
    {r : Domain d → ℝ} (hr : ContinuousOn r U)
    (hside : ∀ y ∈ U, y ∈ Ω ↔ r y < 0)
    {x : Domain d} (hxU : x ∈ U) (hx : x ∈ frontier (Ω : Set (Domain d))) : r x = 0 := by
  have hnot : x ∉ (Ω : Set (Domain d)) := (Ω.isOpen.frontier_eq ▸ hx).2
  have hn : 0 ≤ r x := not_lt.mp (fun h => hnot ((hside x hxU).mpr h))
  apply le_antisymm _ hn
  by_contra h
  have hpos : 0 < r x := lt_of_not_ge h
  have hnhood : (U : Set (Domain d)) ∩ {y | 0 < r y} ∈ 𝓝 x :=
    inter_mem (U.isOpen.mem_nhds hxU)
      ((hr.continuousAt (U.isOpen.mem_nhds hxU)).eventually (eventually_gt_nhds hpos))
  obtain ⟨y, ⟨hyU, hyr⟩, hyΩ⟩ := mem_closure_iff_nhds.mp (frontier_subset_closure hx) _ hnhood
  exact (not_lt_of_ge (le_of_lt hyr)) ((hside y hyU).mp hyΩ)

/-- The exterior part of localization, with no boundary hypotheses. -/
theorem divergence_of_tsupport_disjoint_closure {d : ℕ} (Ω : Opens (Domain d))
    (ν : Fin d → Domain d → ℝ) {f : Domain d → ℝ}
    (hsupport : Disjoint (tsupport f) (closure (Ω : Set (Domain d)))) (j : Fin d) :
    (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
      ∫ x, f x * ν j x ∂Trace.surfaceMeasure Ω := by
  have hzero : ∀ x ∈ closure (Ω : Set (Domain d)), x ∉ tsupport f := by
    intro x hx hf
    exact Set.disjoint_left.mp hsupport hf hx
  have hleft : (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ f y (coordinateVector j)) (fun hd =>
      hzero x (subset_closure hx) (tsupport_fderiv_apply_subset ℝ (coordinateVector j) hd))
  rw [hleft]
  symm
  apply integral_eq_zero_of_ae
  filter_upwards [Trace.surfaceMeasure_ae_frontier Ω] with x hx
  simp [image_eq_zero_of_notMem_tsupport (hzero x (frontier_subset_closure hx))]

namespace GraphFlux

theorem integrable_directional {n : ℕ} {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : Domain n × ℝ) :
    Integrable (fun p => fderiv ℝ f p v) :=
  ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
    (hc.fderiv_apply ℝ v)

theorem slice_deriv {n : ℕ} {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (x : Domain n) (t : ℝ) :
    deriv (fun s => f (x, s)) t = fderiv ℝ f (x,t) (0,1) := by
  exact ((hf.differentiable one_ne_zero (x,t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).deriv

theorem slice_compact {n : ℕ} {f : Domain n × ℝ → ℝ}
    (hc : HasCompactSupport f) (x : Domain n) : HasCompactSupport (fun t => f (x,t)) := by
  exact hc.comp_isClosedEmbedding ((show Isometry (fun t : ℝ => (x,t)) from fun a b => by simp [Prod.edist_eq]).isClosedEmbedding)

theorem integral_vertical_slice {n : ℕ} {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (x : Domain n) (a : ℝ) :
    (∫ t in Ioi a, fderiv ℝ f (x,t) (0,1)) = - f (x,a) := by
  simp_rw [← slice_deriv hf]
  exact HasCompactSupport.integral_Ioi_deriv_eq
    (hf.comp (contDiff_const.prodMk contDiff_id)) (slice_compact hc x) a

/-- A graph shear and its explicit inverse; no boundedness of the height is needed. -/
def shear {n : ℕ} (g : Domain n → ℝ) (hg : Continuous g) : (Domain n × ℝ) ≃ₜ (Domain n × ℝ) where
  toFun p := (p.1, p.2 + g p.1)
  invFun p := (p.1, p.2 - g p.1)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk (continuous_snd.add (hg.comp continuous_fst))
  continuous_invFun := continuous_fst.prodMk (continuous_snd.sub (hg.comp continuous_fst))

theorem shear_preserves_volume {n : ℕ} {g : Domain n → ℝ} (hg : Continuous g) :
    MeasurePreserving (shear g hg) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id volume).skew_product
    (continuous_snd.add (hg.comp continuous_fst)).measurable
    (Filter.Eventually.of_forall fun x => (measurePreserving_add_right volume (g x)).map_eq)

theorem integral_above_graph {n : ℕ} {g : Domain n → ℝ} (hg : Continuous g)
    (F : Domain n × ℝ → ℝ) :
    (∫ p in {p : Domain n × ℝ | g p.1 < p.2}, F p) =
      ∫ p in Set.univ ×ˢ Ioi (0 : ℝ), F (shear g hg p) := by
  have hp := (shear_preserves_volume hg).integral_comp
    (shear g hg).toMeasurableEquiv.measurableEmbedding
    ({p : Domain n × ℝ | g p.1 < p.2}.indicator F)
  have hs : MeasurableSet {p : Domain n × ℝ | g p.1 < p.2} :=
    isOpen_lt (hg.comp continuous_fst) continuous_snd |>.measurableSet
  rw [integral_indicator hs] at hp
  rw [← hp, ← integral_indicator (MeasurableSet.univ.prod measurableSet_Ioi)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p => by
    simp [shear, Set.indicator, show (g p.1 < p.2 + g p.1) ↔ 0 < p.2 by constructor <;> intro h <;> linarith]

theorem integral_vertical_derivative_above_graph {n : ℕ} {g : Domain n → ℝ}
    (hg : Continuous g) {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    (∫ p in {p : Domain n × ℝ | g p.1 < p.2}, fderiv ℝ f p (0,1)) =
      - ∫ x, f (x, g x) := by
  rw [integral_above_graph hg]
  have hint : Integrable (fun p => fderiv ℝ f (shear g hg p) (0,1)) := by
    exact ((shear_preserves_volume hg).integrable_comp_emb
      (shear g hg).toMeasurableEquiv.measurableEmbedding).mpr (integrable_directional hf hc _)
  rw [show (volume : Measure (Domain n × ℝ)) = volume.prod volume from Measure.volume_eq_prod _ _,
    setIntegral_prod _ hint.integrableOn, setIntegral_univ, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    have hslice : ContDiff ℝ 1 (fun t => f (x, t + g x)) :=
      hf.comp (contDiff_const.prodMk (contDiff_id.add contDiff_const))
    have hcs : HasCompactSupport (fun t => f (x,t + g x)) :=
      (slice_compact hc x).comp_homeomorph (Homeomorph.addRight (g x))
    have hd : ∀ t, deriv (fun s => f (x,s + g x)) t =
        fderiv ℝ f (x,t+g x) (0,1) := fun t =>
      ((hf.differentiable one_ne_zero (x,t+g x)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_const t x).prodMk ((hasDerivAt_id t).add_const (g x)))).deriv
    have h := HasCompactSupport.integral_Ioi_deriv_eq hslice hcs 0
    simpa [hd, shear] using h

/-- Tangential derivatives integrate to zero on each horizontal slice. -/
theorem integral_horizontal_slice {n : ℕ} {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : Domain n) (t : ℝ) :
    (∫ x, fderiv ℝ f (x,t) (v,0)) = 0 := by
  let F : Domain n → ℝ := fun x => f (x,t)
  have hF : ContDiff ℝ 1 F := hf.comp (contDiff_id.prodMk contDiff_const)
  have hFc : HasCompactSupport F := hc.comp_isClosedEmbedding
    (show Isometry (fun x : Domain n => (x,t)) from fun a b => by simp [Prod.edist_eq]).isClosedEmbedding
  have hd : ∀ x, fderiv ℝ F x v = fderiv ℝ f (x,t) (v,0) := by
    intro x
    rw [show fderiv ℝ F x = (fderiv ℝ f (x,t)).comp
        ((ContinuousLinearMap.id ℝ (Domain n)).prod (0 : Domain n →L[ℝ] ℝ)) from
      ((hf.differentiable one_ne_zero _).hasFDerivAt.comp x
        (hasFDerivAt_prodMk_left x t)).fderiv]
    simp
  have hi : Integrable (fun x => fderiv ℝ F x v) :=
    ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hFc.fderiv_apply ℝ v)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (Domain n)))
    (f := fun _ : Domain n => (1 : ℝ)) (g := F) (v := v)
    (by simp)
    (by simpa only [one_mul] using hi)
    (by simpa using hF.continuous.integrable_of_hasCompactSupport hFc)
    (fun _ _ => differentiableAt_const _)
    (fun x _ => hF.differentiable one_ne_zero x)
  simpa [hd] using h

theorem integral_horizontal_derivative_halfspace {n : ℕ} {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : Domain n) :
    (∫ p in Set.univ ×ˢ Ioi (0 : ℝ), fderiv ℝ f p (v,0)) = 0 := by
  rw [show (volume : Measure (Domain n × ℝ)) = volume.prod volume from Measure.volume_eq_prod _ _,
    ← setIntegral_prod_swap]
  have hi : Integrable (fun q : ℝ × Domain n => fderiv ℝ f (q.2,q.1) (v,0))
      ((volume : Measure ℝ).prod volume) := (integrable_directional hf hc (v,0)).swap
  change (∫ q : ℝ × Domain n in Ioi 0 ×ˢ univ, fderiv ℝ f (q.2,q.1) (v,0) ∂volume.prod volume) = 0
  rw [setIntegral_prod (fun q : ℝ × Domain n => fderiv ℝ f (q.2,q.1) (v,0)) hi.integrableOn]
  simp only [setIntegral_univ, integral_horizontal_slice hf hc, integral_zero]

/-- A continuous tangential weight need not be globally bounded: the
compact support of the derivative suffices for all product integrability. -/
theorem integral_weighted_vertical_halfspace {n : ℕ} {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (a : Domain n → ℝ) (ha : Continuous a) :
    (∫ p in Set.univ ×ˢ Ioi (0 : ℝ), a p.1 * fderiv ℝ f p (0,1)) =
      - ∫ x, a x * f (x,0) := by
  have hint : Integrable (fun p : Domain n × ℝ => a p.1 * fderiv ℝ f p (0,1)) :=
    ((ha.comp continuous_fst).mul
      ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ (0,1)).mul_left)
  rw [show (volume : Measure (Domain n × ℝ)) = volume.prod volume from Measure.volume_eq_prod _ _,
    setIntegral_prod _ hint.integrableOn, setIntegral_univ, ← integral_neg]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    change (∫ y in Ioi (0 : ℝ), a x * fderiv ℝ f (x,y) (0,1)) = -(a x * f (x,0))
    rw [integral_const_mul, integral_vertical_slice hf hc]
    ring

theorem contDiff_shear {n : ℕ} {g : Domain n → ℝ} (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (shear g hg.continuous) :=
  contDiff_fst.prodMk (contDiff_snd.add (hg.comp contDiff_fst))

theorem fderiv_comp_shear_horizontal {n : ℕ} {g : Domain n → ℝ} (hg : ContDiff ℝ 1 g)
    {f : Domain n × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (p : Domain n × ℝ) (v : Domain n) :
    fderiv ℝ (f ∘ shear g hg.continuous) p (v,0) =
      fderiv ℝ f (shear g hg.continuous p) (v,0) +
      fderiv ℝ g p.1 v * fderiv ℝ f (shear g hg.continuous p) (0,1) := by
  have hS := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk
    (hasFDerivAt_snd.add ((hg.differentiable one_ne_zero p.1).hasFDerivAt.comp p hasFDerivAt_fst))
  change HasFDerivAt (shear g hg.continuous) _ p at hS
  have h := ((hf.differentiable one_ne_zero _).hasFDerivAt.comp p hS).fderiv
  rw [h]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, add_apply]
  change (fderiv ℝ f (shear g hg.continuous p)) (v, 0 + fderiv ℝ g p.1 v) = _
  rw [zero_add]
  rw [show (v, fderiv ℝ g p.1 v) = (v,0) + (fderiv ℝ g p.1 v) • (0,1) by simp]
  rw [map_add, map_smul, smul_eq_mul]

theorem fderiv_comp_shear_vertical {n : ℕ} {g : Domain n → ℝ} (hg : ContDiff ℝ 1 g)
    {f : Domain n × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (p : Domain n × ℝ) :
    fderiv ℝ (f ∘ shear g hg.continuous) p (0,1) =
      fderiv ℝ f (shear g hg.continuous p) (0,1) := by
  have hS := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk
    (hasFDerivAt_snd.add ((hg.differentiable one_ne_zero p.1).hasFDerivAt.comp p hasFDerivAt_fst))
  change HasFDerivAt (shear g hg.continuous) _ p at hS
  rw [((hf.differentiable one_ne_zero _).hasFDerivAt.comp p hS).fderiv]
  simp

/-- The tangential flux on the upper side of a graph has a positive sign. -/
theorem integral_horizontal_derivative_above_graph {n : ℕ} {g : Domain n → ℝ}
    (hg : ContDiff ℝ 1 g) {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : Domain n) :
    (∫ p in {p : Domain n × ℝ | g p.1 < p.2}, fderiv ℝ f p (v,0)) =
      ∫ x, f (x,g x) * fderiv ℝ g x v := by
  let F := f ∘ shear g hg.continuous
  have hF : ContDiff ℝ 1 F := hf.comp (contDiff_shear hg)
  have hFc : HasCompactSupport F := hc.comp_homeomorph (shear g hg.continuous)
  have hzero := integral_horizontal_derivative_halfspace hF hFc v
  have hweight := integral_weighted_vertical_halfspace hF hFc
    (fun x => fderiv ℝ g x v) ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hi₁ : Integrable (fun p => fderiv ℝ f (shear g hg.continuous p) (v,0)) :=
    ((shear_preserves_volume hg.continuous).integrable_comp_emb
      (shear g hg.continuous).toMeasurableEquiv.measurableEmbedding).mpr
        (integrable_directional hf hc _)
  have hi₂ : Integrable (fun p : Domain n × ℝ =>
      fderiv ℝ g p.1 v * fderiv ℝ F p (0,1)) :=
    ((((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp continuous_fst).mul
      ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      ((hFc.fderiv_apply ℝ (0,1)).mul_left)
  simp_rw [F, fderiv_comp_shear_horizontal hg hf, ← fderiv_comp_shear_vertical hg hf] at hzero
  rw [integral_add hi₁.integrableOn hi₂.integrableOn, hweight] at hzero
  rw [integral_above_graph hg.continuous]
  have he : (∫ x, fderiv ℝ g x v * F (x,0)) = ∫ x, f (x,g x) * fderiv ℝ g x v := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp [F, shear, mul_comm]
  rw [he] at hzero
  linarith

/-- The graph parametrization is a proper embedding even for an unbounded
continuous height. -/
theorem graph_closedEmbedding {n : ℕ} {g : Domain n → ℝ} (hg : Continuous g) :
    Topology.IsClosedEmbedding (fun x => (x,g x)) := by
  refine ⟨isEmbedding_graph hg, ?_⟩
  convert hg.isClosed_graph using 1
  ext p
  change (∃ y, (y,g y) = p) ↔ g p.1 = p.2
  constructor
  · rintro ⟨y, rfl⟩
    rfl
  · intro h
    exact ⟨p.1, Prod.ext rfl h⟩

theorem graph_restriction_compact {n : ℕ} {g : Domain n → ℝ} (hg : Continuous g)
    {f : Domain n × ℝ → ℝ} (hc : HasCompactSupport f) :
    HasCompactSupport (fun x => f (x,g x)) :=
  hc.comp_isClosedEmbedding (graph_closedEmbedding hg)

theorem integrable_graph_restriction {n : ℕ} {g : Domain n → ℝ} (hg : Continuous g)
    {f : Domain n × ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => f (x,g x)) :=
  (hf.comp (continuous_id.prodMk hg)).integrable_of_hasCompactSupport
    (graph_restriction_compact hg hc)

theorem integrable_weighted_graph_restriction {n : ℕ} {g : Domain n → ℝ}
    (hg : ContDiff ℝ 1 g) {f : Domain n × ℝ → ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (v : Domain n) :
    Integrable (fun x => f (x,g x) * fderiv ℝ g x v) := by
  exact ((hf.comp (continuous_id.prodMk hg.continuous)).mul
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      ((graph_restriction_compact hg.continuous hc).mul_right)

end GraphFlux


theorem invertible_vertical {n : ℕ} (A : Domain n × ℝ →L[ℝ] ℝ)
    (hA : A (0,1) ≠ 0) : (A.comp (.inr ℝ (Domain n) ℝ)).IsInvertible := by
  let B := A.comp (.inr ℝ (Domain n) ℝ)
  have hB : ∀ t : ℝ, B t = t * A (0,1) := by
    intro t
    change A (0,t) = _
    rw [show (0,t) = t • ((0,1) : Domain n × ℝ) by simp, map_smul, smul_eq_mul]
  change B.IsInvertible
  apply ContinuousLinearMap.IsInvertible.of_inverse
    (g := (A (0,1))⁻¹ • ContinuousLinearMap.id ℝ ℝ)
  · ext
    simp [hB, hA]
  · ext
    simp [hB, hA]

/-- Local implicit graph extracted from an actual nonzero vertical partial.
This includes a zero-dimensional horizontal parameter space. -/
theorem local_implicit_graph {n : ℕ} {r : Domain n × ℝ → ℝ} {p : Domain n × ℝ}
    (hr : ContDiffAt ℝ 2 r p) (hz : r p = 0)
    (hpartial : fderiv ℝ r p (0,1) ≠ 0) :
    ∃ g : Domain n → ℝ, g p.1 = p.2 ∧ ContDiffAt ℝ 2 g p.1 ∧
      (∀ᶠ v in 𝓝 p, r v = 0 ↔ g v.1 = v.2) := by
  have hI := invertible_vertical (fderiv ℝ r p) hpartial
  refine ⟨hr.implicitFunction (by norm_num) hI,
    hr.implicitFunction_apply_self (by norm_num) hI,
    hr.contDiffAt_implicitFunction (by norm_num) hI, ?_⟩
  simpa only [hz] using hr.eventually_apply_eq_iff_implicitFunction (by norm_num) hI

namespace NormalGeometry
open Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem derivative_product_nonneg {r s : E → ℝ} {x : E}
    (hr : DifferentiableAt ℝ r x) (hs : DifferentiableAt ℝ s x)
    (hrx : r x = 0) (hsx : s x = 0)
    (hside : ∀ᶠ y in 𝓝 x, r y < 0 ↔ s y < 0) (v : E) :
    0 ≤ fderiv ℝ r x v * fderiv ℝ s x v := by
  have hc : Continuous (fun t : ℝ => x + t • v) := continuous_const.add (continuous_id.smul continuous_const)
  have hc0 : Tendsto (fun t : ℝ => x + t • v) (𝓝[>] 0) (𝓝 x) := by
    simpa using (hc.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hdr : HasDerivAt (fun t : ℝ => r (x + t • v)) (fderiv ℝ r x v) 0 :=
    hr.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hds : HasDerivAt (fun t : ℝ => s (x + t • v)) (fderiv ℝ s x v) 0 :=
    hs.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
  have hlim := hdr.tendsto_slope_zero_right.mul hds.tendsto_slope_zero_right
  apply ge_of_tendsto hlim
  filter_upwards [hc0.eventually hside] with t ht
  simp only [zero_add, zero_smul, add_zero, hrx, hsx, sub_zero, smul_eq_mul]
  have hprod : 0 ≤ r (x + t • v) * s (x + t • v) := by
    by_cases hrneg : r (x + t • v) < 0
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_lt hrneg) (le_of_lt (ht.mp hrneg))
    · exact mul_nonneg (le_of_not_gt hrneg) (le_of_not_gt (fun h => hrneg (ht.mpr h)))
  convert mul_nonneg (sq_nonneg t⁻¹) hprod using 1; ring

theorem positive_proportional {A B : E →L[ℝ] ℝ} (hA : A ≠ 0) (hB : B ≠ 0)
    (hprod : ∀ v, 0 ≤ A v * B v) :
    ∃ c : ℝ, 0 < c ∧ B = c • A := by
  obtain ⟨w, hw⟩ : ∃ w, A w ≠ 0 := by
    by_contra! h
    exact hA (by ext v; exact h v)
  let u := (A w)⁻¹ • w
  have hu : A u = 1 := by simp [u, hw]
  have hkernel : ∀ v, A v = 0 → B v = 0 := by
    intro v hv
    by_contra hBv
    have hz := hprod (u + ((-B u - 1) / B v) • v)
    simp only [map_add, map_smul, smul_eq_mul, hu, hv, mul_zero, add_zero, one_mul] at hz
    rw [div_mul_cancel₀ _ hBv] at hz
    linarith
  have heq : B = (B u) • A := by
    ext v
    have hz := hkernel (v - (A v) • u) (by simp [hu])
    simp only [map_sub, map_smul, smul_eq_mul] at hz
    simpa only [smul_apply, smul_eq_mul, mul_comm] using sub_eq_zero.mp hz
  refine ⟨B u, lt_of_le_of_ne ?_ ?_, heq⟩
  · simpa only [hu, one_mul] using hprod u
  · intro hzero
    apply hB
    rw [heq, ← hzero, zero_smul]

theorem defining_derivatives_positive_proportional {r s : E → ℝ} {x : E}
    (hr : DifferentiableAt ℝ r x) (hs : DifferentiableAt ℝ s x)
    (hrx : r x = 0) (hsx : s x = 0)
    (hside : ∀ᶠ y in 𝓝 x, r y < 0 ↔ s y < 0)
    (hrne : fderiv ℝ r x ≠ 0) (hsne : fderiv ℝ s x ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ fderiv ℝ s x = c • fderiv ℝ r x :=
  positive_proportional hrne hsne (derivative_product_nonneg hr hs hrx hsx hside)

open ExpandedFA.Distributions

theorem nonzero_coordinate_derivative {d : ℕ} {r : Domain d → ℝ} {x : Domain d}
    (hpos : 0 < ∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2) :
    ∃ i : Fin d, fderiv ℝ r x (coordinateVector i) ≠ 0 := by
  by_contra! h
  simp [h] at hpos

theorem fderiv_ne_zero_of_gradient_pos {d : ℕ} {r : Domain d → ℝ} {x : Domain d}
    (hpos : 0 < ∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2) :
    fderiv ℝ r x ≠ 0 := by
  obtain ⟨i, hi⟩ := nonzero_coordinate_derivative hpos
  intro hzero
  exact hi (by rw [hzero]; simp)

/-- Positive scaling cancels exactly in the normalized Euclidean gradient. -/
theorem normalized_coordinates_eq {d : ℕ} {A B : Domain d →L[ℝ] ℝ}
    {c : ℝ} (hc : 0 < c) (hB : B = c • A)
    (_hpos : 0 < ∑ k : Fin d, (A (coordinateVector k)) ^ 2) (j : Fin d) :
    B (coordinateVector j) / Real.sqrt (∑ k : Fin d, (B (coordinateVector k)) ^ 2) =
      A (coordinateVector j) / Real.sqrt (∑ k : Fin d, (A (coordinateVector k)) ^ 2) := by
  have hsquare : (∑ k : Fin d, (B (coordinateVector k)) ^ 2) =
      c ^ 2 * ∑ k : Fin d, (A (coordinateVector k)) ^ 2 := by
    simp only [hB, smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [hsquare, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_pos hc]
  simp only [hB, smul_apply, smul_eq_mul]
  field_simp

/-- Normalized gradients of two local defining functions agree pointwise.
The hypotheses concern their actual common domain side, with no normal
continuity or graph representation assumed. -/
theorem normalized_defining_derivatives_eq {d : ℕ} {r s : Domain d → ℝ} {x : Domain d}
    (hr : DifferentiableAt ℝ r x) (hs : DifferentiableAt ℝ s x)
    (hrx : r x = 0) (hsx : s x = 0)
    (hside : ∀ᶠ y in 𝓝 x, r y < 0 ↔ s y < 0)
    (hrpos : 0 < ∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2)
    (hspos : 0 < ∑ k : Fin d, (fderiv ℝ s x (coordinateVector k)) ^ 2) (j : Fin d) :
    fderiv ℝ r x (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2) =
      fderiv ℝ s x (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ s x (coordinateVector k)) ^ 2) := by
  obtain ⟨c, hc, hderiv⟩ := defining_derivatives_positive_proportional hr hs hrx hsx hside
    (fderiv_ne_zero_of_gradient_pos hrpos) (fderiv_ne_zero_of_gradient_pos hspos)
  exact (normalized_coordinates_eq hc hderiv hrpos j).symm
end NormalGeometry


/-- Separate any chosen coordinate as the vertical variable. -/
def insertCoordinate {n : ℕ} (i : Fin (n+1)) :
    (Domain n × ℝ) ≃L[ℝ] Domain (n+1) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun p => i.insertNth p.2 p.1
    invFun := fun x => (i.removeNth x, x i)
    left_inv := fun p => by simp
    right_inv := fun x => by simp
    map_add' := fun p q => by
      ext j
      cases j using i.succAboveCases <;> simp
    map_smul' := fun c p => by
      ext j
      cases j using i.succAboveCases <;> simp }

@[simp] theorem insertCoordinate_apply {n : ℕ} (i : Fin (n+1)) (p : Domain n × ℝ) :
    insertCoordinate i p = i.insertNth p.2 p.1 := rfl

@[simp] theorem insertCoordinate_symm_apply {n : ℕ} (i : Fin (n+1)) (x : Domain (n+1)) :
    (insertCoordinate i).symm x = (i.removeNth x,x i) := rfl

@[simp] theorem insertCoordinate_vertical {n : ℕ} (i : Fin (n+1)) :
    insertCoordinate i (0,1) = coordinateVector i := by
  ext j
  cases j using i.succAboveCases <;> simp [coordinateVector]

/-- Extract the local zero-set graph in an actual coordinate of `Domain`.
No chart representation is supplied as an input. -/
theorem coordinate_implicit_graph {n : ℕ} {r : Domain (n+1) → ℝ} {x : Domain (n+1)}
    (hr : ContDiffAt ℝ 2 r x) (hz : r x = 0)
    (hpos : 0 < ∑ k : Fin (n+1), (fderiv ℝ r x (coordinateVector k)) ^ 2) :
    ∃ (i : Fin (n+1)) (g : Domain n → ℝ),
      g (i.removeNth x) = x i ∧ ContDiffAt ℝ 2 g (i.removeNth x) ∧
      (∀ᶠ y in 𝓝 x, r y = 0 ↔ g (i.removeNth y) = y i) := by
  obtain ⟨i, hi⟩ := NormalGeometry.nonzero_coordinate_derivative hpos
  let e := insertCoordinate i
  let p := e.symm x
  have hep : e p = x := e.apply_symm_apply x
  have hc : ContDiffAt ℝ 2 (r ∘ e) p := by
    have hrp : ContDiffAt ℝ 2 r (e p) := hep.symm ▸ hr
    exact hrp.comp p e.contDiff.contDiffAt
  have hd : fderiv ℝ (r ∘ e) p (0,1) = fderiv ℝ r x (coordinateVector i) := by
    have hrp : HasFDerivAt r (fderiv ℝ r x) (e p) :=
      hep.symm ▸ (hr.differentiableAt (by norm_num)).hasFDerivAt
    rw [(hrp.comp p e.hasFDerivAt).fderiv]
    change fderiv ℝ r x (e (0,1)) = _
    simp [e, coordinateVector]
  obtain ⟨g, hgp, hg, hgraph⟩ := local_implicit_graph hc (by simpa [Function.comp_def, hep] using hz)
    (by simpa only [hd] using hi)
  refine ⟨i,g,hgp,hg,?_⟩
  have hecont : Tendsto e.symm (𝓝 x) (𝓝 p) := e.symm.continuous.tendsto x
  filter_upwards [hecont.eventually hgraph] with y hy
  simpa [Function.comp_def, e] using hy

end ExpandedFA.SmoothBoundaryDivergence


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Topology ENNReal
namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions ExpandedFA.Sobolev

theorem insertCoordinate_preserves_volume {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (insertCoordinate i) volume volume := by
  have h := ((volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) i)).comp
      (Measure.measurePreserving_swap (μ := (volume : Measure (Domain n))) (ν := (volume : Measure ℝ)))
  convert h using 1
  ext p k
  rfl

/-- Move the last Euclidean coordinate to the selected coordinate. -/
def lastCoordinatePermutation {n : ℕ} (i : Fin (n+1)) :
    HausdorffGraphArea.E (n+1) ≃ₗᵢ[ℝ] HausdorffGraphArea.E (n+1) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (finSuccEquivLast.trans (finSuccEquiv' i).symm)

@[simp] theorem lastCoordinatePermutation_apply_last {n : ℕ} (i : Fin (n+1))
    (v : HausdorffGraphArea.E (n+1)) : lastCoordinatePermutation i v i = v (Fin.last n) := by
  simp [lastCoordinatePermutation, Equiv.piCongrLeft']

@[simp] theorem lastCoordinatePermutation_apply_succAbove {n : ℕ} (i : Fin (n+1))
    (v : HausdorffGraphArea.E (n+1)) (k : Fin n) :
    lastCoordinatePermutation i v (i.succAbove k) = v k.castSucc := by
  simp [lastCoordinatePermutation, Equiv.piCongrLeft']

@[simp] theorem lastCoordinatePermutation_graph {n : ℕ} (i : Fin (n+1))
    (g : HausdorffGraphArea.E n → ℝ) (z : HausdorffGraphArea.E n) :
    lastCoordinatePermutation i (HausdorffGraphArea.graphMap g z) =
      WithLp.toLp 2 (i.insertNth (g z) (WithLp.ofLp z)) := by
  ext k
  cases k using i.succAboveCases <;> simp [HausdorffGraphArea.graphMap]


/-- Coordinate and Euclidean graph area factors have exactly the same value. -/
theorem graphJacobian_toLp {n : ℕ} {g : Domain n → ℝ}
    (hg : ContDiff ℝ 1 g) (x : Domain n) :
    HausdorffGraphArea.graphJacobian (g ∘ WithLp.ofLp) (WithLp.toLp 2 x) =
      Real.sqrt (1 + ∑ k : Fin n, (fderiv ℝ g x (coordinateVector k)) ^ 2) := by
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)
  have hd : fderiv ℝ (g ∘ WithLp.ofLp) (WithLp.toLp 2 x) =
      (fderiv ℝ g x).comp e.toContinuousLinearMap :=
    ((hg.differentiable one_ne_zero x).hasFDerivAt.comp (WithLp.toLp 2 x) e.hasFDerivAt).fderiv
  unfold HausdorffGraphArea.graphJacobian
  rw [hd]
  rfl

/-- The normalized Euclidean ambient Hausdorff measure is transported
without changing the frozen coordinate-space norm or its measure. -/
theorem toLp_preserves_normalized_hausdorff (n : ℕ) :
    MeasurePreserving (WithLp.toLp 2 : Domain (n+1) → HausdorffGraphArea.E (n+1))
      (volume (Metric.ball (0 : HausdorffGraphArea.E n) (1/2 : ℝ)) •
        Measure.comap (WithLp.toLp 2 : Domain (n+1) → HausdorffGraphArea.E (n+1))
          (Measure.hausdorffMeasure (n : ℝ)))
      (volume (Metric.ball (0 : HausdorffGraphArea.E n) (1/2 : ℝ)) •
        (Measure.hausdorffMeasure (n : ℝ) : Measure (HausdorffGraphArea.E (n+1)))) := by
  let e := MeasurableEquiv.toLp 2 (Domain (n+1))
  refine ⟨e.measurable, ?_⟩
  change Measure.map e (_ • Measure.comap e _) = _
  rw [Measure.map_smul _ e.measurable.aemeasurable, e.measurableEmbedding.map_comap,
    Set.range_eq_univ.mpr e.surjective, Measure.restrict_univ]

theorem lastCoordinatePermutation_preserves_normalized_hausdorff {n : ℕ} (i : Fin (n+1)) :
    MeasurePreserving (lastCoordinatePermutation i)
      (volume (Metric.ball (0 : HausdorffGraphArea.E n) (1/2 : ℝ)) •
        (Measure.hausdorffMeasure (n : ℝ) : Measure (HausdorffGraphArea.E (n+1))))
      (volume (Metric.ball (0 : HausdorffGraphArea.E n) (1/2 : ℝ)) •
        (Measure.hausdorffMeasure (n : ℝ) : Measure (HausdorffGraphArea.E (n+1)))) := by
  let e := (lastCoordinatePermutation i).toIsometryEquiv
  refine ⟨e.continuous.measurable, ?_⟩
  change Measure.map e (_ • _) = _
  rw [Measure.map_smul _ e.continuous.measurable.aemeasurable,
    e.map_hausdorffMeasure]

/-- Signed graph integration in any coordinate of the actual sup-norm
`Domain`, with the exact normalized Euclidean Hausdorff measure. -/
theorem normalized_coordinate_graph_integral {n : ℕ} (i : Fin (n+1))
    {g : Domain n → ℝ} (hg : ContDiff ℝ 1 g)
    (s : Set (Domain n)) (hs : MeasurableSet s)
    (h : Domain (n+1) → ℝ) (hh : Measurable h) :
    (∫ y in (fun z => i.insertNth (g z) z) '' s, h y
      ∂(volume (Metric.ball (0 : HausdorffGraphArea.E n) (1/2 : ℝ)) •
        Measure.comap (WithLp.toLp 2 : Domain (n+1) → HausdorffGraphArea.E (n+1))
          (Measure.hausdorffMeasure (n : ℝ)))) =
      ∫ z in s, Real.sqrt (1 + ∑ k : Fin n, (fderiv ℝ g z (coordinateVector k)) ^ 2) *
        h (i.insertNth (g z) z) ∂volume := by
  let e := MeasurableEquiv.toLp 2 (Domain (n+1))
  let a := MeasurableEquiv.toLp 2 (Domain n)
  let P := lastCoordinatePermutation i
  let G : HausdorffGraphArea.E n → ℝ := g ∘ WithLp.ofLp
  let Γ : Domain n → Domain (n+1) := fun z => i.insertNth (g z) z
  have hG : ContDiff ℝ 1 G := hg.comp PiLp.contDiff_ofLp
  have hs' : MeasurableSet (a '' s) := a.measurableEmbedding.measurableSet_image.mpr hs
  have himage : e '' (Γ '' s) = P '' (HausdorffGraphArea.graphMap G '' (a '' s)) := by
    simp only [← Set.image_comp]
    congr 1
    ext z k
    cases k using i.succAboveCases <;> simp [e, a, P, G, Γ, HausdorffGraphArea.graphMap]
  calc
    _ = ∫ y in e '' (Γ '' s), h (e.symm y)
      ∂(volume (Metric.ball (0 : HausdorffGraphArea.E n) (1/2 : ℝ)) •
        (Measure.hausdorffMeasure (n : ℝ) : Measure (HausdorffGraphArea.E (n+1)))) := by
      change (∫ y in Γ '' s, h y ∂_) = _
      simpa only [Function.comp_def, e, MeasurableEquiv.coe_toLp,
        MeasurableEquiv.coe_toLp_symm, WithLp.ofLp_toLp] using
        ((toLp_preserves_normalized_hausdorff n).setIntegral_image_emb
        e.measurableEmbedding (h ∘ e.symm) (Γ '' s)).symm
    _ = ∫ y in HausdorffGraphArea.graphMap G '' (a '' s), h (e.symm (P y))
      ∂(volume (Metric.ball (0 : HausdorffGraphArea.E n) (1/2 : ℝ)) •
        (Measure.hausdorffMeasure (n : ℝ) : Measure (HausdorffGraphArea.E (n+1)))) := by
      rw [himage]
      exact (lastCoordinatePermutation_preserves_normalized_hausdorff i).setIntegral_image_emb
        P.toHomeomorph.measurableEmbedding (h ∘ e.symm) _
    _ = ∫ z in a '' s, HausdorffGraphArea.graphJacobian G z *
        h (e.symm (P (HausdorffGraphArea.graphMap G z))) ∂volume := by
      exact normalized_graph_integral n univ G isOpen_univ hG.contDiffOn
        (a '' s) hs' (subset_univ _) _
        ((hh.comp (e.symm.measurable.comp P.continuous.measurable)).aestronglyMeasurable)
    _ = ∫ z in s, HausdorffGraphArea.graphJacobian G (a z) *
        h (e.symm (P (HausdorffGraphArea.graphMap G (a z)))) ∂volume :=
      (PiLp.volume_preserving_toLp (Fin n)).setIntegral_image_emb a.measurableEmbedding _ s
    _ = _ := by
      apply setIntegral_congr_fun hs
      intro z _
      simp [G, a, e, P, graphJacobian_toLp hg]

end ExpandedFA.SmoothBoundaryDivergence


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Topology

namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions

/-- A compactly supported smooth function splits into finitely many smooth
compactly supported functions subordinate to any open cover of the ambient
coordinate space. This uses the accepted countable locally finite partition. -/
theorem finite_smooth_decomposition {d : ℕ} {ι : Type} (U : ι → Set (Domain d))
    (hU : ∀ i, IsOpen (U i)) (hcover : (univ : Set (Domain d)) ⊆ ⋃ i, U i)
    {f : Domain d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcompact : HasCompactSupport f) :
    ∃ (κ : Type) (s : Finset κ) (g : κ → Domain d → ℝ),
      (∀ k, ContDiff ℝ (⊤ : ℕ∞) (g k)) ∧
      (∀ k, HasCompactSupport (g k)) ∧
      (∀ k, ∃ i, tsupport (g k) ⊆ U i) ∧
      f = fun x => ∑ k ∈ s, g k x := by
  classical
  obtain ⟨κ, _, φ, _, hlf, hone, hsub⟩ :=
    Distributions.smooth_partition_of_unity d ⊤ ι U hU hcover
  have hlf' : LocallyFinite (fun k => tsupport (φ k)) := by
    exact hlf.preimage_continuous
      (continuous_id.subtype_mk (fun x : Domain d => mem_univ x))
  let s := (hlf'.finite_nonempty_inter_compact hcompact).toFinset
  let g : κ → Domain d → ℝ := fun k x => φ k x * f x
  refine ⟨κ, s, g, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (φ k).contDiff.mul hf
  · intro k
    exact (φ k).hasCompactSupport.mul_right
  · intro k
    obtain ⟨i, hi⟩ := hsub k
    exact ⟨i, tsupport_mul_subset_left.trans hi⟩
  · funext x
    by_cases hx : f x = 0
    · simp [g, hx]
    · have hsupp : Function.support (fun k => φ k x) ⊆ s := by
        intro k hk
        change k ∈ (hlf'.finite_nonempty_inter_compact hcompact).toFinset
        rw [Set.Finite.mem_toFinset]
        exact ⟨x, subset_tsupport _ hk, subset_tsupport _ hx⟩
      calc
        f x = (∑ᶠ k, φ k x) * f x := by rw [hone x (mem_univ x), one_mul]
        _ = (∑ k ∈ s, φ k x) * f x := by
          rw [finsum_eq_sum_of_support_subset _ hsupp]
        _ = ∑ k ∈ s, g k x := by simp only [Finset.sum_mul, g]

/-- Localization of the coordinate divergence identity. Every local input is
only used for compactly supported smooth functions in its own neighborhood;
all integration assumptions are explicit and can be discharged from global
smoothness and the existing finite surface measure. -/
theorem coordinate_divergence_of_local {d : ℕ} (Ω : Set (Domain d))
    (μ : Measure (Domain d)) (ν : Domain d → ℝ) (v : Domain d)
    (hinterior : ∀ g : Domain d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      IntegrableOn (fun x => fderiv ℝ g x v) Ω)
    (hboundary : ∀ g : Domain d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      Integrable (fun x => g x * ν x) μ)
    (hlocal : ∀ x : Domain d, ∃ U : Opens (Domain d), x ∈ U ∧
      ∀ g : Domain d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        tsupport g ⊆ U →
        (∫ y in Ω, fderiv ℝ g y v) = ∫ y, g y * ν y ∂μ)
    {f : Domain d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcompact : HasCompactSupport f) :
    (∫ x in Ω, fderiv ℝ f x v) = ∫ x, f x * ν x ∂μ := by
  classical
  choose U hxU hlocalU using hlocal
  obtain ⟨κ, s, g, hg, hgc, hgsub, hsum⟩ := finite_smooth_decomposition
    (fun x => (U x : Set (Domain d))) (fun x => (U x).isOpen)
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩) hf hcompact
  have hderiv (x : Domain d) : fderiv ℝ f x v = ∑ k ∈ s, fderiv ℝ (g k) x v := by
    conv_lhs => rw [hsum]
    rw [fderiv_fun_sum (fun k _ => (hg k).differentiable (by simp) x)]
    simp
  have hmul (x : Domain d) : f x * ν x = ∑ k ∈ s, g k x * ν x := by
    conv_lhs => rw [hsum]
    exact Finset.sum_mul s (fun k => g k x) (ν x)
  calc
    (∫ x in Ω, fderiv ℝ f x v) = ∫ x in Ω, ∑ k ∈ s, fderiv ℝ (g k) x v :=
      integral_congr_ae (Filter.Eventually.of_forall hderiv)
    _ = ∑ k ∈ s, ∫ x in Ω, fderiv ℝ (g k) x v :=
      integral_finsetSum s (fun k _ => hinterior _ (hg k) (hgc k))
    _ = ∑ k ∈ s, ∫ x, g k x * ν x ∂μ := by
      apply Finset.sum_congr rfl
      intro k _
      obtain ⟨x, hx⟩ := hgsub k
      exact hlocalU x (g k) (hg k) (hgc k) hx
    _ = ∫ x, ∑ k ∈ s, g k x * ν x ∂μ :=
      (integral_finsetSum s (fun k _ => hboundary _ (hg k) (hgc k))).symm
    _ = ∫ x, f x * ν x ∂μ := integral_congr_ae (Filter.Eventually.of_forall (fun x => (hmul x).symm))

end ExpandedFA.SmoothBoundaryDivergence


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Topology

namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions ExpandedFA.Sobolev

/-- The partition reduction needs the local divergence theorem only at actual
boundary points. Interior and exterior points use elementary support arguments. -/
theorem coordinate_divergence_of_boundary_local {d : ℕ} (Ω : Opens (Domain d))
    (hbounded : Bornology.IsBounded (Ω : Set (Domain d)))
    (hΩ : C1Extension.IsC1Domain Ω) (ν : Fin d → Domain d → ℝ)
    (hν : ∀ j, AEStronglyMeasurable (ν j) (Trace.surfaceMeasure Ω))
    (hνbound : ∀ j, ∀ᵐ x ∂Trace.surfaceMeasure Ω, |ν j x| ≤ 1)
    (j : Fin d)
    (hlocal : ∀ x ∈ frontier (Ω : Set (Domain d)),
      ∃ U : Opens (Domain d), x ∈ U ∧
        ∀ g : Domain d → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
          tsupport g ⊆ U →
          (∫ y in (Ω : Set (Domain d)), fderiv ℝ g y (coordinateVector j)) =
            ∫ y, g y * ν j y ∂Trace.surfaceMeasure Ω)
    {f : Domain d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hcompact : HasCompactSupport f) :
    (∫ x in (Ω : Set (Domain d)), fderiv ℝ f x (coordinateVector j)) =
      ∫ x, f x * ν j x ∂Trace.surfaceMeasure Ω := by
  apply coordinate_divergence_of_local (Ω : Set (Domain d))
    (Trace.surfaceMeasure Ω) (ν j) (coordinateVector j)
    (fun g hg hgc => integrableOn_coordinate_derivative Ω hg hgc j)
    (fun g hg hgc => integrable_boundary_product Ω hbounded hΩ hg.continuous hgc
      (hν j) (hνbound j)) ?_ hf hcompact
  intro x
  by_cases hx : x ∈ (Ω : Set (Domain d))
  · refine ⟨Ω, hx, ?_⟩
    intro g hg hgc hs
    exact divergence_of_tsupport_subset Ω ν hg hgc hs j
  · by_cases hc : x ∈ closure (Ω : Set (Domain d))
    · exact hlocal x (by rw [Ω.isOpen.frontier_eq]; exact ⟨hc, hx⟩)
    · refine ⟨⟨(closure (Ω : Set (Domain d)))ᶜ, isClosed_closure.isOpen_compl⟩, hc, ?_⟩
      intro g _ _ hs
      apply divergence_of_tsupport_disjoint_closure Ω ν (j := j)
      exact Set.disjoint_left.mpr (fun y hy hyΩ => (hs hy) hyΩ)

end ExpandedFA.SmoothBoundaryDivergence


noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions ExpandedFA.Sobolev

namespace NormalGeometry
/-- Identify the supplied normal with any regular local defining function,
including at points other than the original graph-patch center. -/
theorem supplied_normal_eq {d : ℕ} (Ω : Opens (Domain d))
    {ν : Fin d → Domain d → ℝ} {x : Domain d}
    (hνx : ∃ (U : Opens (Domain d)) (r : Domain d → ℝ),
      x ∈ U ∧ ContDiffOn ℝ 2 r U ∧ r x = 0 ∧
      (∀ y ∈ U, y ∈ Ω ↔ r y < 0) ∧
      0 < ∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2 ∧
      ∀ j, ν j x = fderiv ℝ r x (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2))
    {s : Domain d → ℝ} (hs : DifferentiableAt ℝ s x) (hsx : s x = 0)
    (hside : ∀ᶠ y in 𝓝 x, y ∈ Ω ↔ s y < 0)
    (hspos : 0 < ∑ k : Fin d, (fderiv ℝ s x (coordinateVector k)) ^ 2)
    (j : Fin d) :
    ν j x = fderiv ℝ s x (coordinateVector j) /
      Real.sqrt (∑ k : Fin d, (fderiv ℝ s x (coordinateVector k)) ^ 2) := by
  obtain ⟨U, r, hxU, hr, hrx, hrside, hrpos, hνr⟩ := hνx
  rw [hνr]
  apply normalized_defining_derivatives_eq
    ((hr.contDiffAt (U.isOpen.mem_nhds hxU)).differentiableAt (by norm_num))
    hs hrx hsx _ hrpos hspos
  filter_upwards [U.isOpen.mem_nhds hxU, hside] with y hyU hys
  exact (hrside y hyU).symm.trans hys
end NormalGeometry

@[simp] theorem insertCoordinate_horizontal {n : ℕ} (i : Fin (n+1)) (k : Fin n) :
    insertCoordinate i (coordinateVector k,0) = coordinateVector (i.succAbove k) := by
  ext j
  cases j using i.succAboveCases <;> simp [coordinateVector, Pi.single_apply]

@[simp] theorem insertCoordinate_symm_vertical {n : ℕ} (i : Fin (n+1)) :
    (insertCoordinate i).symm (coordinateVector i) = (0,1) := by
  apply (insertCoordinate i).injective
  rw [(insertCoordinate i).apply_symm_apply]
  exact (insertCoordinate_vertical i).symm

@[simp] theorem insertCoordinate_symm_horizontal {n : ℕ} (i : Fin (n+1)) (k : Fin n) :
    (insertCoordinate i).symm (coordinateVector (i.succAbove k)) = (coordinateVector k,0) := by
  apply (insertCoordinate i).injective
  rw [(insertCoordinate i).apply_symm_apply]
  exact (insertCoordinate_horizontal i k).symm

end ExpandedFA.SmoothBoundaryDivergence

namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions ExpandedFA.Sobolev

/-- A local graph defining function with the region below the graph as its
negative side. -/
def graphDefiningFunction {n : ℕ} (i : Fin (n+1)) (g : Domain n → ℝ)
    (x : Domain (n+1)) : ℝ := x i - g (i.removeNth x)

theorem graphDefiningFunction_hasFDerivAt {n : ℕ} (i : Fin (n+1))
    {g : Domain n → ℝ} {x : Domain (n+1)}
    (hg : DifferentiableAt ℝ g (i.removeNth x)) :
    HasFDerivAt (graphDefiningFunction i g)
      (((ContinuousLinearMap.snd ℝ (Domain n) ℝ).comp
          (insertCoordinate i).symm.toContinuousLinearMap) -
        (fderiv ℝ g (i.removeNth x)).comp
          ((ContinuousLinearMap.fst ℝ (Domain n) ℝ).comp
            (insertCoordinate i).symm.toContinuousLinearMap)) x := by
  have hfst := (ContinuousLinearMap.fst ℝ (Domain n) ℝ).hasFDerivAt.comp x
    (insertCoordinate i).symm.hasFDerivAt
  have hsnd := (ContinuousLinearMap.snd ℝ (Domain n) ℝ).hasFDerivAt.comp x
    (insertCoordinate i).symm.hasFDerivAt
  exact hsnd.sub (hg.hasFDerivAt.comp x hfst)

@[simp] theorem graphDefiningFunction_fderiv_vertical {n : ℕ} (i : Fin (n+1))
    {g : Domain n → ℝ} {x : Domain (n+1)}
    (hg : DifferentiableAt ℝ g (i.removeNth x)) :
    fderiv ℝ (graphDefiningFunction i g) x (coordinateVector i) = 1 := by
  rw [(graphDefiningFunction_hasFDerivAt i hg).fderiv]
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, insertCoordinate_symm_vertical]
  change 1 - fderiv ℝ g (i.removeNth x) 0 = 1
  simp

@[simp] theorem graphDefiningFunction_fderiv_horizontal {n : ℕ} (i : Fin (n+1))
    {g : Domain n → ℝ} {x : Domain (n+1)}
    (hg : DifferentiableAt ℝ g (i.removeNth x)) (k : Fin n) :
    fderiv ℝ (graphDefiningFunction i g) x (coordinateVector (i.succAbove k)) =
      -fderiv ℝ g (i.removeNth x) (coordinateVector k) := by
  rw [(graphDefiningFunction_hasFDerivAt i hg).fderiv]
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, insertCoordinate_symm_horizontal]
  change 0 - fderiv ℝ g (i.removeNth x) (coordinateVector k) = _
  exact zero_sub _

theorem graphDefiningFunction_gradient_sq {n : ℕ} (i : Fin (n+1))
    {g : Domain n → ℝ} {x : Domain (n+1)}
    (hg : DifferentiableAt ℝ g (i.removeNth x)) :
    (∑ k : Fin (n+1), (fderiv ℝ (graphDefiningFunction i g) x (coordinateVector k)) ^ 2) =
      1 + ∑ k : Fin n, (fderiv ℝ g (i.removeNth x) (coordinateVector k)) ^ 2 := by
  rw [Fin.sum_univ_succAbove _ i]
  simp only [graphDefiningFunction_fderiv_vertical i hg,
    graphDefiningFunction_fderiv_horizontal i hg, one_pow, neg_sq]

end ExpandedFA.SmoothBoundaryDivergence

namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions ExpandedFA.Sobolev

/-- Both graph orientations identify the arbitrary supplied geometric normal;
σ = 1 is the region below the graph and σ = -1 is the region above it. -/
theorem supplied_normal_eq_oriented_graph {n : ℕ} (Ω : Opens (Domain (n+1)))
    {ν : Fin (n+1) → Domain (n+1) → ℝ} {x : Domain (n+1)}
    (hνx : ∃ (U : Opens (Domain (n+1))) (r : Domain (n+1) → ℝ),
      x ∈ U ∧ ContDiffOn ℝ 2 r U ∧ r x = 0 ∧
      (∀ y ∈ U, y ∈ Ω ↔ r y < 0) ∧
      0 < ∑ k : Fin (n+1), (fderiv ℝ r x (coordinateVector k)) ^ 2 ∧
      ∀ j, ν j x = fderiv ℝ r x (coordinateVector j) /
        Real.sqrt (∑ k : Fin (n+1), (fderiv ℝ r x (coordinateVector k)) ^ 2))
    (i : Fin (n+1)) {g : Domain n → ℝ}
    (hg : DifferentiableAt ℝ g (i.removeNth x))
    (hgraph : g (i.removeNth x) = x i)
    (σ : ℝ) (hσ : σ ^ 2 = 1)
    (hside : ∀ᶠ y in 𝓝 x, y ∈ Ω ↔ σ * (y i - g (i.removeNth y)) < 0) :
    ν i x = σ / Real.sqrt
        (1 + ∑ k : Fin n, (fderiv ℝ g (i.removeNth x) (coordinateVector k)) ^ 2) ∧
      ∀ k : Fin n, ν (i.succAbove k) x =
        -(σ * fderiv ℝ g (i.removeNth x) (coordinateVector k)) / Real.sqrt
          (1 + ∑ k : Fin n, (fderiv ℝ g (i.removeNth x) (coordinateVector k)) ^ 2) := by
  let q := graphDefiningFunction i g
  let s := fun y => σ * q y
  have hdq : DifferentiableAt ℝ q x :=
    (graphDefiningFunction_hasFDerivAt i hg).differentiableAt
  have hds : DifferentiableAt ℝ s x := hdq.const_mul σ
  have hD (j : Fin (n+1)) : fderiv ℝ s x (coordinateVector j) =
      σ * fderiv ℝ q x (coordinateVector j) := by
    dsimp [s]
    rw [fderiv_const_mul hdq σ]
    rfl
  have hgrad : (∑ j : Fin (n+1), (fderiv ℝ s x (coordinateVector j)) ^ 2) =
      1 + ∑ k : Fin n, (fderiv ℝ g (i.removeNth x) (coordinateVector k)) ^ 2 := by
    simp_rw [hD, mul_pow, hσ, one_mul]
    exact graphDefiningFunction_gradient_sq i hg
  have hpos : 0 < ∑ j : Fin (n+1), (fderiv ℝ s x (coordinateVector j)) ^ 2 := by
    rw [hgrad]
    positivity
  have hsx : s x = 0 := by simp [s, q, graphDefiningFunction, hgraph]
  have hνs (j : Fin (n+1)) := NormalGeometry.supplied_normal_eq Ω hνx hds hsx hside hpos j
  constructor
  · have hj := hνs i
    rw [hgrad, hD, graphDefiningFunction_fderiv_vertical i hg, mul_one] at hj
    exact hj
  · intro k
    have hj := hνs (i.succAbove k)
    rw [hgrad, hD, graphDefiningFunction_fderiv_horizontal i hg, mul_neg] at hj
    exact hj

end ExpandedFA.SmoothBoundaryDivergence

namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions ExpandedFA.Sobolev
namespace NormalGeometry

/-- The normal data at each nearby boundary point agree with one fixed regular
local defining function. Regularity at the center is propagated by continuity. -/
theorem supplied_normal_eventually_eq_definingFunction {d : ℕ}
    (Ω : Opens (Domain d)) {ν : Fin d → Domain d → ℝ} {x : Domain d}
    (hν : ∀ x ∈ frontier (Ω : Set (Domain d)), ∃ (U : Opens (Domain d)) (r : Domain d → ℝ),
      x ∈ U ∧ ContDiffOn ℝ 2 r U ∧ r x = 0 ∧
      (∀ y ∈ U, y ∈ Ω ↔ r y < 0) ∧
      0 < ∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2 ∧
      ∀ j, ν j x = fderiv ℝ r x (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2))
    (U : Opens (Domain d)) {r : Domain d → ℝ}
    (hxU : x ∈ U) (hr : ContDiffOn ℝ 2 r U)
    (hside : ∀ y ∈ U, y ∈ Ω ↔ r y < 0)
    (hpos : 0 < ∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2) :
    ∀ᶠ y in 𝓝 x, y ∈ frontier (Ω : Set (Domain d)) →
      ∀ j : Fin d, ν j y = fderiv ℝ r y (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ r y (coordinateVector k)) ^ 2) := by
  have hrAt := hr.contDiffAt (U.isOpen.mem_nhds hxU)
  have hgradcont : ContinuousAt
      (fun y => ∑ k : Fin d, (fderiv ℝ r y (coordinateVector k)) ^ 2) x := by
    have hD := hrAt.continuousAt_fderiv (by norm_num)
    fun_prop
  have hposEvent := hgradcont.eventually (eventually_gt_nhds hpos)
  filter_upwards [U.isOpen.mem_nhds hxU, hposEvent] with y hyU hypos hyfront
  intro j
  apply supplied_normal_eq Ω (hν y hyfront)
    ((hr.contDiffAt (U.isOpen.mem_nhds hyU)).differentiableAt (by norm_num))
    (definingFunction_eq_zero_on_frontier Ω U hr.continuousOn hside hyU hyfront)
    _ hypos j
  filter_upwards [U.isOpen.mem_nhds hyU] with z hzU
  exact hside z hzU

end NormalGeometry
end ExpandedFA.SmoothBoundaryDivergence


noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Topology ENNReal
namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions ExpandedFA.Sobolev

/-- Only points in the integrand's support matter when changing a set of
integration. No integrability assumption is needed for this equality. -/
theorem setIntegral_eq_of_mem_support_iff {E : Type*} [MeasurableSpace E]
    (μ : Measure E) {s t : Set E} (hs : MeasurableSet s) (ht : MeasurableSet t)
    (h : E → ℝ) (heq : ∀ x ∈ Function.support h, x ∈ s ↔ x ∈ t) :
    (∫ x in s, h x ∂μ) = ∫ x in t, h x ∂μ := by
  rw [← integral_indicator hs, ← integral_indicator ht]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : h x = 0
    · by_cases hxs : x ∈ s <;> by_cases hxt : x ∈ t <;>
        simp [Set.indicator,hxs,hxt,hx]
    · have hst := heq x hx
      by_cases hxs : x ∈ s
      · simp [hxs, hst.mp hxs]
      · have hxt : x ∉ t := fun ht => hxs (hst.mpr ht)
        simp [hxs, hxt]

/-- The entire frozen surface measure agrees locally with exact graph area
in any selected coordinate. Compact support will supply the displayed local
support condition when the formula is used for a boundary summand. -/
theorem integral_surface_eq_coordinate_graph_integral {n : ℕ}
    (Ω W : Opens (Domain (n+1))) (i : Fin (n+1))
    {g : Domain n → ℝ} (hg : ContDiff ℝ 1 g)
    (hfront : ∀ y ∈ W, y ∈ frontier (Ω : Set (Domain (n+1))) ↔
      g (i.removeNth y) = y i)
    (h : Domain (n+1) → ℝ) (hh : Measurable h)
    (hsupport : Function.support h ⊆ (W : Set (Domain (n+1)))) :
    (∫ y, h y ∂Trace.surfaceMeasure Ω) =
      ∫ z, Real.sqrt (1 + ∑ k : Fin n, (fderiv ℝ g z (coordinateVector k)) ^ 2) *
        h (i.insertNth (g z) z) ∂volume := by
  let Γ : Domain n → Domain (n+1) := fun z => i.insertNth (g z) z
  have hrange : Set.range Γ = {y | g (i.removeNth y) = y i} := by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      simp [Γ]
    · intro hy
      refine ⟨i.removeNth y, ?_⟩
      change i.insertNth (g (i.removeNth y)) (i.removeNth y) = y
      rw [hy, i.insertNth_self_removeNth]
  have hremove : Continuous (i.removeNth : Domain (n+1) → Domain n) := by
    exact continuous_pi (fun k => continuous_apply (i.succAbove k))
  have hclosed : IsClosed (Set.range Γ) := by
    rw [hrange]
    exact isClosed_eq (hg.continuous.comp hremove) (continuous_apply i)
  simp only [Trace.surfaceMeasure, Nat.add_sub_cancel]
  rw [← Measure.restrict_smul]
  calc
    _ = ∫ y in Set.range Γ, h y
      ∂(volume (Metric.ball (0 : HausdorffGraphArea.E n) (1/2 : ℝ)) •
        Measure.comap (WithLp.toLp 2 : Domain (n+1) → HausdorffGraphArea.E (n+1))
          (Measure.hausdorffMeasure (n : ℝ))) := by
      apply setIntegral_eq_of_mem_support_iff _ isClosed_frontier.measurableSet hclosed.measurableSet
      intro y hy
      rw [hrange]
      exact hfront y (hsupport hy)
    _ = _ := by
      simpa only [Γ, Set.image_univ, setIntegral_univ] using
        normalized_coordinate_graph_integral i hg univ MeasurableSet.univ h hh

end ExpandedFA.SmoothBoundaryDivergence


noncomputable section
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology
namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions

theorem neg_iff_of_abs_sub_le_half {u v : ℝ}
    (h : |u - v| ≤ |v| / 2) : u < 0 ↔ v < 0 := by
  have hh := abs_le.mp h
  by_cases hv : v < 0
  · rw [abs_of_neg hv] at hh
    constructor
    · exact fun _ => hv
    · intro _
      linarith [hh.2]
  · rw [abs_of_nonneg (le_of_not_gt hv)] at hh
    constructor
    · intro hu
      linarith [hh.1]
    · exact fun h => False.elim (hv h)

/-- The local zero graph determines the actual domain side. The multiplier is
exactly the nonzero vertical partial of the supplied defining function. -/
theorem local_implicit_graph_side {n : ℕ} {r : Domain n × ℝ → ℝ} {p : Domain n × ℝ}
    (hr : ContDiffAt ℝ 2 r p) (hz : r p = 0)
    (hpartial : fderiv ℝ r p (0,1) ≠ 0) :
    ∃ g : Domain n → ℝ, g p.1 = p.2 ∧ ContDiffAt ℝ 2 g p.1 ∧
      (∀ᶠ v in 𝓝 p, r v = 0 ↔ g v.1 = v.2) ∧
      (∀ᶠ v in 𝓝 p, r v < 0 ↔ fderiv ℝ r p (0,1) * (v.2 - g v.1) < 0) := by
  obtain ⟨g,hgp,hg,hgraph⟩ := local_implicit_graph hr hz hpartial
  refine ⟨g,hgp,hg,hgraph,?_⟩
  have hc : Tendsto (fun v : Domain n × ℝ => (v.1,g v.1)) (𝓝 p) (𝓝 p) := by
    have hf : Tendsto (fun v : Domain n × ℝ => v.1) (𝓝 p) (𝓝 p.1) := continuous_fst.tendsto p
    have h := hf.prodMk_nhds (hg.continuousAt.tendsto.comp hf)
    simpa only [Function.comp_apply,hgp, Prod.mk.eta] using h
  have hzero : ∀ᶠ v in 𝓝 p, r (v.1,g v.1) = 0 := by
    filter_upwards [hc.eventually hgraph] with v hv
    exact hv.mpr rfl
  have hsmall := ((hr.hasStrictFDerivAt (by norm_num)).isLittleO.comp_tendsto
    (tendsto_id.prodMk_nhds hc)).bound
      (show 0 < |fderiv ℝ r p (0,1)| / 2 from div_pos (abs_pos.mpr hpartial) (by norm_num))
  filter_upwards [hzero,hsmall] with v hv hsmall
  dsimp only [Function.comp_apply, id_eq] at hsmall
  rw [hv, sub_zero] at hsmall
  have hsub : v - (v.1,g v.1) = (v.2 - g v.1) • ((0,1) : Domain n × ℝ) := by
    ext <;> simp
  rw [hsub,map_smul] at hsmall
  simp only [smul_eq_mul, norm_smul, Prod.norm_def, norm_zero, norm_one, max_eq_right
    (show (0 : ℝ) ≤ 1 by norm_num), mul_one, Real.norm_eq_abs] at hsmall
  apply neg_iff_of_abs_sub_le_half
  calc
    |r v - fderiv ℝ r p (0,1) * (v.2-g v.1)| =
        |r v - (v.2-g v.1) * fderiv ℝ r p (0,1)| := by rw [mul_comm (fderiv ℝ r p (0,1))]
    _ ≤ _ := hsmall
    _ = _ := by rw [abs_mul]; ring

/-- A finite-order smooth germ extends to a global smooth function after
multiplication by a bump supported inside its regularity neighborhood. -/
theorem global_contDiff_extension {n : ℕ} {g : Domain n → ℝ} {x : Domain n}
    (hg : ContDiffAt ℝ 2 g x) :
    ∃ G : Domain n → ℝ, ContDiff ℝ 2 G ∧ HasCompactSupport G ∧ G =ᶠ[𝓝 x] g := by
  obtain ⟨ε,hε,hsub⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (hg.eventually (by norm_num))
  let ψ : ContDiffBump x := ⟨ε/2,ε,half_pos hε,half_lt_self hε⟩
  refine ⟨fun y => ψ y * g y,?_,ψ.hasCompactSupport.mul_right,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport ψ
    · exact ψ.contDiffAt.mul (hsub (by simpa only [ψ.tsupport_eq] using hy))
    · apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hy] with z hz
      rw [image_eq_zero_of_notMem_tsupport (f := ψ) hz,zero_mul]
  · filter_upwards [ψ.eventuallyEq_one] with y hy
    simp only [hy,Pi.one_apply,one_mul]

/-- The implicit height can be chosen globally C². Only its germ enters the
local zero-set and signed-side statements. -/
theorem local_implicit_graph_global_side {n : ℕ} {r : Domain n × ℝ → ℝ} {p : Domain n × ℝ}
    (hr : ContDiffAt ℝ 2 r p) (hz : r p = 0)
    (hpartial : fderiv ℝ r p (0,1) ≠ 0) :
    ∃ g : Domain n → ℝ, g p.1 = p.2 ∧ ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∀ᶠ v in 𝓝 p, r v = 0 ↔ g v.1 = v.2) ∧
      (∀ᶠ v in 𝓝 p, r v < 0 ↔ fderiv ℝ r p (0,1) * (v.2 - g v.1) < 0) := by
  obtain ⟨g,hgp,hg,hgraph,hside⟩ := local_implicit_graph_side hr hz hpartial
  obtain ⟨G,hG,hGc,heq⟩ := global_contDiff_extension hg
  refine ⟨G,heq.self_of_nhds.trans hgp,hG,hGc,?_,?_⟩
  · filter_upwards [hgraph,(continuous_fst.tendsto p).eventually heq] with v hv heqv
    simpa only [heqv] using hv
  · filter_upwards [hside,(continuous_fst.tendsto p).eventually heq] with v hv heqv
    simpa only [heqv] using hv

/-- Coordinate graph extraction with a global C² height and the actual signed
side. The orientation multiplier is a coordinate partial of the given r. -/
theorem coordinate_implicit_graph_global_side {n : ℕ} {r : Domain (n+1) → ℝ} {x : Domain (n+1)}
    (hr : ContDiffAt ℝ 2 r x) (hz : r x = 0)
    (hpos : 0 < ∑ k : Fin (n+1), (fderiv ℝ r x (coordinateVector k)) ^ 2) :
    ∃ (i : Fin (n+1)) (g : Domain n → ℝ),
      fderiv ℝ r x (coordinateVector i) ≠ 0 ∧
      g (i.removeNth x) = x i ∧ ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      (∀ᶠ y in 𝓝 x, r y = 0 ↔ g (i.removeNth y) = y i) ∧
      (∀ᶠ y in 𝓝 x, r y < 0 ↔
        fderiv ℝ r x (coordinateVector i) * (y i - g (i.removeNth y)) < 0) := by
  obtain ⟨i, hi⟩ := NormalGeometry.nonzero_coordinate_derivative hpos
  let e := insertCoordinate i
  let p := e.symm x
  have hep : e p = x := e.apply_symm_apply x
  have hc : ContDiffAt ℝ 2 (r ∘ e) p := by
    have hrp : ContDiffAt ℝ 2 r (e p) := hep.symm ▸ hr
    exact hrp.comp p e.contDiff.contDiffAt
  have hd : fderiv ℝ (r ∘ e) p (0,1) = fderiv ℝ r x (coordinateVector i) := by
    have hrp : HasFDerivAt r (fderiv ℝ r x) (e p) :=
      hep.symm ▸ (hr.differentiableAt (by norm_num)).hasFDerivAt
    rw [(hrp.comp p e.hasFDerivAt).fderiv]
    change fderiv ℝ r x (e (0,1)) = _
    simp [e, coordinateVector]
  obtain ⟨g,hgp,hg,hgc,hgraph,hside⟩ := local_implicit_graph_global_side hc
    (by simpa [Function.comp_def, hep] using hz) (by simpa only [hd] using hi)
  refine ⟨i,g,hi,hgp,hg,hgc,?_,?_⟩
  · have hecont : Tendsto e.symm (𝓝 x) (𝓝 p) := e.symm.continuous.tendsto x
    filter_upwards [hecont.eventually hgraph] with y hy
    simpa [Function.comp_def, e] using hy
  · have hecont : Tendsto e.symm (𝓝 x) (𝓝 p) := e.symm.continuous.tendsto x
    filter_upwards [hecont.eventually hside] with y hy
    rw [hd] at hy
    simpa [Function.comp_def, e] using hy

theorem inter_frontier_eq_of_inter_eq {E : Type*} [TopologicalSpace E]
    {s t W : Set E} (hW : IsOpen W) (h : s ∩ W = t ∩ W) :
    frontier s ∩ W = frontier t ∩ W := by
  rw [← frontier_inter_open_inter hW, h, frontier_inter_open_inter hW]

/-- The frontier of either signed side of a continuous global graph is the
graph itself, including a zero-dimensional horizontal space. -/
theorem mem_frontier_signed_graph {n : ℕ} {g : Domain n → ℝ} (hg : Continuous g)
    {a : ℝ} (ha : a ≠ 0) (p : Domain n × ℝ) :
    p ∈ frontier {v : Domain n × ℝ | a * (v.2 - g v.1) < 0} ↔ p.2 = g p.1 := by
  let e := GraphFlux.shear g hg
  let S : Set (Domain n × ℝ) := {v | a * (v.2 - g v.1) < 0}
  have hmem : p ∈ frontier S ↔ e.symm p ∈ frontier (e ⁻¹' S) := by
    rw [← e.preimage_frontier]
    simp only [mem_preimage,e.apply_symm_apply]
  rcases lt_or_gt_of_ne ha with haneg | hapos
  · have hpre : e ⁻¹' S = Set.univ ×ˢ Set.Ioi 0 := by
      ext v
      change a * (v.2 + g v.1 - g v.1) < 0 ↔ True ∧ 0 < v.2
      simp only [add_sub_cancel_right,mul_neg_iff,haneg,
        not_lt_of_ge haneg.le,false_and,false_or,true_and]
    rw [hpre,frontier_univ_prod_eq,frontier_Ioi] at hmem
    change p ∈ frontier S ↔ True ∧ p.2-g p.1 = 0 at hmem
    simpa only [true_and,sub_eq_zero] using hmem
  · have hpre : e ⁻¹' S = Set.univ ×ˢ Set.Iio 0 := by
      ext v
      change a * (v.2 + g v.1 - g v.1) < 0 ↔ True ∧ v.2 < 0
      simp only [add_sub_cancel_right,mul_neg_iff,hapos,
        not_lt_of_ge hapos.le,false_and,or_false,true_and]
    rw [hpre,frontier_univ_prod_eq,frontier_Iio] at hmem
    change p ∈ frontier S ↔ True ∧ p.2-g p.1 = 0 at hmem
    simpa only [true_and,sub_eq_zero] using hmem

/-- Coordinate reordering transports the signed graph frontier exactly. -/
theorem mem_frontier_coordinate_signed_graph {n : ℕ} (i : Fin (n+1))
    {g : Domain n → ℝ} (hg : Continuous g) {a : ℝ} (ha : a ≠ 0)
    (y : Domain (n+1)) :
    y ∈ frontier {z : Domain (n+1) | a * (z i - g (i.removeNth z)) < 0} ↔
      g (i.removeNth y) = y i := by
  let e := insertCoordinate i
  let S : Set (Domain (n+1)) := {z | a * (z i - g (i.removeNth z)) < 0}
  have hpre : e ⁻¹' S = {v : Domain n × ℝ | a * (v.2 - g v.1) < 0} := by
    ext v
    simp [e,S]
  have hm : y ∈ frontier S ↔ e.symm y ∈ frontier (e ⁻¹' S) := by
    change y ∈ frontier S ↔ e.symm y ∈ frontier (e.toHomeomorph ⁻¹' S)
    rw [← e.toHomeomorph.preimage_frontier]
    change y ∈ frontier S ↔ e (e.symm y) ∈ frontier S
    rw [e.apply_symm_apply]
  rw [hpre,mem_frontier_signed_graph hg ha] at hm
  simpa only [e,insertCoordinate_symm_apply,eq_comm] using hm

theorem exists_unit_sign_same_neg {a : ℝ} (ha : a ≠ 0) :
    ∃ σ : ℝ, σ ^ 2 = 1 ∧ ∀ t : ℝ, a*t < 0 ↔ σ*t < 0 := by
  rcases lt_or_gt_of_ne ha with haneg | hapos
  · refine ⟨-1,by norm_num,?_⟩
    intro t
    simp [mul_neg_iff,haneg,not_lt_of_ge haneg.le]
  · refine ⟨1,by norm_num,?_⟩
    intro t
    simp [mul_neg_iff,hapos,not_lt_of_ge hapos.le]

/-- A defining function from the supplied geometric-normal data produces an
actual coordinate boundary patch. The height is globally C²; the side and
frontier statements both hold on an open neighborhood of the base point. -/
theorem coordinate_boundary_graph_patch {n : ℕ} (Ω U : Opens (Domain (n+1)))
    {r : Domain (n+1) → ℝ} {x : Domain (n+1)} (hxU : x ∈ U)
    (hr : ContDiffOn ℝ 2 r U) (hz : r x = 0)
    (hside : ∀ y ∈ U, y ∈ Ω ↔ r y < 0)
    (hpos : 0 < ∑ k : Fin (n+1), (fderiv ℝ r x (coordinateVector k)) ^ 2) :
    ∃ (i : Fin (n+1)) (g : Domain n → ℝ) (σ : ℝ) (W : Opens (Domain (n+1))),
      x ∈ W ∧ g (i.removeNth x) = x i ∧ ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      σ ^ 2 = 1 ∧
      (∀ y ∈ W, y ∈ Ω ↔ σ * (y i - g (i.removeNth y)) < 0) ∧
      (∀ y ∈ W, y ∈ frontier (Ω : Set (Domain (n+1))) ↔ g (i.removeNth y) = y i) := by
  obtain ⟨i,g,ha,hgx,hg,hgc,_hzero,hsg⟩ := coordinate_implicit_graph_global_side
    (hr.contDiffAt (U.isOpen.mem_nhds hxU)) hz hpos
  obtain ⟨σ,hσ,hσneg⟩ := exists_unit_sign_same_neg ha
  have hlocal : ∀ᶠ y in 𝓝 x, y ∈ Ω ↔ σ * (y i - g (i.removeNth y)) < 0 := by
    filter_upwards [U.isOpen.mem_nhds hxU,hsg] with y hyU hys
    exact ((hside y hyU).trans hys).trans (hσneg _)
  obtain ⟨W,hsub,hWo,hxW⟩ := mem_nhds_iff.mp hlocal
  refine ⟨i,g,σ,⟨W,hWo⟩,hxW,hgx,hg,hgc,hσ,fun y hy => hsub hy,?_⟩
  let S : Set (Domain (n+1)) := {y | σ * (y i - g (i.removeNth y)) < 0}
  have hσne : σ ≠ 0 := by intro h; simp [h] at hσ
  have heq : (Ω : Set (Domain (n+1))) ∩ W = S ∩ W := by
    ext y
    exact and_congr_left fun hy => hsub hy
  have hf := inter_frontier_eq_of_inter_eq hWo heq
  intro y hy
  change y ∈ W at hy
  have hm : y ∈ frontier (Ω : Set (Domain (n+1))) ↔ y ∈ frontier S := by
    have hh : y ∈ frontier (Ω : Set (Domain (n+1))) ∩ W ↔ y ∈ frontier S ∩ W := by rw [hf]
    simpa only [mem_inter_iff,hy,and_true] using hh
  exact hm.trans (mem_frontier_coordinate_signed_graph i hg.continuous hσne y)

end ExpandedFA.SmoothBoundaryDivergence



noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Topology
namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions
namespace GraphFlux

/-- Flux in any constant product-space direction above a graph. -/
theorem integral_directional_above_graph {n : ℕ} {g : Domain n → ℝ}
    (hg : ContDiff ℝ 1 g) {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : Domain n × ℝ) :
    (∫ p in {p : Domain n × ℝ | g p.1 < p.2}, fderiv ℝ f p v) =
      ∫ x, f (x,g x) * (fderiv ℝ g x v.1 - v.2) := by
  have hd (p : Domain n × ℝ) : fderiv ℝ f p v =
      fderiv ℝ f p (v.1,0) + v.2 * fderiv ℝ f p (0,1) := by
    conv_lhs => rw [show v = (v.1,0) + v.2 • ((0,1) : Domain n × ℝ) by ext <;> simp]
    rw [map_add, map_smul, smul_eq_mul]
  simp_rw [hd]
  rw [integral_add (integrable_directional hf hc _).integrableOn
      (((integrable_directional hf hc _).const_mul v.2).integrableOn),
    integral_const_mul, integral_horizontal_derivative_above_graph hg hf hc,
    integral_vertical_derivative_above_graph hg.continuous hf hc]
  rw [show (fun x => f (x,g x) * (fderiv ℝ g x v.1 - v.2)) =
    (fun x => f (x,g x) * fderiv ℝ g x v.1 - v.2 * f (x,g x)) by ext x; ring]
  rw [integral_sub (integrable_weighted_graph_restriction hg hf.continuous hc _)
      ((integrable_graph_restriction hg.continuous hf.continuous hc).const_mul _), integral_const_mul]
  ring

/-- Reflection in the vertical coordinate. -/
def verticalReflection {n : ℕ} : (Domain n × ℝ) ≃ₜ (Domain n × ℝ) where
  toFun p := (p.1,-p.2)
  invFun p := (p.1,-p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk continuous_snd.neg
  continuous_invFun := continuous_fst.prodMk continuous_snd.neg

@[simp] theorem verticalReflection_apply {n : ℕ} (p : Domain n × ℝ) :
    verticalReflection p = (p.1,-p.2) := rfl

theorem verticalReflection_preserves_volume {n : ℕ} :
    MeasurePreserving (verticalReflection : (Domain n × ℝ) ≃ₜ _) volume volume := by
  rw [Measure.volume_eq_prod]
  exact (MeasurePreserving.id (volume : Measure (Domain n))).prod
    (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem contDiff_verticalReflection {n : ℕ} :
    ContDiff ℝ 1 (verticalReflection : (Domain n × ℝ) ≃ₜ _) :=
  contDiff_fst.prodMk contDiff_snd.neg

theorem fderiv_comp_verticalReflection {n : ℕ} {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (p v : Domain n × ℝ) :
    fderiv ℝ (f ∘ verticalReflection) p v =
      fderiv ℝ f (verticalReflection p) (v.1,-v.2) := by
  have hR := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).prodMk hasFDerivAt_snd.neg
  change HasFDerivAt (verticalReflection : (Domain n × ℝ) ≃ₜ _) _ p at hR
  rw [((hf.differentiable one_ne_zero _).hasFDerivAt.comp p hR).fderiv]
  rfl

/-- Flux in any constant product-space direction below a graph. -/
theorem integral_directional_below_graph {n : ℕ} {g : Domain n → ℝ}
    (hg : ContDiff ℝ 1 g) {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : Domain n × ℝ) :
    (∫ p in {p : Domain n × ℝ | p.2 < g p.1}, fderiv ℝ f p v) =
      ∫ x, f (x,g x) * (v.2 - fderiv ℝ g x v.1) := by
  have hF : ContDiff ℝ 1 (f ∘ verticalReflection) := hf.comp contDiff_verticalReflection
  have hFc : HasCompactSupport (f ∘ verticalReflection) := hc.comp_homeomorph verticalReflection
  have h := integral_directional_above_graph hg.neg hF hFc (v.1,-v.2)
  have he := (verticalReflection_preserves_volume (n := n)).setIntegral_preimage_emb
    verticalReflection.measurableEmbedding (fun p => fderiv ℝ f p v)
    {p : Domain n × ℝ | p.2 < g p.1}
  have hs : (verticalReflection : (Domain n × ℝ) ≃ₜ _) ⁻¹'
      {p : Domain n × ℝ | p.2 < g p.1} = {p : Domain n × ℝ | -g p.1 < p.2} := by
    ext p
    simp only [mem_preimage, verticalReflection_apply, mem_ofPred_eq]
    constructor <;> intro hp <;> linarith
  rw [hs] at he
  rw [← he]
  convert h using 1
  · apply setIntegral_congr_fun (isOpen_lt (hg.continuous.neg.comp continuous_fst) continuous_snd).measurableSet
    intro p _
    dsimp only
    rw [fderiv_comp_verticalReflection hf]
    simp
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      dsimp only
      rw [fderiv_fun_neg]
      simp only [Function.comp_apply, verticalReflection_apply, neg_neg, neg_apply]
      ring

/-- The orientation coefficient can be any nonzero real number: only its
sign enters the graph flux. This matches the implicit-function extraction. -/
theorem integral_directional_oriented_graph {n : ℕ} {g : Domain n → ℝ}
    (hg : ContDiff ℝ 1 g) {f : Domain n × ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : Domain n × ℝ)
    {a : ℝ} (ha : a ≠ 0) :
    (∫ p in {p : Domain n × ℝ | a * (p.2-g p.1) < 0}, fderiv ℝ f p v) =
      ∫ x, f (x,g x) * (a / |a|) * (v.2 - fderiv ℝ g x v.1) := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hs : {p : Domain n × ℝ | a * (p.2-g p.1) < 0} =
        {p : Domain n × ℝ | g p.1 < p.2} := by
      ext p
      simp only [mem_ofPred_eq, mul_neg_iff]
      constructor
      · rintro (⟨_,h⟩ | ⟨h,_⟩)
        · linarith
        · linarith
      · intro hp
        exact Or.inr ⟨hneg,sub_pos.mpr hp⟩
    rw [hs, integral_directional_above_graph hg hf hc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      rw [abs_of_neg hneg, div_neg, div_self ha]
      ring
  · have hs : {p : Domain n × ℝ | a * (p.2-g p.1) < 0} =
        {p : Domain n × ℝ | p.2 < g p.1} := by
      ext p
      rw [mem_ofPred_eq, mem_ofPred_eq, mul_neg_iff]
      constructor
      · rintro (⟨_,h⟩ | ⟨h,_⟩)
        · exact sub_neg.mp h
        · linarith
      · intro hp
        exact Or.inl ⟨hpos, sub_neg.mpr hp⟩
    rw [hs, integral_directional_below_graph hg hf hc]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by simp only [abs_of_pos hpos, div_self ha, mul_one]

end GraphFlux

/-- A locally valid oriented graph description suffices for the domain flux
when the test function is supported inside that graph neighborhood. The
coordinate insertion volume identity is a separate transport input. -/
theorem local_oriented_coordinate_graph_flux {n : ℕ} (i : Fin (n+1))
    (he : MeasurePreserving (insertCoordinate i) volume volume)
    (Ω : Opens (Domain (n+1))) (W : Set (Domain (n+1)))
    {g : Domain n → ℝ} (hg : ContDiff ℝ 1 g)
    {a : ℝ} (ha : a ≠ 0)
    (hside : ∀ y ∈ W, y ∈ Ω ↔ a * (y i - g (i.removeNth y)) < 0)
    {f : Domain (n+1) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ W) (v : Domain (n+1)) :
    (∫ y in (Ω : Set (Domain (n+1))), fderiv ℝ f y v) =
      ∫ z, f (i.insertNth (g z) z) * (a / |a|) *
        (v i - fderiv ℝ g z (i.removeNth v)) := by
  classical
  let e := insertCoordinate i
  let F := f ∘ e
  let V := e.symm v
  have hF : ContDiff ℝ 1 F := hf.comp e.contDiff
  have hFc : HasCompactSupport F := hc.comp_homeomorph e.toHomeomorph
  have hd (p : Domain n × ℝ) : fderiv ℝ F p V = fderiv ℝ f (e p) v := by
    rw [((hf.differentiable one_ne_zero _).hasFDerivAt.comp p e.hasFDerivAt).fderiv]
    simp only [ContinuousLinearMap.comp_apply]
    change fderiv ℝ f (e p) (e (e.symm v)) = _
    rw [e.apply_symm_apply]
  have hp := he.setIntegral_preimage_emb e.toHomeomorph.measurableEmbedding
    (fun y => fderiv ℝ f y v) (Ω : Set (Domain (n+1)))
  rw [← hp]
  have hΩ : MeasurableSet (e ⁻¹' (Ω : Set (Domain (n+1)))) :=
    Ω.isOpen.measurableSet.preimage e.continuous.measurable
  have hG : MeasurableSet {p : Domain n × ℝ | a * (p.2-g p.1) < 0} :=
    (isOpen_lt (continuous_const.mul (continuous_snd.sub (hg.continuous.comp continuous_fst)))
      continuous_const).measurableSet
  calc
    _ = ∫ p in {p : Domain n × ℝ | a * (p.2-g p.1) < 0}, fderiv ℝ F p V := by
      rw [← integral_indicator hΩ, ← integral_indicator hG]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        change (if e p ∈ Ω then fderiv ℝ f (e p) v else 0) =
          (if a * (p.2-g p.1) < 0 then fderiv ℝ F p V else 0)
        by_cases hw : e p ∈ W
        · have hh := hside (e p) hw
          have hcoord : (e p) i = p.2 ∧ i.removeNth (e p) = p.1 := by simp [e]
          rw [hcoord.1,hcoord.2] at hh
          rw [← hd p]
          exact if_congr hh rfl rfl
        · have hz : fderiv ℝ f (e p) v = 0 :=
            image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ f y v)
              (fun h => hw (hsupp (tsupport_fderiv_apply_subset ℝ v h)))
          rw [hd p,hz]
          split_ifs <;> rfl
    _ = _ := by
      simpa only [F, Function.comp_apply, e, insertCoordinate_apply, V,
        insertCoordinate_symm_apply] using
        GraphFlux.integral_directional_oriented_graph hg hF hFc V ha


@[simp] theorem removeNth_coordinateVector_self {n : ℕ} (i : Fin (n+1)) :
    i.removeNth (coordinateVector i) = (0 : Domain n) := by
  ext k
  simp [coordinateVector, Fin.removeNth]

@[simp] theorem removeNth_coordinateVector_succAbove {n : ℕ} (i : Fin (n+1)) (k : Fin n) :
    i.removeNth (coordinateVector (i.succAbove k)) = coordinateVector k := by
  ext l
  simp [coordinateVector, Fin.removeNth, Pi.single_apply]

/-- With a unit orientation, vertical coordinate flux has exactly that sign. -/
theorem local_signed_vertical_coordinate_graph_flux {n : ℕ} (i : Fin (n+1))
    (he : MeasurePreserving (insertCoordinate i) volume volume)
    (Ω : Opens (Domain (n+1))) (W : Set (Domain (n+1)))
    {g : Domain n → ℝ} (hg : ContDiff ℝ 1 g)
    {σ : ℝ} (hσ : σ ^ 2 = 1)
    (hside : ∀ y ∈ W, y ∈ Ω ↔ σ * (y i - g (i.removeNth y)) < 0)
    {f : Domain (n+1) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ W) :
    (∫ y in (Ω : Set (Domain (n+1))), fderiv ℝ f y (coordinateVector i)) =
      ∫ z, f (i.insertNth (g z) z) * σ := by
  have hσne : σ ≠ 0 := by intro h; simp [h] at hσ
  have habs : |σ| = 1 := by
    rcases sq_eq_one_iff.mp hσ with h | h <;> simp [h]
  have hci : coordinateVector i i = 1 := by simp [coordinateVector]
  simpa only [habs, div_one, hci,
    removeNth_coordinateVector_self, map_zero, sub_zero, mul_one] using
    local_oriented_coordinate_graph_flux i he Ω W hg hσne hside hf hc hsupp (coordinateVector i)

/-- Tangential coordinate flux carries the negative oriented graph derivative. -/
theorem local_signed_horizontal_coordinate_graph_flux {n : ℕ} (i : Fin (n+1))
    (he : MeasurePreserving (insertCoordinate i) volume volume)
    (Ω : Opens (Domain (n+1))) (W : Set (Domain (n+1)))
    {g : Domain n → ℝ} (hg : ContDiff ℝ 1 g)
    {σ : ℝ} (hσ : σ ^ 2 = 1)
    (hside : ∀ y ∈ W, y ∈ Ω ↔ σ * (y i - g (i.removeNth y)) < 0)
    {f : Domain (n+1) → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (hsupp : tsupport f ⊆ W) (k : Fin n) :
    (∫ y in (Ω : Set (Domain (n+1))), fderiv ℝ f y (coordinateVector (i.succAbove k))) =
      ∫ z, f (i.insertNth (g z) z) * (- (σ * fderiv ℝ g z (coordinateVector k))) := by
  have hσne : σ ≠ 0 := by intro h; simp [h] at hσ
  have habs : |σ| = 1 := by
    rcases sq_eq_one_iff.mp hσ with h | h <;> simp [h]
  rw [local_oriented_coordinate_graph_flux i he Ω W hg hσne hside hf hc hsupp]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    rw [habs, div_one, removeNth_coordinateVector_succAbove]
    have hz : coordinateVector (i.succAbove k) i = 0 := by simp [coordinateVector]
    rw [hz]
    ring

end ExpandedFA.SmoothBoundaryDivergence


noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped Topology ENNReal
namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions ExpandedFA.Sobolev

/-- Exact outward graph flux for every supplied geometric normal on a local
patch. The function only has to vanish outside that patch. -/
theorem integral_supplied_normal_on_graph_patch {n : ℕ}
    (Ω W : Opens (Domain (n+1))) (i : Fin (n+1))
    {g : Domain n → ℝ} (hg : ContDiff ℝ 1 g)
    {ν : Fin (n+1) → Domain (n+1) → ℝ}
    (hν : ∀ x ∈ frontier (Ω : Set (Domain (n+1))), ∃ (U : Opens (Domain (n+1))) (r : Domain (n+1) → ℝ),
      x ∈ U ∧ ContDiffOn ℝ 2 r U ∧ r x = 0 ∧
      (∀ y ∈ U, y ∈ Ω ↔ r y < 0) ∧
      0 < ∑ k : Fin (n+1), (fderiv ℝ r x (coordinateVector k)) ^ 2 ∧
      ∀ j, ν j x = fderiv ℝ r x (coordinateVector j) /
        Real.sqrt (∑ k : Fin (n+1), (fderiv ℝ r x (coordinateVector k)) ^ 2))
    (σ : ℝ) (hσ : σ ^ 2 = 1)
    (hside : ∀ y ∈ W, y ∈ Ω ↔ σ * (y i - g (i.removeNth y)) < 0)
    (hfront : ∀ y ∈ W, y ∈ frontier (Ω : Set (Domain (n+1))) ↔
      g (i.removeNth y) = y i)
    {f : Domain (n+1) → ℝ} (hf : Continuous f) (hsupport : tsupport f ⊆ W) :
    (∫ y, f y * ν i y ∂Trace.surfaceMeasure Ω) =
      σ * ∫ z, f (i.insertNth (g z) z) ∂volume ∧
    ∀ k : Fin n, (∫ y, f y * ν (i.succAbove k) y ∂Trace.surfaceMeasure Ω) =
      (-σ) * ∫ z, f (i.insertNth (g z) z) *
        fderiv ℝ g z (coordinateVector k) ∂volume := by
  let J := fun z : Domain n =>
    Real.sqrt (1 + ∑ k : Fin n, (fderiv ℝ g z (coordinateVector k)) ^ 2)
  let Γ : Domain n → Domain (n+1) := fun z => i.insertNth (g z) z
  have hD : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hJ : Continuous J := by dsimp [J]; fun_prop
  have hJpos (z : Domain n) : 0 < J z := by dsimp [J]; positivity
  have hremove : Continuous (i.removeNth : Domain (n+1) → Domain n) :=
    continuous_pi (fun k => continuous_apply (i.succAbove k))
  have hnorm (y : Domain (n+1)) (hyfront : y ∈ frontier (Ω : Set (Domain (n+1))))
      (hyW : y ∈ W) :
      ν i y = σ / J (i.removeNth y) ∧
        ∀ k : Fin n, ν (i.succAbove k) y =
          -(σ * fderiv ℝ g (i.removeNth y) (coordinateVector k)) / J (i.removeNth y) := by
    apply supplied_normal_eq_oriented_graph Ω (hν y hyfront) i
      (hg.differentiable one_ne_zero _) ((hfront y hyW).mp hyfront) σ hσ
    filter_upwards [W.isOpen.mem_nhds hyW] with z hzW
    exact hside z hzW
  have hbridge (j : Fin (n+1)) (H : Domain (n+1) → ℝ) (hH : Measurable H)
      (heq : ∀ y ∈ frontier (Ω : Set (Domain (n+1))), y ∈ W → ν j y = H y) :
      (∫ y, f y * ν j y ∂Trace.surfaceMeasure Ω) =
        ∫ z, J z * (f (Γ z) * H (Γ z)) ∂volume := by
    calc
      _ = ∫ y, f y * H y ∂Trace.surfaceMeasure Ω := by
        apply integral_congr_ae
        filter_upwards [Trace.surfaceMeasure_ae_frontier Ω] with y hyfront
        by_cases hyW : y ∈ W
        · rw [heq y hyfront hyW]
        · have hfzero : f y = 0 := image_eq_zero_of_notMem_tsupport
            (fun hy => hyW (hsupport hy))
          simp only [hfzero, zero_mul]
      _ = _ := by
        apply integral_surface_eq_coordinate_graph_integral Ω W i hg hfront
          (fun y => f y * H y) (hf.measurable.mul hH)
        intro y hy
        apply hsupport
        apply subset_tsupport
        exact (mul_ne_zero_iff.mp hy).1
  constructor
  · let H := fun y : Domain (n+1) => σ / J (i.removeNth y)
    have hH : Measurable H := measurable_const.div (hJ.measurable.comp hremove.measurable)
    rw [hbridge i H hH (fun y hy hyW => (hnorm y hy hyW).1)]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      have hJne := ne_of_gt (hJpos z)
      dsimp [H, Γ]
      simp only [Fin.removeNth_insertNth]
      field_simp
  · intro k
    let H := fun y : Domain (n+1) =>
      -(σ * fderiv ℝ g (i.removeNth y) (coordinateVector k)) / J (i.removeNth y)
    have hH : Measurable H := by
      apply Measurable.div _ (hJ.measurable.comp hremove.measurable)
      exact (measurable_const.mul ((hD.clm_apply continuous_const).measurable.comp
        hremove.measurable)).neg
    rw [hbridge (i.succAbove k) H hH (fun y hy hyW => (hnorm y hy hyW).2 k)]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      have hJne := ne_of_gt (hJpos z)
      dsimp [H, Γ]
      simp only [Fin.removeNth_insertNth]
      field_simp

end ExpandedFA.SmoothBoundaryDivergence

namespace ExpandedFA.SmoothBoundaryDivergence
open ExpandedFA.Distributions ExpandedFA.Sobolev

/-- The compact real smooth divergence theorem for the original coordinate
space, normalized surface measure, and every supplied geometric normal. -/
theorem compact_real_smooth_divergence :
    Specs.ExpandedFA.PartIV.SmoothBoundaryDivergence.CompactRealSmoothDivergence := by
  intro d Ω hbounded hcharts ν hν hνbound hνgeom f hf hcompact j
  cases d with
  | zero => exact Fin.elim0 j
  | succ n =>
    apply coordinate_divergence_of_boundary_local Ω hbounded
      (isC1Domain_of_c2_charts Ω hcharts) ν hν hνbound j ?_ hf hcompact
    intro x hx
    obtain ⟨U,r,hxU,hr,hzero,hside,hpos,_⟩ := hνgeom x hx
    obtain ⟨i,g,σ,W,hxW,_hgx,hg,_hgc,hσ,hgraphside,hfront⟩ :=
      coordinate_boundary_graph_patch Ω U hxU hr hzero hside hpos
    refine ⟨W,hxW,?_⟩
    intro F hF hFc hFsupp
    have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
    have hF1 : ContDiff ℝ 1 F := hF.of_le (by simp)
    obtain ⟨hvertical,hhorizontal⟩ := integral_supplied_normal_on_graph_patch Ω W i hg1
      hνgeom σ hσ hgraphside hfront hF.continuous hFsupp
    refine i.succAboveCases ?_ (fun k => ?_) j
    · rw [local_signed_vertical_coordinate_graph_flux i (insertCoordinate_preserves_volume i)
        Ω W hg1 hσ hgraphside hF1 hFc hFsupp, hvertical, integral_mul_const]
      exact mul_comm _ _
    · rw [local_signed_horizontal_coordinate_graph_flux i (insertCoordinate_preserves_volume i)
        Ω W hg1 hσ hgraphside hF1 hFc hFsupp k, hhorizontal k, ← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring

end ExpandedFA.SmoothBoundaryDivergence
