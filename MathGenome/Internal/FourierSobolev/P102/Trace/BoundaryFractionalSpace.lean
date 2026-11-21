import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.BoundaryFractionalSpace
import MathGenome.Internal.FourierSobolev.P102.Sobolev.LipschitzGeometry
import MathGenome.Internal.FourierSobolev.P102.Fractional.Space
import MathGenome.Internal.FourierSobolev.P102.Trace.BoundaryChartLocalization
import MathGenome.Internal.FourierSobolev.P102.Trace.BoundaryPatchExtension
import Mathlib.Analysis.Complex.Basic

noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace P102.Trace.BoundaryFractional
open P102.U4.GraphPieces P102.Sobolev.Geometry

variable {m : ℕ} {𝕜 : Type*} [RCLike 𝕜]
variable {Ω : Set (Ambient m)} {s : ℝ} {p : ℝ≥0∞}

/-- The intrinsic integral depends only on the surface a.e. class. This proof
works directly with the iterated integral and needs no product-measure finiteness. -/
theorem energy_congr {g h : Ambient m → 𝕜} (hgh : g =ᵐ[surfaceMeasure Ω] h) :
    energy Ω s p g = energy Ω s p h := by
  apply lintegral_congr_ae
  filter_upwards [hgh] with x hx
  apply lintegral_congr_ae
  filter_upwards [hgh] with y hy
  simp only [hx, hy]

theorem seminorm_congr {g h : Ambient m → 𝕜} (hgh : g =ᵐ[surfaceMeasure Ω] h) :
    seminorm Ω s p g = seminorm Ω s p h := by
  unfold seminorm
  rw [energy_congr hgh]

theorem intrinsicNorm_congr {g h : Ambient m → 𝕜} (hgh : g =ᵐ[surfaceMeasure Ω] h) :
    intrinsicNorm Ω s p g = intrinsicNorm Ω s p h := by
  unfold intrinsicNorm
  rw [eLpNorm_congr_ae hgh, seminorm_congr hgh]

theorem intrinsic_representative_independence : Expected.IntrinsicRepresentativeIndependence := by
  intro m 𝕜 _ Ω s p g h hgh
  exact ⟨energy_congr hgh, seminorm_congr hgh, intrinsicNorm_congr hgh⟩

/-- The extended norm is finite exactly on the stated intrinsic space. -/
theorem mem_space_iff (g : Lp 𝕜 p (surfaceMeasure Ω)) :
    g ∈ space 𝕜 Ω s p ↔ intrinsicNorm Ω s p (g : Ambient m → 𝕜) < ⊤ := by
  change seminorm Ω s p (g : Ambient m → 𝕜) < ⊤ ↔ _
  simp only [intrinsicNorm, ENNReal.add_lt_top, Lp.eLpNorm_lt_top, true_and]

theorem norm_formula : Expected.NormFormula := by
  intro m 𝕜 _ Ω s p _ g
  rw [spaceNorm, ENNReal.ofReal_add (norm_nonneg _) ENNReal.toReal_nonneg,
    Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _),
    ENNReal.ofReal_toReal g.property.ne]
  rfl

/-- Discard the interior piece of the upstream ambient partition: it vanishes
on the boundary because its topological support lies in the open set. -/
theorem atlas_exists (m : ℕ) (Ω : Set (Ambient m)) (hΩ : IsLipschitzOpen Ω) :
    Nonempty (Atlas Ω) := by
  classical
  obtain ⟨n, C, r, a, hsmall, hcover, V, χ, hVo, hΩV, hχ, hsum, hsupp0, hsep, hsupp⟩ :=
    finite_localization m Ω hΩ
  refine ⟨⟨n, C, r, a, hsmall, hcover, (fun i => χ i.succ),
    (fun i => (hχ i.succ).1), (fun i => (hχ i.succ).2.1),
    (fun i => (hχ i.succ).2.2), ?_, hsupp⟩⟩
  intro x hx
  have hx0 : χ 0 x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    exact (Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hΩ.1)) hx (hsupp0 hxs)
  have hxV := hΩV (frontier_subset_closure hx)
  simpa only [Fin.sum_univ_succ, hx0, zero_add] using hsum x hxV

/-- Even arbitrary nonmeasurable surface-null sets have null preimages on a
chart base. The proof uses the lower outer-measure distortion estimate. -/
theorem graphMap_preimage_null (C : BoundaryChart Ω) {N : Set (Ambient m)}
    (hN : surfaceMeasure Ω N = 0) :
    volume (graphMap C ⁻¹' N ∩ ball C.center C.radius) = 0 := by
  let S := graphMap C ⁻¹' N ∩ ball C.center C.radius
  have hlower := (graph_geometry_in_frame m (ball C.center C.radius)
    C.graphFunction C.constant C.graph_lipschitz C.frame).2.2 S inter_subset_right
  have hi : graphMap C '' S ⊆ N ∩ frontier Ω := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨hx.1, ?_⟩
    have hh : graphMap C x ∈ C.frame '' (graph C.graphFunction '' ball C.center C.radius) :=
      ⟨graph C.graphFunction x, ⟨x, hx.2, rfl⟩, rfl⟩
    rw [← C.boundary] at hh
    exact hh.1
  have hN' : (μHE[m] : Measure (Ambient m)) (N ∩ frontier Ω) = 0 := by
    simpa only [surfaceMeasure, Measure.restrict_apply' isClosed_frontier.measurableSet] using hN
  apply le_antisymm _ bot_le
  calc
    volume S ≤ (μHE[m] : Measure (Ambient m)) (graphMap C '' S) := hlower.1
    _ ≤ (μHE[m] : Measure (Ambient m)) (N ∩ frontier Ω) := measure_mono hi
    _ = 0 := hN'

/-- Zero extension is essential here: outside the base both pullbacks are zero. -/
theorem localizedPullback_congr (A : Atlas Ω) (i : Fin A.count)
    {g h : Ambient m → 𝕜} (hgh : g =ᵐ[surfaceMeasure Ω] h) :
    localizedPullback A i g =ᵐ[volume] localizedPullback A i h := by
  classical
  have hnull := graphMap_preimage_null (A.chart i) (ae_iff.mp hgh)
  have heq : ∀ᵐ x ∂volume, x ∉ graphMap (A.chart i) ⁻¹' {z | ¬ g z = h z} ∩
      ball (A.chart i).center (A.chart i).radius := by
    exact measure_eq_zero_iff_ae_notMem.mp hnull
  filter_upwards [heq] with x hx
  by_cases hxb : x ∈ ball (A.chart i).center (A.chart i).radius
  · have hxgh : g (graphMap (A.chart i) x) = h (graphMap (A.chart i) x) := by
      by_contra hneq
      exact hx ⟨hneq, hxb⟩
    simp only [localizedPullback, ite_eq_left hxb, hxgh]
  · simp only [localizedPullback, ite_eq_right hxb]

theorem chartNorm_congr (A : Atlas Ω) {g h : Ambient m → 𝕜}
    (hgh : g =ᵐ[surfaceMeasure Ω] h) : chartNorm A s p g = chartNorm A s p h := by
  unfold chartNorm
  apply Finset.sum_congr rfl
  intro i hi
  have heq := localizedPullback_congr A i hgh
  rw [eLpNorm_congr_ae heq, P102.Fractional.seminorm_congr (by
    simpa only [P102.Fractional.domainMeasure, Measure.restrict_univ] using heq)]

theorem chart_representative_independence : Expected.ChartRepresentativeIndependence := by
  intro m 𝕜 _ Ω A g h hgh
  exact ⟨fun i => localizedPullback_congr A i hgh, fun s p => chartNorm_congr A hgh⟩

/-- A bounded Lipschitz boundary has finite normalized surface measure. -/
theorem surfaceMeasure_finite (hΩ : IsLipschitzOpen Ω) :
    surfaceMeasure Ω Set.univ < ⊤ := by
  classical
  obtain ⟨A⟩ := atlas_exists m Ω hΩ
  let S : Fin A.count → Set (Ambient m) := fun i =>
    graphMap (A.chart i) '' ball (A.chart i).center (A.chart i).radius
  have hcov : frontier Ω ⊆ ⋃ i, S i := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (A.cover hx)
    have hsmall := (A.smaller i)
    have hfull := chartImage_mono (A.chart i).frame (A.chart i).graphFunction
      (A.chart i).center hsmall.2.1.le hsmall.2.2.2.le hi
    have hf : x ∈ frontier Ω ∩ chartImage (A.chart i).frame
        (A.chart i).graphFunction (A.chart i).center
        (A.chart i).radius (A.chart i).height := ⟨hx, hfull⟩
    rw [(A.chart i).boundary] at hf
    rcases hf with ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact mem_iUnion.mpr ⟨i, ⟨y, hy, rfl⟩⟩
  rw [surfaceMeasure, Measure.restrict_apply_univ]
  apply (measure_mono hcov).trans_lt
  apply (measure_iUnion_fintype_le _ S).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro i hi
  have hle := ((graph_geometry_in_frame m (ball (A.chart i).center (A.chart i).radius)
    (A.chart i).graphFunction (A.chart i).constant (A.chart i).graph_lipschitz
    (A.chart i).frame).2.2 _ Subset.rfl).2
  apply hle.trans_lt
  exact ENNReal.mul_lt_top (by simp) measure_ball_lt_top

/-- The support of a localized pullback is inside the smaller tangential ball,
even though the formula uses the full chart base. -/
theorem localizedPullback_eq_zero_off_smaller (A : Atlas Ω) (i : Fin A.count)
    (g : Ambient m → 𝕜) {x : P102.U4.Space m}
    (hx : x ∉ ball (A.chart i).center (A.radius i)) :
    localizedPullback A i g x = 0 := by
  classical
  unfold localizedPullback
  split_ifs with hxb
  · have hz : A.cutoff i (graphMap (A.chart i) x) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro ht
      obtain ⟨_, ⟨z, hz, rfl⟩, heq⟩ := A.support_subset i ht
      have heq' := (A.chart i).frame.injective heq
      have hfirst := congrArg (fun w : Ambient m => w.ofLp.1) heq'
      change z.ofLp.1 = x at hfirst
      exact hx (hfirst ▸ hz.1)
    rw [hz, zero_smul]
  · rfl

/-- The smaller radius provides an explicit positive artificial-edge gap. -/
theorem localizedPullback_supportedAway (A : Atlas Ω) (i : Fin A.count)
    (g : Ambient m → 𝕜) :
    P102.Fractional.SupportedAway
      (ball (A.chart i).center (A.chart i).radius) Set.univ
      ((A.chart i).radius - A.radius i) (localizedPullback A i g) := by
  apply Filter.Eventually.of_forall
  intro x hx y hy
  have hxs : x ∈ ball (A.chart i).center (A.radius i) := by
    by_contra hnot
    exact hx (localizedPullback_eq_zero_off_smaller A i g hnot)
  have hyb : (A.chart i).radius ≤ dist y (A.chart i).center := by
    simpa only [mem_ball, not_lt] using hy.2
  have hxb : dist x (A.chart i).center < A.radius i := hxs
  have ht := dist_triangle y x (A.chart i).center
  rw [dist_comm y x] at ht
  linarith

/-- The physical pieces reconstruct every representative pointwise on ∂Ω. -/
theorem partition_reconstruction (A : Atlas Ω) (g : Ambient m → 𝕜)
    {x : Ambient m} (hx : x ∈ frontier Ω) :
    ∑ i, A.cutoff i x • g x = g x := by
  rw [← Finset.sum_smul, A.sum_eq_one x hx, one_smul]


/-- The measured metric norm is exactly the intrinsic formula, in ambient
Euclidean coordinates. -/
theorem metricNorm_eq_intrinsicNorm (g : Ambient m → 𝕜) :
    MeasuredFractional.metricNorm m (surfaceMeasure Ω) s p g = intrinsicNorm Ω s p g := by
  simp only [MeasuredFractional.metricNorm, MeasuredFractional.metricSeminorm,
    MeasuredFractional.metricEnergy, intrinsicNorm, seminorm, energy, dist_eq_norm]

/-- The chart summands use the full tangential space. -/
theorem chartNorm_eq_metricNorm_sum (A : Atlas Ω) (g : Ambient m → 𝕜) :
    chartNorm A s p g = ∑ i,
      MeasuredFractional.metricNorm m volume s p (localizedPullback A i g) := by
  unfold chartNorm
  apply Finset.sum_congr rfl
  intro i _
  simpa only [P102.Fractional.domainMeasure, Measure.restrict_univ] using
    (BoundaryChartLocalization.metricNorm_euclidean Set.univ s p
      (localizedPullback A i g)).symm

/-- Smooth compactly supported partition factors preserve Lp membership. -/
theorem cutoff_memLp (A : Atlas Ω) (i : Fin A.count) {g : Ambient m → 𝕜}
    (hg : MemLp g p (surfaceMeasure Ω)) :
    MemLp (fun x => A.cutoff i x • g x) p (surfaceMeasure Ω) := by
  obtain ⟨M, hM⟩ := (A.compact i).exists_bound_of_continuous (A.smooth i).continuous
  apply hg.of_le_mul (c := M) ((A.smooth i).continuous.aestronglyMeasurable.smul hg.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    change ‖A.cutoff i x • g x‖ ≤ M * ‖g x‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)

/-- Assembly of the analytic patch estimates. The constants are fixed before
choosing either the scalar field or the representative. -/
theorem norm_comparison_small
    (m : ℕ) (hm : 1 ≤ m) (Ω : Set (Ambient m)) (hΩ : IsLipschitzOpen Ω)
    (A : Atlas Ω) (s : ℝ) (hs : 0 < s) (hs1 : s < 1)
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (hpt : p ≠ ⊤) :
    ∃ C D : ℝ≥0, 0 < C ∧ 0 < D ∧
      ∀ {𝕜 : Type} [RCLike 𝕜] (g : Ambient m → 𝕜), MemLp g p (surfaceMeasure Ω) →
        chartNorm A s p g ≤ (C : ℝ≥0∞) * intrinsicNorm Ω s p g ∧
        intrinsicNorm Ω s p g ≤ (D : ℝ≥0∞) * chartNorm A s p g := by
  classical
  have hp : 1 ≤ p := Fact.out
  have hpfin : p < ⊤ := lt_top_iff_ne_top.mpr hpt
  have hf (i : Fin A.count) := BoundaryChartLocalization.localized_estimate m hm Ω hΩ
    (A.chart i) (A.radius i) (A.height i) (A.smaller i).1 (A.smaller i).2.1
    (A.smaller i).2.2.1 (A.smaller i).2.2.2 (A.cutoff i)
    (A.smooth i) (A.compact i) (A.support_subset i) s hs hs1 p hp hpfin
  choose F hFpos hF using hf
  have hr (i : Fin A.count) := BoundaryPatchExtension.patch_extension_bound m hm Ω hΩ
    (A.chart i) (tsupport (A.cutoff i)) (A.compact i)
    (fun x hx => chartImage_mono (A.chart i).frame (A.chart i).graphFunction
      (A.chart i).center (A.smaller i).2.1.le (A.smaller i).2.2.2.le
      (A.support_subset i hx)) s hs hs1 p hp hpfin
  choose R hRpos hR using hr
  let C : ℝ≥0 := (∑ i, F i) + 1
  let D : ℝ≥0 := (∑ i, R i) + 1
  refine ⟨C, D, by dsimp [C]; positivity, by dsimp [D]; positivity, ?_⟩
  intro 𝕜 _ g hg
  have hforward (i : Fin A.count) :
      MeasuredFractional.metricNorm m volume s p (localizedPullback A i g) ≤
        (F i : ℝ≥0∞) * intrinsicNorm Ω s p g := by
    have hb := (hF i 𝕜 g hg).2
    change MeasuredFractional.metricNorm m volume s p (localizedPullback A i g) ≤
      (F i : ℝ≥0∞) * MeasuredFractional.metricNorm m (surfaceMeasure Ω) s p g at hb
    simpa only [metricNorm_eq_intrinsicNorm] using hb
  have hreverse (i : Fin A.count) :
      intrinsicNorm Ω s p (fun x => A.cutoff i x • g x) ≤
        (R i : ℝ≥0∞) * MeasuredFractional.metricNorm m volume s p (localizedPullback A i g) := by
    have hsupp : ∀ᵐ x ∂BoundaryPatchExtension.surfaceMeasure Ω,
        x ∉ tsupport (A.cutoff i) → A.cutoff i x • g x = 0 :=
      Filter.Eventually.of_forall fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport hx, zero_smul]
    have hb := (hR i 𝕜 (fun x => A.cutoff i x • g x) (cutoff_memLp A i hg) hsupp).2
    have heq : BoundaryPatchExtension.pullback (A.chart i) (fun x => A.cutoff i x • g x) =
        localizedPullback A i g := by
      funext x
      simp only [BoundaryPatchExtension.pullback, Set.indicator_apply, Function.comp_apply,
        GraphFractionalTransport.graphMap, localizedPullback, graphMap]
    rw [heq] at hb
    change MeasuredFractional.metricNorm m (surfaceMeasure Ω) s p
      (fun x => A.cutoff i x • g x) ≤ (R i : ℝ≥0∞) *
        MeasuredFractional.metricNorm m volume s p (localizedPullback A i g) at hb
    simpa only [metricNorm_eq_intrinsicNorm] using hb
  constructor
  · rw [chartNorm_eq_metricNorm_sum]
    calc
      _ ≤ ∑ i, (F i : ℝ≥0∞) * intrinsicNorm Ω s p g := Finset.sum_le_sum fun i _ => hforward i
      _ = ((∑ i, F i : ℝ≥0) : ℝ≥0∞) * intrinsicNorm Ω s p g := by
        simp [← Finset.sum_mul]
      _ ≤ (C : ℝ≥0∞) * intrinsicNorm Ω s p g := by
        gcongr
        exact le_self_add
  · let : IsFiniteMeasure (surfaceMeasure Ω) := ⟨surfaceMeasure_finite hΩ⟩
    have heq : (∑ i, fun x => A.cutoff i x • g x) =ᵐ[surfaceMeasure Ω] g := by
      filter_upwards [ae_restrict_mem isClosed_frontier.measurableSet] with x hx
      simpa only [Finset.sum_apply] using partition_reconstruction A g hx
    rw [← intrinsicNorm_congr heq, ← metricNorm_eq_intrinsicNorm]
    calc
      _ ≤ ∑ i, MeasuredFractional.metricNorm m (surfaceMeasure Ω) s p
          (fun x => A.cutoff i x • g x) :=
        MeasuredFractional.metricNorm_sum_le hp hpt Finset.univ _ (fun i _ => cutoff_memLp A i hg)
      _ = ∑ i, intrinsicNorm Ω s p (fun x => A.cutoff i x • g x) := by
        simp only [metricNorm_eq_intrinsicNorm]
      _ ≤ ∑ i, (R i : ℝ≥0∞) *
          MeasuredFractional.metricNorm m volume s p (localizedPullback A i g) :=
        Finset.sum_le_sum fun i _ => hreverse i
      _ ≤ ∑ i, (D : ℝ≥0∞) *
          MeasuredFractional.metricNorm m volume s p (localizedPullback A i g) := by
        apply Finset.sum_le_sum
        intro i _
        gcongr
        exact (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ i)).trans le_self_add
      _ = (D : ℝ≥0∞) * chartNorm A s p g := by
        rw [chartNorm_eq_metricNorm_sum, Finset.mul_sum]


section ScalarIsometries
variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The extended Lp convention, including nonmeasurable functions, is invariant
under a linear isometric embedding. -/
theorem eLpNorm_linearIsometry (f : E →ₗᵢ[ℝ] F) (μ : Measure X)
    (p : ℝ≥0∞) (g : X → E) : eLpNorm (f ∘ g) p μ = eLpNorm g p μ := by
  have hm := f.isometry.isEmbedding.aestronglyMeasurable_comp_iff (f := g) (μ := μ)
  by_cases hg : AEStronglyMeasurable g μ
  · exact eLpNorm_congr_norm_ae (hm.mpr hg) hg
      (Filter.Eventually.of_forall fun x => f.norm_map (g x))
  · have hfg : ¬ AEStronglyMeasurable (f ∘ g) μ := fun h => hg (hm.mp h)
    rw [eLpNorm_of_not_aestronglyMeasurable hg,
      eLpNorm_of_not_aestronglyMeasurable hfg]

/-- Both the mass and the increment formula respect scalar isometries. -/
theorem metricNorm_linearIsometry [MetricSpace X] (f : E →ₗᵢ[ℝ] F)
    (m : ℕ) (μ : Measure X) (s : ℝ) (p : ℝ≥0∞) (g : X → E) :
    MeasuredFractional.metricNorm m μ s p (f ∘ g) =
      MeasuredFractional.metricNorm m μ s p g := by
  simp only [MeasuredFractional.metricNorm, eLpNorm_linearIsometry,
    MeasuredFractional.metricSeminorm, MeasuredFractional.metricEnergy,
    Function.comp_apply, ← f.map_sub, f.enorm_map]
end ScalarIsometries

/-- Localization commutes with the real-linear scalar embedding. -/
theorem localizedPullback_linearIsometry {𝕜' : Type*} [RCLike 𝕜']
    (f : 𝕜 →ₗᵢ[ℝ] 𝕜') (A : Atlas Ω) (i : Fin A.count) (g : Ambient m → 𝕜) :
    localizedPullback A i (f ∘ g) = f ∘ localizedPullback A i g := by
  classical
  funext x
  simp only [localizedPullback, Function.comp_apply]
  split_ifs <;> simp only [f.map_smul, f.map_zero]

theorem intrinsicNorm_linearIsometry {𝕜' : Type*} [RCLike 𝕜']
    (f : 𝕜 →ₗᵢ[ℝ] 𝕜') (g : Ambient m → 𝕜) :
    intrinsicNorm Ω s p (f ∘ g) = intrinsicNorm Ω s p g := by
  rw [← metricNorm_eq_intrinsicNorm, ← metricNorm_eq_intrinsicNorm,
    metricNorm_linearIsometry]

theorem chartNorm_linearIsometry {𝕜' : Type*} [RCLike 𝕜']
    (f : 𝕜 →ₗᵢ[ℝ] 𝕜') (A : Atlas Ω) (g : Ambient m → 𝕜) :
    chartNorm A s p (f ∘ g) = chartNorm A s p g := by
  simp only [chartNorm_eq_metricNorm_sum, localizedPullback_linearIsometry,
    metricNorm_linearIsometry]

/-- Every RCLike scalar type, in any universe, embeds isometrically in ℂ. -/
def scalarEmbedding (𝕜 : Type*) [RCLike 𝕜] : 𝕜 →ₗᵢ[ℝ] ℂ where
  toLinearMap := (RCLike.map 𝕜 ℂ).toLinearMap
  norm_map' x := RCLike.norm_to_complex x

/-- The full comparison retains arbitrary scalar universes; the same constants
from the one-chart estimates apply through the canonical scalar isometry. -/
theorem norm_comparison : Expected.NormComparison := by
  intro m hm Ω hΩ A s hs hs1 p _ hpt
  obtain ⟨C, D, hC, hD, hb⟩ := norm_comparison_small m hm Ω hΩ A s hs hs1 p hpt
  refine ⟨C, D, hC, hD, ?_⟩
  intro 𝕜 _ g hg
  let f := scalarEmbedding 𝕜
  have hgf : MemLp (f ∘ g) p (surfaceMeasure Ω) :=
    hg.continuousLinearMap_comp f.toContinuousLinearMap
  simpa only [chartNorm_linearIsometry, intrinsicNorm_linearIsometry] using hb (f ∘ g) hgf

universe u

/-- Final set identification once the analytic two-sided estimate is available.
This is an assembly lemma; it does not assert the missing estimate. -/
theorem common_classes_of_normComparison (hcomparison : Expected.NormComparison.{u}) :
    Expected.CommonUnderlyingClasses.{u} := by
  intro m hm Ω hΩ A s hs hs1 p _ hpt 𝕜 _
  obtain ⟨C, D, hC, hD, hbounds⟩ := hcomparison m hm Ω hΩ A s hs hs1 p hpt
  ext g
  change g ∈ space 𝕜 Ω s p ↔ chartNorm A s p (g : Ambient m → 𝕜) < ⊤
  constructor
  · intro hg
    exact (hbounds g (Lp.memLp g)).1.trans_lt
      (ENNReal.mul_lt_top (by simp) ((mem_space_iff g).mp hg))
  · intro hg
    apply (mem_space_iff g).mpr
    exact (hbounds g (Lp.memLp g)).2.trans_lt
      (ENNReal.mul_lt_top (by simp) hg)

/-- Choice independence follows by composing the two comparisons through the
intrinsic norm; no relation between the two atlases is required. -/
theorem atlas_independence_of_normComparison (hcomparison : Expected.NormComparison.{u}) :
    Expected.AtlasIndependence.{u} := by
  intro m hm Ω hΩ A B s hs hs1 p _ hpt
  obtain ⟨CA, DA, hCA, hDA, hA⟩ := hcomparison m hm Ω hΩ A s hs hs1 p hpt
  obtain ⟨CB, DB, hCB, hDB, hB⟩ := hcomparison m hm Ω hΩ B s hs hs1 p hpt
  refine ⟨CA * DB, CB * DA, mul_pos hCA hDB, mul_pos hCB hDA, ?_⟩
  intro 𝕜 _ g hg
  constructor
  · calc
      chartNorm A s p g ≤ (CA : ℝ≥0∞) * intrinsicNorm Ω s p g := (hA g hg).1
      _ ≤ (CA : ℝ≥0∞) * ((DB : ℝ≥0∞) * chartNorm B s p g) :=
        by gcongr; exact (hB g hg).2
      _ = ((CA * DB : ℝ≥0) : ℝ≥0∞) * chartNorm B s p g := by
        rw [ENNReal.coe_mul, mul_assoc]
  · calc
      chartNorm B s p g ≤ (CB : ℝ≥0∞) * intrinsicNorm Ω s p g := (hB g hg).1
      _ ≤ (CB : ℝ≥0∞) * ((DA : ℝ≥0∞) * chartNorm A s p g) :=
        by gcongr; exact (hA g hg).2
      _ = ((CB * DA : ℝ≥0) : ℝ≥0∞) * chartNorm A s p g := by
        rw [ENNReal.coe_mul, mul_assoc]

theorem common_underlying_classes : Expected.CommonUnderlyingClasses.{u} :=
  common_classes_of_normComparison norm_comparison

theorem atlas_independence : Expected.AtlasIndependence.{u} :=
  atlas_independence_of_normComparison norm_comparison

/-- Public bindings for the canonical definitions above. -/
theorem finite_surface_measure : Expected.FiniteSurfaceMeasure := fun _ _ hΩ =>
  surfaceMeasure_finite hΩ

def boundaryMeasure : Expected.surfaceMeasureType := @surfaceMeasure
def boundaryEnergy : Expected.energyType := @energy
def boundarySeminorm : Expected.seminormType := @seminorm
def boundaryNorm : Expected.intrinsicNormType := @intrinsicNorm
def boundarySpace : Expected.spaceType := @space
def boundarySpaceNorm : Expected.spaceNormType := @spaceNorm
def boundaryPullback : Expected.localizedPullbackType := @localizedPullback
def boundaryChartNorm : Expected.chartNormType := @chartNorm
def boundaryChartSpace : Expected.chartSpaceType := @chartSpace

end P102.Trace.BoundaryFractional
