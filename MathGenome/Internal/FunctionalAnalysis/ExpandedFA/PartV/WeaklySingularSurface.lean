import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.WeaklySingularSurface
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.WeaklySingularEuclidean
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ExpandedFA.PartV.WeaklySingularSurface
open WeaklySingularEuclidean

/-- A graph chart can be restricted near its origin to a bounded Lipschitz
parametrization of finite Hausdorff measure. -/
lemma C1GraphPatch.exists_finite_measure_neighborhood {n d : ℕ} {x : Euclidean d}
    (g : C1GraphPatch n d x) {S : Set (Euclidean d)}
    (hg : g.param '' g.source ∈ 𝓝[S] x) :
    ∃ K : Set (Euclidean d), K ∈ 𝓝[S] x ∧ IsCompact K ∧
      Measure.hausdorffMeasure (n : ℝ) K < ∞ := by
  have hc : ContDiffAt ℝ 1 g.param 0 :=
    g.smooth.contDiffAt (g.open_source.mem_nhds g.zero_mem)
  obtain ⟨L, t, ht, hL⟩ := hc.exists_lipschitzOnWith
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (g.open_source.mem_nhds g.zero_mem) ht)
  let K := g.param '' Metric.closedBall (0 : Euclidean n) (r / 2)
  have hb : Metric.closedBall (0 : Euclidean n) (r / 2) ⊆ g.source ∩ t := by
    apply Set.Subset.trans _ hrt
    exact Metric.closedBall_subset_ball (by linarith)
  have hKn : K ∈ 𝓝[S] x := by
    have hcoord : Continuous (fun y : Euclidean d => g.coord (y - x)) :=
      g.coord.continuous.comp (continuous_id.sub continuous_const)
    have hpre : {y : Euclidean d | g.coord (y - x) ∈ Metric.ball 0 (r / 2)} ∈ 𝓝 x := by
      apply hcoord.continuousAt.preimage_mem_nhds
      simpa using Metric.ball_mem_nhds (0 : Euclidean n) (show 0 < r / 2 by positivity)
    apply Filter.mem_of_superset (Filter.inter_mem hg (nhdsWithin_le_nhds hpre))
    rintro y ⟨⟨u, hu, rfl⟩, hy⟩
    exact ⟨u, Metric.ball_subset_closedBall (by
      change g.coord (g.param u - x) ∈ Metric.ball 0 (r / 2) at hy
      rwa [g.coord_param u hu] at hy), rfl⟩
  refine ⟨K, hKn, (isCompact_closedBall _ _).image_of_continuousOn
    (hL.mono (fun u hu => (hb hu).2)).continuousOn, ?_⟩
  have hH : Measure.hausdorffMeasure (n : ℝ) (Metric.closedBall (0 : Euclidean n) (r / 2)) < ∞ := by
    have he : (n : ℝ) = (Module.finrank ℝ (Euclidean n) : ℝ) := by simp [Euclidean]
    rw [he]
    exact (isCompact_closedBall (0 : Euclidean n) (r / 2)).measure_lt_top
  apply lt_of_le_of_lt ((hL.mono (fun u hu => (hb hu).2)).hausdorffMeasure_image_le
    (show 0 ≤ (n : ℝ) by positivity))
  rw [ENNReal.rpow_natCast]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hH

/-- Compactness turns the local finite-area graph estimates into finite area
of the surface itself. -/
theorem surface_measure_finite : Spec.SurfaceMeasureFinite := by
  intro n d S hS hcharts
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let ν : Measure S := (Measure.hausdorffMeasure (n : ℝ)).comap Subtype.val
  have hme : MeasurableEmbedding (Subtype.val : S → Euclidean d) :=
    MeasurableEmbedding.subtype_coe hS.measurableSet
  haveI : IsLocallyFiniteMeasure ν := by
    constructor
    intro x
    obtain ⟨g, hg⟩ := hcharts x x.property
    obtain ⟨K, hK, hKc, hfin⟩ := g.exists_finite_measure_neighborhood hg
    refine ⟨Subtype.val ⁻¹' K, ?_, ?_⟩
    · exact by
        rw [nhds_subtype_eq_comap_nhdsWithin S x]
        exact preimage_mem_comap hK
    · change (Measure.hausdorffMeasure (n : ℝ)).comap Subtype.val
        (Subtype.val ⁻¹' K) < ∞
      rw [Measure.comap_apply _ hme.injective (fun _ hs => hme.measurableSet_image.mpr hs)
        _ (hKc.measurableSet.preimage measurable_subtype_coe)]
      exact lt_of_le_of_lt (measure_mono (Set.image_preimage_subset _ _)) hfin
  haveI : IsFiniteMeasure ν := inferInstance
  exact inferInstanceAs (IsFiniteMeasure (surfaceNormalization n • ν))

/-- In dimension zero the chart has one parameter, so its image is a singleton.
Every point is isolated relative to S. -/
theorem zero_dimensional_finiteness : Spec.ZeroDimensionalFiniteness := by
  intro d S hS hcharts
  have hdiscrete : ∀ x ∈ S, {x} ∈ 𝓝[S] x := by
    intro x hx
    obtain ⟨g, hg⟩ := hcharts x hx
    apply Filter.mem_of_superset hg
    rintro y ⟨u, hu, rfl⟩
    have hu0 : u = 0 := Subsingleton.elim _ _
    simp [hu0, g.param_zero]
  haveI : DiscreteTopology S := by
    apply discreteTopology_iff_singleton_mem_nhds.mpr
    intro x
    have hh := hdiscrete x x.property
    rw [nhds_subtype_eq_comap_nhdsWithin S x]
    apply Filter.mem_of_superset (preimage_mem_comap hh)
    intro y hy
    exact Subtype.ext hy
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hf : (Set.univ : Set S).Finite := isCompact_univ.finite_of_discrete
  haveI : Finite S := Set.finite_univ_iff.mp hf
  exact Set.toFinite S

/-- The zero-dimensional part of the original theorem, for every kernel. -/
theorem zero_dimensional_compactness : Spec.ZeroDimensionalCompactness := by
  intro d 𝕜 _ _ _ S hS hcharts k
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  haveI : Finite S := (zero_dimensional_finiteness d S hS hcharts).to_subtype
  haveI := surface_measure_finite 0 d S hS hcharts
  exact finite_domain_compact_integral_maps (surfaceMeasure 0 S) k


/-- Positive-dimensional Hausdorff surface measure has no point masses. -/
lemma surface_measure_null_singletons {n d : ℕ} (hn : 0 < n)
    (S : Set (Euclidean d)) (hS : IsCompact S) :
    NullSingletonClass (surfaceMeasure n S) := by
  haveI := Measure.nullSingletonClass_hausdorff (Euclidean d) (show 0 < (n : ℝ) by exact_mod_cast hn)
  have hme := MeasurableEmbedding.subtype_coe hS.measurableSet
  constructor
  intro x
  simp only [surfaceMeasure, Measure.smul_apply, smul_eq_mul]
  rw [Measure.comap_apply _ hme.injective (fun _ hs => hme.measurableSet_image.mpr hs)
    _ (measurableSet_singleton x), Set.image_singleton]
  simp

section RadialApproximation
variable {X 𝕜 : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
  (μ : Measure X) [IsFiniteMeasure μ]

lemma radialBound_symm (n : ℕ) (α : ℝ) (C M : ℝ≥0) (x y : X) :
    radialBound n α C M x y = radialBound n α C M y x := by
  classical
  simp only [radialBound, dist_comm, eq_comm]

/-- The discarded cutoff is supported in the strip of width 2δ and is bounded
by the same nonnegative radial majorant in each row and column. -/
lemma cutoff_error_bounds (k : X × X → 𝕜)
    (n : ℕ) (α : ℝ) (C M : ℝ≥0)
    (hk : ∀ x y, ‖k (x,y)‖ₑ ≤ radialBound n α C M x y)
    (b : ℝ → ℝ≥0)
    (hb : ∀ r : ℝ, 0 < r → ∀ x : X,
      ∫⁻ y in Metric.ball x r, radialBound n α C M x y ∂μ ≤ b r)
    (δ : ℝ) (hδ : 0 < δ) :
    (∀ x, ∫⁻ y, ‖k (x,y) - cutoffKernel δ k (x,y)‖ₑ ∂μ ≤ b (2 * δ)) ∧
    (∀ y, ∫⁻ x, ‖k (x,y) - cutoffKernel δ k (x,y)‖ₑ ∂μ ≤ b (2 * δ)) := by
  classical
  have he (x y : X) : ‖k (x,y) - cutoffKernel δ k (x,y)‖ₑ ≤
      (Metric.ball x (2 * δ)).indicator (radialBound n α C M x) y := by
    by_cases hd : dist x y < 2 * δ
    · rw [Set.indicator_of_mem (by simpa [Metric.mem_ball, dist_comm] using hd)]
      exact (enorm_le_iff_norm_le.mpr (cutoffKernel_error_le δ k (x,y))).trans (hk x y)
    · rw [cutoffKernel_eq_self k hδ (le_of_not_gt hd), sub_self, enorm_zero]
      exact zero_le
  constructor
  · intro x
    calc
      _ ≤ ∫⁻ y, (Metric.ball x (2 * δ)).indicator (radialBound n α C M x) y ∂μ :=
        lintegral_mono (he x)
      _ = _ := lintegral_indicator measurableSet_ball _
      _ ≤ _ := hb _ (by positivity) x
  · intro y
    calc
      _ ≤ ∫⁻ x, (Metric.ball y (2 * δ)).indicator (radialBound n α C M y) x ∂μ := by
        apply lintegral_mono
        intro x
        have h := he x y
        by_cases hd : dist x y < 2 * δ
        · simpa only [Set.indicator_of_mem (show y ∈ Metric.ball x (2 * δ) by
              simpa [Metric.mem_ball, dist_comm] using hd),
            Set.indicator_of_mem (show x ∈ Metric.ball y (2 * δ) from hd),
            radialBound_symm n α C M x y] using h
        · change ‖k (x,y) - cutoffKernel δ k (x,y)‖ₑ ≤ _
          rw [cutoffKernel_eq_self k hδ (le_of_not_gt hd), sub_self, enorm_zero]
          exact zero_le
      _ = _ := lintegral_indicator measurableSet_ball _
      _ ≤ _ := hb _ (by positivity) y

/-- Uniform radial smallness implies the continuous-kernel approximation used
by the upstream compactness theorem. No surface geometry is assumed here. -/
lemma uniform_approximation_from_radial_smallness (k : X × X → 𝕜)
    (n : ℕ) (α : ℝ) (C M : ℝ≥0)
    (hc : ContinuousOn k {z | z.1 ≠ z.2})
    (hk : ∀ x y, x ≠ y → ‖k (x,y)‖ ≤ C * dist x y ^ (α - n) + M)
    (hs : UniformRadialSmallness μ n α C M) :
    UniformKernelApproximation μ (zeroDiagonal k) := by
  classical
  obtain ⟨b, hb0, hb⟩ := hs
  let δ (j : ℕ) : ℝ := (1 / ((j : ℝ) + 1)) / 2
  have hδ (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  let h (j : ℕ) : C(X × X, 𝕜) :=
    ⟨cutoffKernel (δ j) (zeroDiagonal k),
      cutoff_continuous _ (zeroDiagonal_continuousOn _ hc) _ (hδ j)⟩
  have hbound (x y : X) : ‖zeroDiagonal k (x,y)‖ₑ ≤ radialBound n α C M x y := by
    by_cases hxy : x = y
    · simp [zeroDiagonal, radialBound, hxy]
    · simp only [zeroDiagonal, if_neg hxy, radialBound, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hk x y hxy)
  have herr (j : ℕ) := cutoff_error_bounds μ (zeroDiagonal k) n α C M hbound b hb
    (δ j) (hδ j)
  have hcontrow (x : X) : ∫⁻ y, ‖h 0 (x,y)‖ₑ ∂μ ≤
      (measureUnivNNReal μ * ‖h 0‖₊ : ℝ≥0) := by
    calc
      _ ≤ ∫⁻ _ : X, (‖h 0‖₊ : ℝ≥0∞) ∂μ := by
        apply lintegral_mono
        intro y
        exact ENNReal.coe_le_coe.mpr ((h 0).norm_coe_le_norm (x,y))
      _ = _ := by simp [measureUnivNNReal, mul_comm]
  have hcontcol (y : X) : ∫⁻ x, ‖h 0 (x,y)‖ₑ ∂μ ≤
      (measureUnivNNReal μ * ‖h 0‖₊ : ℝ≥0) := by
    calc
      _ ≤ ∫⁻ _ : X, (‖h 0‖₊ : ℝ≥0∞) ∂μ := by
        apply lintegral_mono
        intro x
        exact ENNReal.coe_le_coe.mpr ((h 0).norm_coe_le_norm (x,y))
      _ = _ := by simp [measureUnivNNReal, mul_comm]
  let A : ℝ≥0 := b (2 * δ 0) + measureUnivNNReal μ * ‖h 0‖₊
  have hm : Measurable (zeroDiagonal k) := zeroDiagonal_measurable k hc
  have htotal (x y : X) : ‖zeroDiagonal k (x,y)‖ₑ ≤
      ‖zeroDiagonal k (x,y) - h 0 (x,y)‖ₑ + ‖h 0 (x,y)‖ₑ := by
    simpa only [sub_add_cancel] using
      enorm_add_le (zeroDiagonal k (x,y) - h 0 (x,y)) (h 0 (x,y))
  have hAr (x : X) : ∫⁻ y, ‖zeroDiagonal k (x,y)‖ₑ ∂μ ≤ A := by
    calc
      _ ≤ ∫⁻ y, ‖zeroDiagonal k (x,y) - h 0 (x,y)‖ₑ + ‖h 0 (x,y)‖ₑ ∂μ :=
        lintegral_mono (htotal x)
      _ = _ := lintegral_add_left
        ((hm.comp (measurable_const.prodMk measurable_id)).sub
          ((h 0).continuous.measurable.comp (measurable_const.prodMk measurable_id))).enorm _
      _ ≤ _ := by
        simpa [A, h] using add_le_add ((herr 0).1 x) (hcontrow x)
  have hAc (y : X) : ∫⁻ x, ‖zeroDiagonal k (x,y)‖ₑ ∂μ ≤ A := by
    calc
      _ ≤ ∫⁻ x, ‖zeroDiagonal k (x,y) - h 0 (x,y)‖ₑ + ‖h 0 (x,y)‖ₑ ∂μ :=
        lintegral_mono (fun x => htotal x y)
      _ = _ := lintegral_add_left
        ((hm.comp (measurable_id.prodMk measurable_const)).sub
          ((h 0).continuous.measurable.comp (measurable_id.prodMk measurable_const))).enorm _
      _ ≤ _ := by
        simpa [A, h] using add_le_add ((herr 0).2 y) (hcontcol y)
  refine ⟨⟨A, hAr, hAc⟩, h, fun j => b (2 * δ j), ?_, herr⟩
  apply hb0.comp
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · simpa only [δ, mul_div_cancel₀ _ (show (2 : ℝ) ≠ 0 by norm_num)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  · exact Eventually.of_forall (fun j => show 0 < 2 * δ j by positivity)

/-- Compactness for the original kernel follows by removing and restoring the
null diagonal. This proves absolute existence as well as the integral formulas. -/
theorem compactness_from_radial_smallness : Spec.CompactnessFromRadialSmallness := by
  intro X 𝕜 _ _ _ _ _ _ _ _ μ _ _ k n α C M hc hk hs
  exact (compactIntegralMaps_zeroDiagonal_iff μ k).mp
    (compactIntegralMaps_of_uniformKernelApproximation μ (zeroDiagonal k)
      (zeroDiagonal_measurable k hc)
      (uniform_approximation_from_radial_smallness μ k n α C M hc hk hs))

end RadialApproximation

/-- The local graph estimate uses the linear projection to place all parameters
above an ambient ball inside one parameter ball. Its center need not lie in
the graph patch. -/
lemma C1GraphPatch.exists_local_growth_bound {n d : ℕ} {x : Euclidean d}
    (g : C1GraphPatch n d x) {S : Set (Euclidean d)}
    (hg : g.param '' g.source ∈ 𝓝[S] x) :
    ∃ K : Set (Euclidean d), K ∈ 𝓝[S] x ∧
      ∃ B : ℝ≥0, ∀ (y : Euclidean d) (r : ℝ), 0 < r →
        Measure.hausdorffMeasure (n : ℝ) (K ∩ Metric.ball y r) ≤
          ENNReal.ofReal (B * r ^ n) := by
  have hc : ContDiffAt ℝ 1 g.param 0 :=
    g.smooth.contDiffAt (g.open_source.mem_nhds g.zero_mem)
  obtain ⟨L, t, ht, hL⟩ := hc.exists_lipschitzOnWith
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (g.open_source.mem_nhds g.zero_mem) ht)
  let V := Metric.ball (0 : Euclidean n) ε
  have hV : V ⊆ g.source ∩ t := hεt
  let K := g.param '' V
  have hKn : K ∈ 𝓝[S] x := by
    have hcoord : Continuous (fun y : Euclidean d => g.coord (y - x)) :=
      g.coord.continuous.comp (continuous_id.sub continuous_const)
    have hpre : {y : Euclidean d | g.coord (y - x) ∈ V} ∈ 𝓝 x := by
      apply hcoord.continuousAt.preimage_mem_nhds
      simpa [V] using Metric.ball_mem_nhds (0 : Euclidean n) hε
    apply Filter.mem_of_superset (Filter.inter_mem hg (nhdsWithin_le_nhds hpre))
    rintro y ⟨⟨u, hu, rfl⟩, hy⟩
    exact ⟨u, by
      change g.coord (g.param u - x) ∈ V at hy
      rwa [g.coord_param u hu] at hy, rfl⟩
  let H : Measure (Euclidean n) := Measure.hausdorffMeasure (n : ℝ)
  haveI : Measure.IsAddHaarMeasure H := by
    have he : (n : ℝ) = (Module.finrank ℝ (Euclidean n) : ℝ) := by simp [Euclidean]
    dsimp [H]
    rw [he]
    infer_instance
  let q : ℝ≥0 := ‖g.coord‖₊ + 1
  have hq : 0 < (q : ℝ) := by dsimp [q]; positivity
  let B : ℝ≥0 := L ^ n * q ^ n * (H (Metric.ball 0 1)).toNNReal
  refine ⟨K, hKn, B, ?_⟩
  intro y r hr
  let P := V ∩ g.param ⁻¹' Metric.ball y r
  have himage : K ∩ Metric.ball y r = g.param '' P := by
    exact (Set.image_inter_preimage _ _ _).symm
  have hP : P ⊆ Metric.ball (g.coord (y - x)) ((q : ℝ) * r) := by
    intro u hu
    have hleft := g.coord_param u (hV hu.1).1
    have he : dist u (g.coord (y - x)) = ‖g.coord (g.param u - y)‖ := by
      calc
        _ = ‖g.coord (g.param u - x) - g.coord (y - x)‖ := by rw [hleft]; rfl
        _ = ‖g.coord (g.param u - y)‖ := by
          rw [← map_sub]
          congr 2
          abel
    rw [Metric.mem_ball, he]
    have hy : ‖g.param u - y‖ < r := hu.2
    calc
      ‖g.coord (g.param u - y)‖ ≤ ‖g.coord‖ * ‖g.param u - y‖ := g.coord.le_opNorm _
      _ ≤ (q : ℝ) * ‖g.param u - y‖ := by
        gcongr
        exact le_add_of_nonneg_right zero_le_one
      _ < (q : ℝ) * r := mul_lt_mul_of_pos_left hy hq
  have hmass : H (Metric.ball (g.coord (y - x)) ((q : ℝ) * r)) =
      ENNReal.ofReal ((q : ℝ) * r) ^ n * H (Metric.ball 0 1) := by
    rw [Measure.addHaar_ball_of_pos H _ (mul_pos hq hr)]
    simp only [Euclidean, finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_pow
      (le_of_lt (mul_pos hq hr))]
  calc
    _ = Measure.hausdorffMeasure (n : ℝ) (g.param '' P) := congrArg _ himage
    _ ≤ (L : ℝ≥0∞) ^ (n : ℝ) * H P :=
      (hL.mono (fun u hu => (hV hu.1).2)).hausdorffMeasure_image_le (by positivity)
    _ ≤ (L : ℝ≥0∞) ^ (n : ℝ) * H (Metric.ball (g.coord (y - x)) ((q : ℝ) * r)) :=
      by
        gcongr
    _ = ENNReal.ofReal (B * r ^ n) := by
      rw [hmass, ENNReal.rpow_natCast]
      have hf : H (Metric.ball 0 1) ≠ ∞ := measure_ball_ne_top
      simp only [B, NNReal.coe_mul, NNReal.coe_pow, ENNReal.ofReal_mul
        (by positivity : 0 ≤ (L : ℝ) ^ n * (q : ℝ) ^ n *
          ((H (Metric.ball 0 1)).toNNReal : ℝ)), ENNReal.ofReal_pow hr.le,
        ENNReal.ofReal_mul hq.le, mul_pow, ENNReal.ofReal_coe_nnreal,
        ENNReal.coe_toNNReal hf]
      rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (L : ℝ) ^ n * (q : ℝ) ^ n),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (L : ℝ) ^ n),
        ENNReal.ofReal_pow (NNReal.coe_nonneg L), ENNReal.ofReal_pow hq.le,
        ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
      rw [ENNReal.ofReal_coe_nnreal, ENNReal.coe_toNNReal hf]
      ring


/-- Finitely many local C¹ graphs yield a global upper n-dimensional ball
estimate for the actual surface area, uniformly over centers and radii. -/
theorem surface_ball_growth : Spec.SurfaceBallGrowth := by
  classical
  intro n d hn S hS hcharts
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have hlocal (x : S) : ∃ K : Set (Euclidean d), K ∈ 𝓝[S] (x : Euclidean d) ∧
      ∃ B : ℝ≥0, ∀ (y : Euclidean d) (r : ℝ), 0 < r →
        Measure.hausdorffMeasure (n : ℝ) (K ∩ Metric.ball y r) ≤
          ENNReal.ofReal (B * r ^ n) := by
    obtain ⟨g, hg⟩ := hcharts x x.property
    exact g.exists_local_growth_bound hg
  choose K hK B hB using hlocal
  have hU (x : S) : Subtype.val ⁻¹' K x ∈ 𝓝 x := by
    rw [nhds_subtype_eq_comap_nhdsWithin S x]
    exact preimage_mem_comap (hK x)
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover
    (fun x : S => interior (Subtype.val ⁻¹' K x)) (fun _ => isOpen_interior)
    (show (Set.univ : Set S) ⊆ ⋃ x : S, interior (Subtype.val ⁻¹' K x) from by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y, mem_interior_iff_mem_nhds.mpr (hU y)⟩)
  let Btotal : ℝ≥0 := ∑ i ∈ F, B i
  refine ⟨surfaceNormalization n * Btotal, ?_⟩
  intro y r hr
  have hcover : S ∩ Metric.ball (y : Euclidean d) r ⊆
      ⋃ i ∈ F, K i ∩ Metric.ball (y : Euclidean d) r := by
    rintro z ⟨hzS, hz⟩
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.mp (hF (Set.mem_univ (⟨z, hzS⟩ : S)))
    exact Set.mem_iUnion₂.mpr ⟨i, hi, (interior_subset hzi : (⟨z, hzS⟩ : S) ∈ Subtype.val ⁻¹' K i), hz⟩
  have hsum : Measure.hausdorffMeasure (n : ℝ) (S ∩ Metric.ball (y : Euclidean d) r) ≤
      ENNReal.ofReal (Btotal * r ^ n) := by
    calc
      _ ≤ Measure.hausdorffMeasure (n : ℝ)
          (⋃ i ∈ F, K i ∩ Metric.ball (y : Euclidean d) r) := measure_mono hcover
      _ ≤ ∑ i ∈ F, Measure.hausdorffMeasure (n : ℝ)
          (K i ∩ Metric.ball (y : Euclidean d) r) := measure_biUnion_finset_le _ _
      _ ≤ ∑ i ∈ F, ENNReal.ofReal (B i * r ^ n) :=
        Finset.sum_le_sum (fun i _ => hB i y r hr)
      _ = ENNReal.ofReal (Btotal * r ^ n) := by
        simp only [Btotal, NNReal.coe_sum, Finset.sum_mul]
        exact (ENNReal.ofReal_sum_of_nonneg fun i _ =>
          mul_nonneg (B i).coe_nonneg (pow_nonneg hr.le n)).symm
  rw [surfaceMeasure, Measure.smul_apply, comap_subtype_coe_apply hS.measurableSet,
    Subtype.image_ball, Set.inter_comm]
  change (surfaceNormalization n : ℝ≥0∞) * _ ≤ _
  calc
    _ ≤ (surfaceNormalization n : ℝ≥0∞) * ENNReal.ofReal (Btotal * r ^ n) := by
      gcongr
      exact hsum
    _ = _ := by
      simp only [NNReal.coe_mul, mul_assoc,
        ENNReal.ofReal_mul (surfaceNormalization n).coe_nonneg, ENNReal.ofReal_coe_nnreal]


/-- Choose one dyadic annulus. The factor works for either sign of β. -/
lemma dyadic_power_bound {R t : ℝ} (hR : 0 < R) (ht : 0 < t) (htR : t ≤ R)
    (β : ℝ) : ∃ j : ℕ,
      t < 2 * R * (1 / 2 : ℝ) ^ j ∧
      t ^ β ≤ (1 + (1 / 2 : ℝ) ^ β) * (R * (1 / 2 : ℝ) ^ j) ^ β := by
  obtain ⟨j, hjl, hju⟩ := exists_nat_pow_near_of_lt_one (div_pos ht hR)
    ((div_le_one hR).mpr htR) (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  have hlo : R * (1 / 2 : ℝ) ^ (j + 1) < t := by
    have := (lt_div_iff₀ hR).mp hjl
    simpa only [mul_comm] using this
  have hhi : t ≤ R * (1 / 2 : ℝ) ^ j := by
    have := (div_le_iff₀ hR).mp hju
    simpa only [mul_comm] using this
  have hpos : 0 < R * (1 / 2 : ℝ) ^ j := by positivity
  refine ⟨j, by nlinarith, ?_⟩
  by_cases hβ : 0 ≤ β
  · calc
      t ^ β ≤ (R * (1 / 2 : ℝ) ^ j) ^ β := Real.rpow_le_rpow ht.le hhi hβ
      _ ≤ _ := by
        have hp := Real.rpow_nonneg hpos.le β
        have hq := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) β
        nlinarith
  · have hβ' : β ≤ 0 := le_of_not_ge hβ
    calc
      t ^ β ≤ (R * (1 / 2 : ℝ) ^ (j + 1)) ^ β :=
        Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hβ'
          (show 0 < R * (1 / 2 : ℝ) ^ (j + 1) by positivity) ht hlo.le
      _ = (1 / 2 : ℝ) ^ β * (R * (1 / 2 : ℝ) ^ j) ^ β := by
        rw [show R * (1 / 2 : ℝ) ^ (j + 1) = (1 / 2 : ℝ) * (R * (1 / 2 : ℝ) ^ j) by
          rw [pow_succ]; ring]
        exact Real.mul_rpow (by norm_num) hpos.le
      _ ≤ _ := by
        have hp := Real.rpow_nonneg hpos.le β
        nlinarith

/-- Cancellation of the n-dimensional volume factor against the singular
power leaves the positive exponent α in the dyadic series. -/
lemma dyadic_power_volume_identity (n j : ℕ) (α D A R : ℝ) (hR : 0 < R) :
    (D * (R * (1 / 2 : ℝ) ^ j) ^ (α - n)) *
        (A * (2 * R * (1 / 2 : ℝ) ^ j) ^ n) =
      (D * A * 2 ^ n) * R ^ α * ((1 / 2 : ℝ) ^ α) ^ j := by
  have hp (a : ℝ) (ha : 0 < a) : a ^ (α - n) * a ^ n = a ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha]
    congr 1
    ring
  rw [Real.mul_rpow hR.le (by positivity), mul_pow, mul_pow]
  calc
    _ = (D * A * 2 ^ n) *
        (R ^ (α - n) * R ^ n) *
        (((1 / 2 : ℝ) ^ j) ^ (α - n) * ((1 / 2 : ℝ) ^ j) ^ n) := by ring
    _ = _ := by
      rw [hp R hR, hp _ (by positivity), ← Real.rpow_pow_comm (by norm_num)]

section GrowthAnalysis
attribute [local instance] Classical.propDecidable
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) (n : ℕ) (A : ℝ≥0)
  (hgrowth : ∀ (x : X) (r : ℝ), 0 < r → μ (Metric.ball x r) ≤ ENNReal.ofReal (A * r ^ n))

include hgrowth in
/-- A direct dyadic estimate, retaining every positive real α. -/
lemma power_strip_lintegral_bound (α : ℝ) (hα : 0 < α) (x : X)
    (R : ℝ) (hR : 0 < R) :
    ∫⁻ y in Metric.ball x R,
      (if x = y then 0 else ENNReal.ofReal (dist x y ^ (α - n))) ∂μ ≤
      ENNReal.ofReal (((1 + (1 / 2 : ℝ) ^ (α - n)) * A * 2 ^ n) *
        R ^ α * (1 - (1 / 2 : ℝ) ^ α)⁻¹) := by
  classical
  let D : ℝ := 1 + (1 / 2 : ℝ) ^ (α - n)
  let q : ℝ := (1 / 2 : ℝ) ^ α
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  let F (j : ℕ) : X → ℝ≥0∞ := (Metric.ball x (2 * R * (1 / 2 : ℝ) ^ j)).indicator
    (fun _ => ENNReal.ofReal (D * (R * (1 / 2 : ℝ) ^ j) ^ (α - n)))
  have hm (j : ℕ) : Measurable (F j) := measurable_const.indicator measurableSet_ball
  have hpoint (y : X) :
      (Metric.ball x R).indicator
        (fun y => if x = y then 0 else ENNReal.ofReal (dist x y ^ (α - n))) y ≤
          ∑' j, F j y := by
    by_cases hy : y ∈ Metric.ball x R
    · rw [Set.indicator_of_mem hy]
      by_cases hxy : x = y
      · simp [hxy]
      · rw [if_neg hxy]
        have hd : 0 < dist x y := dist_pos.mpr hxy
        have hdR : dist x y ≤ R := by exact (show dist x y < R by simpa only [Metric.mem_ball, dist_comm] using hy).le
        obtain ⟨j, hjball, hjpow⟩ := dyadic_power_bound hR hd hdR (α - n)
        calc
          _ ≤ F j y := by
            dsimp only [F]
            rw [Set.indicator_of_mem (by simpa [Metric.mem_ball, dist_comm] using hjball)]
            exact ENNReal.ofReal_le_ofReal hjpow
          _ ≤ _ := ENNReal.le_tsum (f := fun j => F j y) j
    · rw [Set.indicator_of_notMem hy]
      exact zero_le
  have hterm (j : ℕ) : ∫⁻ y, F j y ∂μ ≤
      ENNReal.ofReal ((D * A * 2 ^ n) * R ^ α * q ^ j) := by
    rw [show F j = _ from rfl, lintegral_indicator measurableSet_ball, lintegral_const]
    calc
      _ ≤ ENNReal.ofReal (D * (R * (1 / 2 : ℝ) ^ j) ^ (α - n)) *
          ENNReal.ofReal (A * (2 * R * (1 / 2 : ℝ) ^ j) ^ n) := by
        gcongr
        simpa only [Measure.restrict_apply_univ] using
          hgrowth x (2 * R * (1 / 2 : ℝ) ^ j) (by positivity)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hD (Real.rpow_nonneg (by positivity) _)),
          dyadic_power_volume_identity n j α D A R hR]
  calc
    _ = ∫⁻ y, (Metric.ball x R).indicator
        (fun y => if x = y then 0 else ENNReal.ofReal (dist x y ^ (α - n))) y ∂μ :=
      (lintegral_indicator measurableSet_ball _).symm
    _ ≤ ∫⁻ y, ∑' j, F j y ∂μ := lintegral_mono hpoint
    _ = ∑' j, ∫⁻ y, F j y ∂μ := lintegral_tsum (fun j => (hm j).aemeasurable)
    _ ≤ ∑' j, ENNReal.ofReal ((D * A * 2 ^ n) * R ^ α * q ^ j) :=
      ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal ((D * A * 2 ^ n) * R ^ α * (1 - q)⁻¹) := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
        ((summable_geometric_of_lt_one hq0 hq1).mul_left _), tsum_mul_left,
        tsum_geometric_of_lt_one hq0 hq1]

end GrowthAnalysis

/-- Uniform polynomial ball growth implies vanishing strip integrals by the
dyadic estimate. The bounded remainder contributes O(rⁿ). -/
theorem radial_smallness_from_growth : Spec.RadialSmallnessFromGrowth := by
  classical
  intro X _ _ _ _ μ _ _ n hn A hgrowth α C M hα
  let D : ℝ := 1 + (1 / 2 : ℝ) ^ (α - n)
  let q : ℝ := (1 / 2 : ℝ) ^ α
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hD : 0 ≤ D := by dsimp [D]; positivity
  let K : ℝ := D * A * 2 ^ n * (1 - q)⁻¹
  have hK : 0 ≤ K := by dsimp [K]; positivity
  let b (r : ℝ) : ℝ≥0 := ⟨C * K * |r| ^ α + M * A * |r| ^ n, by positivity⟩
  refine ⟨b, ?_, ?_⟩
  · apply NNReal.tendsto_coe.mp
    have ht : Tendsto (fun r : ℝ => C * K * |r| ^ α + M * A * |r| ^ n)
        (𝓝 0) (𝓝 0) := by
      have hcont : ContinuousAt (fun r : ℝ => C * K * |r| ^ α + M * A * |r| ^ n) 0 := by
        apply ContinuousAt.add
        · exact continuousAt_const.mul (continuous_abs.continuousAt.rpow_const (.inr hα.le))
        · fun_prop
      simpa only [abs_zero, Real.zero_rpow hα.ne', zero_pow hn.ne', mul_zero, add_zero]
        using hcont.tendsto
    exact ht.mono_left nhdsWithin_le_nhds
  · intro r hr x
    let P (y : X) : ℝ≥0∞ := if x = y then 0 else ENNReal.ofReal (dist x y ^ (α - n))
    have hp : ∫⁻ y in Metric.ball x r, P y ∂μ ≤ ENNReal.ofReal (K * r ^ α) := by
      have hh := power_strip_lintegral_bound μ n A hgrowth α hα x r hr
      convert hh using 1
      congr 1
      dsimp [K, D, q]
      ring
    have hpoint (y : X) : radialBound n α C M x y ≤ (C : ℝ≥0∞) * P y + M := by
      by_cases hxy : x = y
      · simp [radialBound, P, hxy]
      · simp only [radialBound, P, if_neg hxy]
        rw [ENNReal.ofReal_add (mul_nonneg C.coe_nonneg (Real.rpow_nonneg dist_nonneg _)),
          ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
          ENNReal.ofReal_coe_nnreal]
        exact M.coe_nonneg
    have hbcast : (b r : ℝ≥0∞) = ENNReal.ofReal (C * K * r ^ α + M * A * r ^ n) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      change ENNReal.ofReal (C * K * |r| ^ α + M * A * |r| ^ n) = _
      rw [abs_of_pos hr]
    rw [hbcast]
    calc
      _ ≤ ∫⁻ y in Metric.ball x r, (C : ℝ≥0∞) * P y + M ∂μ :=
        lintegral_mono hpoint
      _ = (C : ℝ≥0∞) * (∫⁻ y in Metric.ball x r, P y ∂μ) +
          (M : ℝ≥0∞) * μ (Metric.ball x r) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          lintegral_const, Measure.restrict_apply_univ]
      _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (K * r ^ α) +
          (M : ℝ≥0∞) * ENNReal.ofReal (A * r ^ n) := by
        exact add_le_add (mul_le_mul_right hp _) (mul_le_mul_right (hgrowth x r hr) _)
      _ = _ := by
        have hC : (C : ℝ≥0∞) = ENNReal.ofReal (C : ℝ) := ENNReal.ofReal_coe_nnreal.symm
        have hM : (M : ℝ≥0∞) = ENNReal.ofReal (M : ℝ) := ENNReal.ofReal_coe_nnreal.symm
        rw [hC, hM, ← ENNReal.ofReal_mul C.coe_nonneg, ← ENNReal.ofReal_mul M.coe_nonneg,
          ← ENNReal.ofReal_add (by positivity : 0 ≤ (C : ℝ) * (K * r ^ α))]
        · congr 1
          ring
        · positivity

/-- The complete weakly singular surface theorem: genuine surface area,
arbitrary diagonal values, both scalar fields, and every endpoint Lp. -/
theorem surface_compactness : Spec.SurfaceCompactness := by
  intro n d 𝕜 _ _ _ S hS hcharts k α C M hα hk
  by_cases hn : n = 0
  · subst n
    exact zero_dimensional_compactness d 𝕜 S hS hcharts k
  · letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
    haveI := surface_measure_finite n d S hS hcharts
    haveI := surface_measure_null_singletons (Nat.pos_of_ne_zero hn) S hS
    obtain ⟨A, hA⟩ := surface_ball_growth n d (Nat.pos_of_ne_zero hn) S hS hcharts
    exact compactness_from_radial_smallness (surfaceMeasure n S) k n α C M hk.1 hk.2
      (radial_smallness_from_growth (surfaceMeasure n S) n (Nat.pos_of_ne_zero hn)
        A hA α C M hα)

end ExpandedFA.PartV.WeaklySingularSurface
