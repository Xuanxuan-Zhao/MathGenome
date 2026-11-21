import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.MetricTopFormsAndDensities
import MathGenome.Internal.MultivariableAnalysis.D04.C14.OrientationsAndChartSigns
import MathGenome.Internal.MultivariableAnalysis.D04.C13.OrientedEuclideanDictionary

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Set Filter Topology
open scoped ContDiff
namespace D04MetricDensity
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.OrientedEuclideanDictionary.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C14.GraphTransitionsAndIntrinsicBoundary.Model
open Specs.D04.C14.ChartIndependentTangentSpaces.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
open Specs.D04.C14.MetricTopFormsAndDensities.Model


theorem metricVolume_eq {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (hM : IsEmbeddedManifold r k M) (o : TangentOrientationField r k M) (x : M) :
    let : Fact (Module.finrank ℝ (tangentSpace r k M x) = k) :=
      ⟨D04.tangentSpace_finrank hM x x.property⟩
    metricVolume o x = metricTopForm (o x x.property) := by
  simp [metricVolume, Specs.D04.C14.MetricTopFormsAndDensities.Model.metricVolume,
    D04.tangentSpace_finrank hM x x.property]

theorem metricVolume_normalized :
    Specs.D04.C14.MetricTopFormsAndDensities.metricVolume_normalizedType := by
  intro r k n M hM o x b hb
  let : Fact (Module.finrank ℝ (tangentSpace r k M x) = k) :=
    ⟨D04.tangentSpace_finrank hM x x.property⟩
  rw [metricVolume_eq hM o x]
  exact D04.Dictionary.metricTopForm_normalized _ b hb

theorem metricVolume_unique :
    Specs.D04.C14.MetricTopFormsAndDensities.metricVolume_uniqueType := by
  intro r k n M hM hk o η hη
  funext x
  let : Fact (Module.finrank ℝ (tangentSpace r k M x) = k) :=
    ⟨D04.tangentSpace_finrank hM x x.property⟩
  rw [metricVolume_eq hM o x]
  exact (D04.Dictionary.metricTopForm_exists_unique hk (o x x.property)).unique
    (hη x) (D04.Dictionary.metricTopForm_normalized _)

/-- The sign of the normalized volume form agrees with the orientation ray. -/
theorem metricTopForm_signed_gram {k : ℕ} {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [hdim : Fact (Module.finrank ℝ V = k)]
    (hk : 0 < k) (o : SpaceOrientation k V) (v : Fin k → V) :
    metricTopForm o v = Real.sign (o.someVector v) * gramDensity v := by
  let b := o.finOrthonormalBasis hk hdim.out
  have hb : b.toBasis.orientation = o := o.finOrthonormalBasis_orientation hk hdim.out
  have hp : 0 < o.someVector b.toBasis := (D04.Orientations.representative_pos_iff o b.toBasis).mpr hb
  have he : o.someVector v = o.someVector b.toBasis * metricTopForm o v := by
    conv_lhs => rw [o.someVector.eq_smul_basis_det b.toBasis]
    change o.someVector b.toBasis * b.toBasis.det v = _
    exact congrArg (fun f : Covector V k => o.someVector b.toBasis * f v)
      (o.volumeForm_robust b hb).symm
  have hs : Real.sign (o.someVector v) = Real.sign (metricTopForm o v) := by
    rw [he, D04.Orientations.sign_mul, Real.sign_of_pos hp, one_mul]
  have hg : |metricTopForm o v| = gramDensity v := D04.Dictionary.metricTopForm_gram o v
  rw [← hg, hs]
  rcases lt_trichotomy (metricTopForm o v) 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h]; ring
  · rw [h]; simp
  · rw [Real.sign_of_pos h, abs_of_pos h, one_mul]

theorem metricVolume_pullback :
    Specs.D04.C14.MetricTopFormsAndDensities.metricVolume_pullbackType := by
  intro r k n M hM hk o c u hu
  let x : M := ⟨c.toFun u, (c.map_source hu).1⟩
  let : Fact (Module.finrank ℝ (tangentSpace r k M x) = k) :=
    ⟨D04.tangentSpace_finrank hM x x.property⟩
  let v := fun i => tangentChartMap c u hu (standardBasis k i)
  have he : tangentPullback (metricVolume o) c u hu (standardBasis k) =
      chartSign o c u hu * chartDensity c u := by
    change metricVolume o x v = _
    rw [metricVolume_eq hM o x, metricTopForm_signed_gram hk]
    rfl
  rw [(tangentPullback (metricVolume o) c u hu).eq_smul_basis_det (standardBasis k), he]
  rfl

theorem metricVolume_positive_chart :
    Specs.D04.C14.MetricTopFormsAndDensities.metricVolume_positive_chartType := by
  intro r k n M hM hk o c u hu hs
  rw [metricVolume_pullback hM hk o c u hu, hs, one_mul]

theorem metricVolume_reverse :
    Specs.D04.C14.MetricTopFormsAndDensities.metricVolume_reverseType := by
  intro r k n M o
  funext x
  dsimp [metricVolume, Specs.D04.C14.MetricTopFormsAndDensities.Model.metricVolume]
  split_ifs with h
  · let : Fact (Module.finrank ℝ (tangentSpace r k M x) = k) := ⟨h⟩
    exact D04.Dictionary.metricTopForm_reverse _
  · simp

theorem metricVolume_abs_density :
    Specs.D04.C14.MetricTopFormsAndDensities.metricVolume_abs_densityType := by
  intro r k n M hM o x v
  let : Fact (Module.finrank ℝ (tangentSpace r k M x) = k) :=
    ⟨D04.tangentSpace_finrank hM x x.property⟩
  rw [metricVolume_eq hM o x]
  exact D04.Dictionary.metricTopForm_gram _ v

theorem density_chart : Specs.D04.C14.MetricTopFormsAndDensities.density_chartType := by
  intro r k n M c u hu
  rfl

theorem density_zero : Specs.D04.C14.MetricTopFormsAndDensities.density_zeroType := by
  intro r n M x v
  simp [tangentDensity, Specs.D04.C14.MetricTopFormsAndDensities.Model.tangentDensity,
    gramDensity, Matrix.det_isEmpty]

theorem metricVolume_zero : Specs.D04.C14.MetricTopFormsAndDensities.metricVolume_zeroType := by
  intro r n M o x v
  rfl

theorem zeroMetricVolume_pullback :
    Specs.D04.C14.MetricTopFormsAndDensities.zeroMetricVolume_pullbackType := by
  intro r n M o c u hu
  ext v
  simp [tangentPullback, Specs.D04.C14.MetricTopFormsAndDensities.Model.tangentPullback,
    zeroMetricVolume, Specs.D04.C14.MetricTopFormsAndDensities.Model.zeroMetricVolume,
    scalarCovector, omega, Module.Basis.det_isEmpty]


/-- Gram matrices transform by congruence under change of their columns. -/
theorem gram_linear_change {k : ℕ} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (F : E k →ₗ[ℝ] V) (A : E k →ₗ[ℝ] E k) :
    Matrix.gram ℝ (fun i => F (A (standardBasis k i))) =
      (LinearMap.toMatrix (standardBasis k) (standardBasis k) A).transpose *
        Matrix.gram ℝ (fun i => F (standardBasis k i)) *
          LinearMap.toMatrix (standardBasis k) (standardBasis k) A := by
  let B := LinearMap.toMatrix (standardBasis k) (standardBasis k) A
  have he (i : Fin k) : A (standardBasis k i) = ∑ j, B j i • standardBasis k j :=
    by simpa only [B, LinearMap.toMatrix_apply] using
      ((standardBasis k).sum_repr (A (standardBasis k i))).symm
  ext i j
  simp only [Matrix.gram_apply, he, map_sum, map_smul, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.gram_apply]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  dsimp [B]
  ring

theorem gramDensity_linear_change {k : ℕ} {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (F : E k →ₗ[ℝ] V) (A : E k →ₗ[ℝ] E k) :
    gramDensity (fun i => F (A (standardBasis k i))) =
      |LinearMap.det A| * gramDensity (fun i => F (standardBasis k i)) := by
  change Real.sqrt (Matrix.gram ℝ _).det = _
  rw [gram_linear_change, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose,
    LinearMap.det_toMatrix]
  rw [show LinearMap.det A * (Matrix.gram ℝ (fun i => F (standardBasis k i))).det *
      LinearMap.det A = (LinearMap.det A)^2 *
        (Matrix.gram ℝ (fun i => F (standardBasis k i))).det by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rfl

theorem density_linear_change :
    Specs.D04.C14.MetricTopFormsAndDensities.density_linear_changeType := by
  intro r k n M x F A
  exact gramDensity_linear_change _ _

theorem matrixOfLinearMap_columns {k n : ℕ} (F : E k →ₗ[ℝ] E n) :
    matrixOfLinearMap F = Matrix.of (fun i j => F (standardBasis k j) i) := by
  ext i j
  exact D04.matrixOfLinearMap_apply F i j

theorem chartDensity_matrix :
    Specs.D04.C14.MetricTopFormsAndDensities.chartDensity_matrixType := by
  intro r k n M c u
  change Real.sqrt (Matrix.gram ℝ (fun i => chartDifferential c u (standardBasis k i))).det = _
  rw [Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin n) ℝ)]
  rw [matrixOfLinearMap_columns]
  simp only [Matrix.conjTranspose_eq_transpose_of_trivial]
  rfl

theorem chartDensity_positive :
    Specs.D04.C14.MetricTopFormsAndDensities.chartDensity_positiveType := by
  intro r k n M c hr u hu
  apply Real.sqrt_pos.mpr
  exact (Matrix.posDef_gram_of_linearIndependent
    ((standardBasis k).linearIndependent.map' (chartDifferential c u).toLinearMap
      (LinearMap.ker_eq_bot.mpr (D04.EmbeddedChart.differential_injective c hr hu)))).det_pos

theorem chartDensity_reparametrize :
    Specs.D04.C14.MetricTopFormsAndDensities.chartDensity_reparametrizeType := by
  intro r k n M c d hr h hm he u hu A hA
  have hd : chartDifferential c u = (chartDifferential d (h u)).comp A := by
    apply (D04.EmbeddedChart.source_uniqueDiff c u hu).eq
      (D04.EmbeddedChart.hasDifferential c hr hu)
    exact ((D04.EmbeddedChart.hasDifferential d hr (hm hu)).comp u hA hm).congr'
      (fun v hv => he hv) hu
  change gramDensity _ = _
  rw [hd]
  exact gramDensity_linear_change (chartDifferential d (h u)).toLinearMap A.toLinearMap

theorem chartDensity_transition :
    Specs.D04.C14.MetricTopFormsAndDensities.chartDensity_transitionType := by
  intro r k n M c d hr hkn u hu
  obtain ⟨A, hA, _⟩ := D04.chart_transition_derivatives c d hr hkn u hu
  have he : chartDifferential c u =
      (chartDifferential d (chartTransition c d u)).comp A.toContinuousLinearMap := by
    apply (D04.EmbeddedChart.overlap_uniqueDiff c d u hu).eq
      ((D04.EmbeddedChart.hasDifferential c hr hu.1).mono inter_subset_left)
    exact ((D04.EmbeddedChart.hasDifferential d hr (D04.EmbeddedChart.transition_mem c d hu).1).comp u hA
      (fun v hv => (D04.EmbeddedChart.transition_mem c d hv).1)).congr'
      (fun v hv => (d.right_inv _ ⟨(c.map_source hv.1).1, hv.2⟩).symm) hu
  rw [hA.fderivWithin (D04.EmbeddedChart.overlap_uniqueDiff c d u hu)]
  change gramDensity _ = _
  rw [he]
  exact gramDensity_linear_change (chartDifferential d _).toLinearMap A.toLinearEquiv.toLinearMap

theorem gram_speed : Specs.D04.C14.MetricTopFormsAndDensities.gram_speedType := by
  intro n A
  change Real.sqrt (Matrix.det (fun i j : Fin 1 => inner ℝ (A (standardBasis 1 i))
    (A (standardBasis 1 j)))) = _
  rw [Matrix.det_fin_one, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem gram_full_dimension :
    Specs.D04.C14.MetricTopFormsAndDensities.gram_full_dimensionType := by
  intro n A
  change Real.sqrt (Matrix.gram ℝ (fun i => A (standardBasis n i))).det = _
  rw [Matrix.gram_eq_conjTranspose_mul (EuclideanSpace.basisFun (Fin n) ℝ),
    Matrix.det_mul, Matrix.det_conjTranspose]
  simp only [star_trivial]
  rw [matrixOfLinearMap_columns]
  exact Real.sqrt_mul_self_eq_abs _


/-- Local C¹ extendibility gives continuity of the full chart differential,
including at flat-boundary points. -/
theorem chartDifferential_continuous {r : ℕ∞ω} {k n : ℕ} {M : Set (E n)}
    (c : EmbeddedChart r k n M) (hr : ManifoldRegularity r) :
    ContinuousOn (chartDifferential c) c.source := by
  have hc : ContDiffOn ℝ r c.toFun c.source := by
    intro u hu
    obtain ⟨W, g, hW, huW, he, hg, _⟩ := c.regular u hu
    exact ((hg.contDiffAt (hW.mem_nhds huW)).contDiffWithinAt).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (inter_mem self_mem_nhdsWithin
        (mem_nhdsWithin_of_mem_nhds (hW.mem_nhds huW))) he.symm)
      (he ⟨hu, huW⟩).symm
  exact hc.continuousOn_fderivWithin (fun u hu => D04.EmbeddedChart.source_uniqueDiff c u hu) hr.1

theorem chartDensity_continuous :
    Specs.D04.C14.MetricTopFormsAndDensities.chartDensity_continuousType := by
  intro r k n M c hr
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hd : Continuous (fun u : c.source => chartDifferential c u) :=
    (chartDifferential_continuous c hr).domRestrict
  have hcol (i : Fin k) : Continuous (fun u : c.source => chartDifferential c u (standardBasis k i)) :=
    hd.clm_apply continuous_const
  have hg : Continuous (fun u : c.source => Matrix.gram ℝ
      (fun i => chartDifferential c u (standardBasis k i))) :=
    continuous_matrix (fun i j => (hcol i).inner (hcol j))
  exact hg.matrix_det.sqrt

theorem metricVolume_continuous :
    Specs.D04.C14.MetricTopFormsAndDensities.metricVolume_continuousType := by
  intro r k n M o c
  have he (u : c.source) :
      tangentPullback (metricVolume o.atPoint) c u u.property (standardBasis k) =
        chartSign o.atPoint c u u.property * chartDensity c u := by
    rw [metricVolume_pullback o.manifold o.positive_dimension]
    simp only [smul_apply, smul_eq_mul, omega, Module.Basis.det_self, mul_one]
  simp_rw [he]
  exact (o.locally_constant c).continuous.mul
    ((chartDensity_continuous c o.manifold.1).domRestrict)

/-- The Euclidean cross product and the two-column Gram determinant have
identical squares; nonnegative square roots give the surface factor. -/
theorem cross_norm_sq (v w : E 3) :
    inner ℝ v v * inner ℝ w w - inner ℝ v w * inner ℝ w v =
      ‖euclideanCross v w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [euclideanCross, EuclideanSpace.inner_eq_star_dotProduct,
    star_trivial]
  rw [cross_dot_cross]
  ring

theorem gram_cross : Specs.D04.C14.MetricTopFormsAndDensities.gram_crossType := by
  intro A
  change Real.sqrt (Matrix.det (fun i j : Fin 2 => inner ℝ (A (standardBasis 2 i))
    (A (standardBasis 2 j)))) = _
  rw [Matrix.det_fin_two, cross_norm_sq, Real.sqrt_sq (norm_nonneg _)]

abbrev TangentTopField := @Specs.D04.C14.MetricTopFormsAndDensities.Model.TangentTopField
abbrev metricVolume := @Specs.D04.C14.MetricTopFormsAndDensities.Model.metricVolume
abbrev tangentDensity := @Specs.D04.C14.MetricTopFormsAndDensities.Model.tangentDensity
abbrev chartDensity := @Specs.D04.C14.MetricTopFormsAndDensities.Model.chartDensity
abbrev tangentPullback := @Specs.D04.C14.MetricTopFormsAndDensities.Model.tangentPullback
abbrev zeroMetricVolume := @Specs.D04.C14.MetricTopFormsAndDensities.Model.zeroMetricVolume


end D04MetricDensity
