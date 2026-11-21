import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.ChartRegionStokes
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ContinuousGraphFlux
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.BoundaryGraphDirections
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Finiteness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Stokes for the original chart regions of paper.tex 4972–4987.
The direct continuous-graph proof includes all noncuspidal reflex corners:
it proves local flux in two independent inward directions, identifies the
actual parametrized boundary integrals, and applies a finite smooth partition
of unity. A compact cutoff removes global support assumptions. Earlier
corner-removal estimates and limit lemmas remain as additional proved helpers.
-/

noncomputable section
open Set MeasureTheory Filter Metric Module
open scoped Topology ContDiff Manifold

namespace P202.ChartRegionStokes
open P202Specs.PlanarRegionTopology P202Specs.ChartRegionStokes

/-- Smoothness on the original open neighborhood is enough to integrate
d omega on the actual compact closure. No support assumption is needed. -/
theorem exteriorCoefficient_continuousOn {U : Set Plane} (hU : IsOpen U)
    {omega : OneForm} (homega : ContDiffOn ℝ ∞ omega U) :
    ContinuousOn (exteriorCoefficient omega) U := by
  have hd := homega.continuousOn_fderiv_of_isOpen hU (by simp)
  exact (hd.clm_apply continuousOn_const |>.clm_apply continuousOn_const).sub
    (hd.clm_apply continuousOn_const |>.clm_apply continuousOn_const)

theorem bulk_integrable (R : PlanarRegion) {U : Set Plane} (hU : IsOpen U)
    (hRU : R.carrier ⊆ U) {omega : OneForm} (homega : ContDiffOn ℝ ∞ omega U) :
    IntegrableOn (exteriorCoefficient omega) R.carrier :=
  ((exteriorCoefficient_continuousOn hU homega).mono hRU).integrableOn_compact
    R.compact_closure

theorem realLift_continuous (c : RegularJordanCurve) :
    Continuous (realLift c.parametrization) :=
  c.parametrization.continuous.comp (AddCircle.continuous_mk' (1 : ℝ))

/-- The given one-sided extensions bound the actual derivative locally,
even when that derivative is set to zero at a nonsmooth join. -/
theorem realLift_deriv_locally_bounded (c : RegularJordanCurve) (t : ℝ) :
    ∃ N ∈ 𝓝 t, Bornology.IsBounded ((deriv (realLift c.parametrization)) '' N) := by
  obtain ⟨d, l, r, hd, hl, hr, hel, her, _⟩ := c.regular_joins t
  let J := Icc (t - d / 2) (t + d / 2)
  have hJ : J ⊆ Ioo (t - d) (t + d) := by
    intro x hx
    dsimp [J] at hx
    constructor <;> linarith [hx.1, hx.2]
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hl.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).mono hJ)
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hr.continuousOn_deriv_of_isOpen isOpen_Ioo (by simp)).mono hJ)
  have hel' : EqOn (deriv l) (deriv (realLift c.parametrization)) (Ioo (t - d) t) :=
    (hel.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  have her' : EqOn (deriv r) (deriv (realLift c.parametrization)) (Ioo t (t + d)) :=
    (her.mono Ioo_subset_Icc_self).deriv isOpen_Ioo
  refine ⟨Ioo (t - d / 2) (t + d / 2), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨max (max L R) ‖deriv (realLift c.parametrization) t‖, ?_⟩
  rintro y ⟨s, hs, rfl⟩
  have hsJ : s ∈ J := ⟨hs.1.le, hs.2.le⟩
  rcases lt_trichotomy s t with hst | rfl | hts
  · rw [← hel' (by constructor <;> linarith [hs.1])]
    exact (hL s hsJ).trans ((le_max_left L R).trans (le_max_left _ _))
  · exact le_max_right _ _
  · rw [← her' (by constructor <;> linarith [hs.2])]
    exact (hR s hsJ).trans ((le_max_right L R).trans (le_max_left _ _))

theorem realLift_deriv_bounded (c : RegularJordanCurve) :
    ∃ L : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (realLift c.parametrization) t‖ ≤ L := by
  have hb := Bornology.isBounded_image_of_isLocallyBounded_of_isCompact
    (s := Icc (0 : ℝ) 1) isCompact_Icc (realLift_deriv_locally_bounded c)
  obtain ⟨L, hL⟩ := hb.exists_norm_le
  exact ⟨L, fun t ht => hL _ (mem_image_of_mem _ ht)⟩

/-- Representatives of the finite join set in one positive period. -/
def joinTimes (c : RegularJordanCurve) : Set ℝ :=
  (fun z : ParameterCircle => ((AddCircle.equivIoc (1 : ℝ) 0) z : ℝ)) ''
    (c.joins : Set ParameterCircle)

theorem joinTimes_finite (c : RegularJordanCurve) : (joinTimes c).Finite :=
  c.joins.finite_toSet.image _

theorem mem_joinTimes_of_join (c : RegularJordanCurve) {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) 1) (hj : (t : ParameterCircle) ∈ c.joins) :
    t ∈ joinTimes c := by
  refine ⟨(t : ParameterCircle), hj, ?_⟩
  exact AddCircle.equivIoc_coe_of_mem (by simpa using ht)

/-- Omitting just the joins leaves the actual curve integrand unchanged
almost everywhere. This fact holds independently of integrability. -/
theorem boundaryIntegrand_ae_eq (omega : OneForm) (c : RegularJordanCurve) :
    boundaryIntegrand omega c =ᵐ[volume.restrict (Ioc (0 : ℝ) 1)]
      (fun t => omega (realLift c.parametrization t) (deriv (realLift c.parametrization) t)) := by
  filter_upwards [ae_restrict_of_ae ((joinTimes_finite c).countable.ae_notMem volume),
    ae_restrict_mem measurableSet_Ioc] with t ht hI
  have hj : (t : ParameterCircle) ∉ c.joins := fun hj =>
    ht (mem_joinTimes_of_join c hI hj)
  simp [boundaryIntegrand, hj]

theorem componentIntegral_eq_unmasked (omega : OneForm) (c : RegularJordanCurve) :
    componentIntegral omega c = ∫ t in (0 : ℝ)..1,
      omega (realLift c.parametrization t) (deriv (realLift c.parametrization) t) := by
  apply intervalIntegral.integral_congr_ae_restrict
  simpa only [uIoc_of_le zero_le_one] using boundaryIntegrand_ae_eq omega c

theorem realLift_mem_carrier (R : PlanarRegion) (i : Fin R.boundaryCount) (t : ℝ) :
    realLift (R.curve i).parametrization t ∈ R.carrier := by
  apply frontier_subset_closure
  rw [R.boundary_eq]
  exact mem_iUnion.mpr ⟨i, mem_range_self _⟩

/-- Boundary integrability follows from the original regular-join
hypotheses. In particular it is not an extra input to the Stokes theorem. -/
theorem boundary_integrable (R : PlanarRegion) {U : Set Plane}
    (hRU : R.carrier ⊆ U) {omega : OneForm} (homega : ContinuousOn omega U)
    (i : Fin R.boundaryCount) :
    IntervalIntegrable (boundaryIntegrand omega (R.curve i)) volume 0 1 := by
  let c := R.curve i
  let f := realLift c.parametrization
  have hf : Continuous f := realLift_continuous c
  have hcomp : Continuous (fun t => omega (f t)) :=
    homega.comp_continuous hf (fun t => hRU (realLift_mem_carrier R i t))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hcomp.continuousOn : ContinuousOn (fun t => omega (f t)) (Icc (0 : ℝ) 1))
  obtain ⟨L, hL⟩ := realLift_deriv_bounded c
  have hMpos : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hm : Measurable (fun t => omega (f t) (deriv f t)) :=
    isBoundedBilinearMap_apply.continuous.measurable.comp
      (hcomp.measurable.prodMk (measurable_deriv f))
  have hint : IntegrableOn (fun t => omega (f t) (deriv f t)) (Icc (0 : ℝ) 1) := by
    apply (integrableOn_const (C := M * L) (μ := volume) (s := Icc (0 : ℝ) 1)
      (isCompact_Icc.measure_ne_top)).mono'
      hm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact ((omega (f t)).le_opNorm _).trans
      (mul_le_mul (hM t ht) (hL t ht) (norm_nonneg _) hMpos)
  have hi : IntervalIntegrable (fun t => omega (f t) (deriv f t)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hint
  apply hi.congr_ae
  simpa only [uIoc_of_le zero_le_one] using (boundaryIntegrand_ae_eq omega c).symm

/-- Splitting at arbitrary ordered parameter cuts gives the usual finite
sum of arc integrals. Taking cuts at all join times gives the regular arc
interpretation of the specification. Endpoints have zero measure. -/
theorem componentIntegral_eq_sum (R : PlanarRegion) {U : Set Plane}
    (hRU : R.carrier ⊆ U) {omega : OneForm} (homega : ContinuousOn omega U)
    (i : Fin R.boundaryCount) (a : ℕ → ℝ) (n : ℕ)
    (ha : ∀ k ≤ n, a k ∈ Icc (0 : ℝ) 1) (hzero : a 0 = 0) (hone : a n = 1) :
    componentIntegral omega (R.curve i) =
      ∑ k ∈ Finset.range n, ∫ t in a k..a (k + 1),
        omega (realLift (R.curve i).parametrization t)
          (deriv (realLift (R.curve i).parametrization) t) := by
  have hint := (boundary_integrable R hRU homega i).congr_ae
    (by simpa only [uIoc_of_le zero_le_one] using
      boundaryIntegrand_ae_eq omega (R.curve i))
  rw [componentIntegral_eq_unmasked]
  symm
  convert intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := n) ?_ using 1
  · rw [hzero, hone]
  · intro k hk
    apply hint.mono_set
    apply uIcc_subset_uIcc
    · simpa only [uIcc_of_le zero_le_one] using ha k hk.le
    · simpa only [uIcc_of_le zero_le_one] using ha (k + 1) hk

/-- A bound for the integral of a one-form on any parametrized arc.
The coefficient bound and speed bound are independent, and the signed
parameter interval can have either orientation. -/
theorem arc_integral_bound (omega : OneForm) (c : ℝ → Plane)
    {a b M L : ℝ} (hM : 0 ≤ M)
    (homega : ∀ t ∈ uIoc a b, ‖omega (c t)‖ ≤ M)
    (hc : ∀ t ∈ uIoc a b, ‖deriv c t‖ ≤ L) :
    ‖∫ t in a..b, omega (c t) (deriv c t)‖ ≤ M * L * |b - a| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro t ht
  exact (omega (c t)).le_opNorm (deriv c t) |>.trans
    (mul_le_mul (homega t ht) (hc t ht) (norm_nonneg _) hM)

/-- Any portion of a removed coordinate disk has area at most pi epsilon².
This includes arbitrary measurable or nonmeasurable subsets: the measure
inequality is an outer-measure inequality. -/
theorem removed_area_bound (p : Plane) {epsilon : ℝ} (he : 0 ≤ epsilon)
    {A : Set Plane} (hA : A ⊆ closedBall p epsilon) :
    volume.real A ≤ Real.pi * epsilon ^ 2 := by
  have hvol : volume (closedBall p epsilon) ≠ ⊤ := by
    rw [EuclideanSpace.volume_closedBall_fin_two]
    finiteness
  calc
    volume.real A ≤ volume.real (closedBall p epsilon) := measureReal_mono hA hvol
    _ = Real.pi * epsilon ^ 2 := by
      simp [Measure.real, EuclideanSpace.volume_closedBall_fin_two, he,
        ENNReal.toReal_mul, ENNReal.toReal_pow, Real.pi_nonneg, mul_comm]

/-- The removed bulk integral has the source's quadratic estimate. -/
theorem removed_integral_bound (p : Plane) {epsilon M : ℝ}
    (he : 0 ≤ epsilon) (hM : 0 ≤ M) {A : Set Plane}
    (hA : A ⊆ closedBall p epsilon) (f : Plane → ℝ)
    (hf : ∀ x ∈ A, ‖f x‖ ≤ M) :
    ‖∫ x in A, f x‖ ≤ M * Real.pi * epsilon ^ 2 := by
  have hfinite : volume A < ⊤ :=
    lt_of_le_of_lt (measure_mono hA) (isCompact_closedBall p epsilon).measure_lt_top
  calc
    ‖∫ x in A, f x‖ ≤ M * volume.real A :=
      norm_setIntegral_le_of_norm_le_const hfinite hf
    _ ≤ M * (Real.pi * epsilon ^ 2) :=
      mul_le_mul_of_nonneg_left (removed_area_bound p he hA) hM
    _ = M * Real.pi * epsilon ^ 2 := by ring

/-- All corners can be removed simultaneously, with an explicit constant
equal to the number of corners. Disjointness is not needed for the estimate. -/
theorem removed_union_integral_bound {N : ℕ} (p : Fin N → Plane)
    {epsilon M : ℝ} (he : 0 ≤ epsilon) (hM : 0 ≤ M)
    {A : Set Plane} (hA : A ⊆ ⋃ i, closedBall (p i) epsilon)
    (f : Plane → ℝ) (hf : ∀ x ∈ A, ‖f x‖ ≤ M) :
    ‖∫ x in A, f x‖ ≤ (N : ℝ) * M * Real.pi * epsilon ^ 2 := by
  have hcompact : IsCompact (⋃ i, closedBall (p i) epsilon) :=
    isCompact_iUnion (fun i => isCompact_closedBall (p i) epsilon)
  have hfinite : volume A < ⊤ :=
    lt_of_le_of_lt (measure_mono hA) hcompact.measure_lt_top
  calc
    ‖∫ x in A, f x‖ ≤ M * volume.real A :=
      norm_setIntegral_le_of_norm_le_const hfinite hf
    _ ≤ M * volume.real (⋃ i, closedBall (p i) epsilon) :=
      mul_le_mul_of_nonneg_left (measureReal_mono hA hcompact.measure_ne_top) hM
    _ ≤ M * ∑ i, volume.real (closedBall (p i) epsilon) :=
      mul_le_mul_of_nonneg_left (measureReal_iUnion_fintype_le _) hM
    _ = (N : ℝ) * M * Real.pi * epsilon ^ 2 := by
      simp [Measure.real, EuclideanSpace.volume_closedBall_fin_two,
        ENNReal.toReal_mul, ENNReal.toReal_pow, he, Real.pi_nonneg]
      ring

theorem removed_integrals_tendsto_zero {N : ℕ} (p : Fin N → Plane)
    {epsilon : ℕ → ℝ} (he : ∀ n, 0 ≤ epsilon n)
    (hlim : Tendsto epsilon atTop (𝓝 0)) {M : ℝ} (hM : 0 ≤ M)
    (A : ℕ → Set Plane) (hA : ∀ n, A n ⊆ ⋃ i, closedBall (p i) (epsilon n))
    (f : Plane → ℝ) (hf : ∀ n x, x ∈ A n → ‖f x‖ ≤ M) :
    Tendsto (fun n => ∫ x in A n, f x) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => removed_union_integral_bound p (he n) hM
    (hA n) f (hf n))
  simpa using tendsto_const_nhds.mul (hlim.pow 2)

/-- Actual coordinate circle and its velocity, allowing any angular subarc. -/
def circlePoint (p : Plane) (epsilon theta : ℝ) : Plane :=
  p + epsilon • !₂[Real.cos theta, Real.sin theta]

def circleVelocity (epsilon theta : ℝ) : Plane :=
  epsilon • !₂[-Real.sin theta, Real.cos theta]

theorem circlePoint_hasDerivAt (p : Plane) (epsilon theta : ℝ) :
    HasDerivAt (circlePoint p epsilon) (circleVelocity epsilon theta) theta := by
  have h : HasDerivAt (fun t : ℝ => ![Real.cos t, Real.sin t])
      ![-Real.sin theta, Real.cos theta] theta := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact Real.hasDerivAt_cos theta
    · exact Real.hasDerivAt_sin theta
  have hv := (EuclideanSpace.equiv (Fin 2) ℝ).symm.hasFDerivAt.comp_hasDerivAt theta h
  change HasDerivAt (fun t => p + epsilon • !₂[Real.cos t, Real.sin t])
    (epsilon • !₂[-Real.sin theta, Real.cos theta]) theta
  exact (hv.const_smul epsilon).const_add p

theorem circleVelocity_norm (epsilon theta : ℝ) :
    ‖circleVelocity epsilon theta‖ = |epsilon| := by
  have hnorm : ‖(!₂[-Real.sin theta, Real.cos theta] : Plane)‖ = 1 := by
    have h := EuclideanSpace.real_norm_sq_eq
      (!₂[-Real.sin theta, Real.cos theta] : Plane)
    simp [Fin.sum_univ_two] at h
    rcases h with h | h
    · exact h
    · have hn := norm_nonneg (!₂[-Real.sin theta, Real.cos theta] : Plane)
      linarith
  simp [circleVelocity, norm_smul, hnorm, Real.norm_eq_abs]

/-- A circular portion contributes at most 2 pi M epsilon. No restriction
on convexity or on the angle of the original corner appears. -/
theorem circle_integral_bound (p : Plane) {epsilon M a b : ℝ}
    (he : 0 ≤ epsilon) (hM : 0 ≤ M) (hab : |b - a| ≤ 2 * Real.pi)
    (omega : OneForm)
    (homega : ∀ t ∈ uIoc a b, ‖omega (circlePoint p epsilon t)‖ ≤ M) :
    ‖∫ t in a..b, omega (circlePoint p epsilon t)
      (deriv (circlePoint p epsilon) t)‖ ≤ 2 * Real.pi * M * epsilon := by
  have hv : ∀ t ∈ uIoc a b, ‖deriv (circlePoint p epsilon) t‖ ≤ epsilon := by
    intro t _
    rw [(circlePoint_hasDerivAt p epsilon t).deriv, circleVelocity_norm, abs_of_nonneg he]
  calc
    ‖∫ t in a..b, omega (circlePoint p epsilon t)
        (deriv (circlePoint p epsilon) t)‖ ≤ M * epsilon * |b - a| :=
      arc_integral_bound omega (circlePoint p epsilon) hM homega hv
    _ ≤ M * epsilon * (2 * Real.pi) :=
      mul_le_mul_of_nonneg_left hab (mul_nonneg hM he)
    _ = 2 * Real.pi * M * epsilon := by ring

theorem circle_integrals_tendsto_zero (p : Plane) {epsilon : ℕ → ℝ}
    (he : ∀ n, 0 ≤ epsilon n) (hlim : Tendsto epsilon atTop (𝓝 0))
    {M : ℝ} (hM : 0 ≤ M) (a b : ℕ → ℝ)
    (hab : ∀ n, |b n - a n| ≤ 2 * Real.pi) (omega : OneForm)
    (homega : ∀ n t, t ∈ uIoc (a n) (b n) →
      ‖omega (circlePoint p (epsilon n) t)‖ ≤ M) :
    Tendsto (fun n => ∫ t in a n..b n, omega (circlePoint p (epsilon n) t)
      (deriv (circlePoint p (epsilon n)) t)) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun n => circle_integral_bound p (he n) hM (hab n)
    omega (homega n))
  simpa using tendsto_const_nhds.mul hlim

/-- A regular one-sided arc escapes the corner at at least a fixed
positive fraction of its initial speed. This is the quantitative fact
needed to control the original boundary portions cut out by a small disk. -/
theorem regular_arc_radial_lower_bound {c : ℝ → Plane} {v : Plane}
    (hc : HasDerivAt c v 0) (hv : v ≠ 0) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      (‖v‖ / 2) * t ≤ ‖c t - c 0‖ := by
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlim := hc.tendsto_slope_zero_right.norm
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ‖v‖ / 2 < ‖t⁻¹ • (c (0 + t) - c 0)‖ :=
    hlim.eventually (lt_mem_nhds (show ‖v‖ / 2 < ‖v‖ by linarith))
  obtain ⟨delta, hd, hdelta⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨delta, hd, fun t ht htd => ?_⟩
  have h := hdelta ⟨ht, htd⟩
  simp only [zero_add, norm_smul, Real.norm_eq_abs, abs_inv] at h
  have hmul := mul_lt_mul_of_pos_right h ht
  simpa [abs_of_pos ht, ne_of_gt ht, mul_assoc, mul_comm, mul_left_comm] using hmul.le

/-- Strict radial transversality follows from the first derivative and its
continuity. Using squared distance avoids differentiating the norm at the
corner itself. -/
theorem regular_arc_radial_inner_pos {c : ℝ → Plane} {v : Plane}
    (hc : HasDerivAt c v 0) (hv : v ≠ 0)
    (hd : ContinuousAt (deriv c) 0) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      0 < inner ℝ (c t - c 0) (deriv c t) := by
  have hvel : Tendsto (deriv c) (𝓝[>] (0 : ℝ)) (𝓝 v) := by
    rw [← hc.deriv]
    exact hd.tendsto.mono_left nhdsWithin_le_nhds
  have hlim := hc.tendsto_slope_zero_right.inner (𝕜 := ℝ) hvel
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      0 < inner ℝ (t⁻¹ • (c (0 + t) - c 0)) (deriv c t) :=
    hlim.eventually (lt_mem_nhds (real_inner_self_pos.mpr hv))
  obtain ⟨delta, hd, hdelta⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hevent
  refine ⟨delta, hd, fun t ht htd => ?_⟩
  have h := hdelta ⟨ht, htd⟩
  simp only [zero_add, real_inner_smul_left] at h
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr ht)).mp h

/-- A smooth regular incident arc meets all sufficiently small concentric
circles transversely, wherever it meets them. The level function is the
actual squared Euclidean distance from the corner. -/
theorem regular_arc_circle_transverse {c : ℝ → Plane} {O : Set ℝ}
    (hO : IsOpen O) (hzero : 0 ∈ O) (hc : ContDiffOn ℝ ∞ c O)
    (hv : deriv c 0 ≠ 0) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, 0 < t → t < delta →
      HasDerivAt (fun s => ‖c s - c 0‖ ^ 2)
        (2 * inner ℝ (c t - c 0) (deriv c t)) t ∧
      0 < 2 * inner ℝ (c t - c 0) (deriv c t) := by
  have hdiff : DifferentiableOn ℝ c O := hc.differentiableOn (by simp)
  have hcont := hc.continuousOn_deriv_of_isOpen hO (by simp)
  have hat : HasDerivAt c (deriv c 0) 0 :=
    (hdiff.differentiableAt (hO.mem_nhds hzero)).hasDerivAt
  obtain ⟨d, hd, hinner⟩ := regular_arc_radial_inner_pos hat hv
    (hcont.continuousAt (hO.mem_nhds hzero))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hzero)
  refine ⟨min d r, lt_min hd hr, fun t ht htd => ?_⟩
  have htO : t ∈ O := hball (by
    simpa [mem_ball, Real.dist_eq, abs_of_pos ht] using (lt_of_lt_of_le htd (min_le_right d r)))
  have htderiv := (hdiff.differentiableAt (hO.mem_nhds htO)).hasDerivAt
  exact ⟨(htderiv.sub_const (c 0)).norm_sq,
    mul_pos (by norm_num) (hinner t ht (lt_of_lt_of_le htd (min_le_left d r)))⟩

/-- The original incident arc removed by a disk has small integral too:
the bound is proportional to the distance of its endpoint from the corner.
Together with `circle_integral_bound`, this controls both kinds of boundary
terms, rather than discarding the original reflex-corner contributions. -/
theorem regular_arc_integral_bound (omega : OneForm) {c : ℝ → Plane} {v : Plane}
    (hc : HasDerivAt c v 0) (hv : v ≠ 0)
    (hd : ContinuousAt (deriv c) 0) (homega : ContinuousAt omega (c 0)) :
    ∃ delta C : ℝ, 0 < delta ∧ 0 < C ∧
      ∀ t : ℝ, 0 ≤ t → t < delta →
        ‖∫ s in (0 : ℝ)..t, omega (c s) (deriv c s)‖ ≤ C * ‖c t - c 0‖ := by
  let M := ‖omega (c 0)‖ + 1
  let L := ‖v‖ + 1
  have hM : 0 < M := by dsimp [M]; positivity
  have hL : 0 < L := by dsimp [L]; positivity
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hlim1 := (homega.comp hc.continuousAt).norm
  have hlim2 : Tendsto (fun s => ‖deriv c s‖) (𝓝 (0 : ℝ)) (𝓝 ‖v‖) := by
    rw [← hc.deriv]
    exact hd.norm
  have hbound : ∀ᶠ s in 𝓝 (0 : ℝ), ‖omega (c s)‖ ≤ M ∧ ‖deriv c s‖ ≤ L := by
    filter_upwards [hlim1.eventually (gt_mem_nhds (lt_add_one ‖omega (c 0)‖)),
      hlim2.eventually (gt_mem_nhds (lt_add_one ‖v‖))] with s hs1 hs2
    exact ⟨hs1.le, hs2.le⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hbound
  obtain ⟨d, hdpos, hrad⟩ := regular_arc_radial_lower_bound hc hv
  let C := 2 * M * L / ‖v‖
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨min d r, C, lt_min hdpos hr, hC, fun t ht htd => ?_⟩
  rcases ht.eq_or_lt with rfl | htpos
  · simp
  have hb : ∀ s ∈ uIoc 0 t, ‖omega (c s)‖ ≤ M ∧ ‖deriv c s‖ ≤ L := by
    intro s hs
    rw [uIoc_of_le ht] at hs
    apply hball
    simpa [mem_ball, Real.dist_eq, abs_of_pos hs.1] using
      (lt_of_le_of_lt hs.2 (lt_of_lt_of_le htd (min_le_right d r)))
  have hlow := hrad t htpos (lt_of_lt_of_le htd (min_le_left d r))
  have hcancel : C * (‖v‖ / 2) = M * L := by
    dsimp [C]
    field_simp
  calc
    ‖∫ s in (0 : ℝ)..t, omega (c s) (deriv c s)‖ ≤ M * L * |t - 0| :=
      arc_integral_bound omega c hM.le (fun s hs => (hb s hs).1)
        (fun s hs => (hb s hs).2)
    _ = C * ((‖v‖ / 2) * t) := by rw [sub_zero, abs_of_pos htpos, ← hcancel]; ring
    _ ≤ C * ‖c t - c 0‖ := mul_le_mul_of_nonneg_left hlow hC.le

/-- Small circles cut a regular incident arc exactly once near its endpoint.
The existence and uniqueness are conclusions of the original smoothness and
nonzero velocity, rather than extra assumptions about a truncation. -/
theorem regular_arc_small_circle_unique {c : ℝ → Plane} {O : Set ℝ}
    (hO : IsOpen O) (hzero : 0 ∈ O) (hc : ContDiffOn ℝ ∞ c O)
    (hv : deriv c 0 ≠ 0) :
    ∃ delta rho : ℝ, 0 < delta ∧ 0 < rho ∧ Icc 0 delta ⊆ O ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < rho →
        (∃! t : ℝ, t ∈ Ioo 0 delta ∧ ‖c t - c 0‖ = epsilon) ∧
        (∀ t ∈ Ioo 0 delta, ‖c t - c 0‖ = epsilon →
          HasDerivAt (fun s => ‖c s - c 0‖ ^ 2)
            (2 * inner ℝ (c t - c 0) (deriv c t)) t ∧
          0 < 2 * inner ℝ (c t - c 0) (deriv c t)) := by
  obtain ⟨d, hd, htrans⟩ := regular_arc_circle_transverse hO hzero hc hv
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hzero)
  let delta := min d r / 2
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdelta_d : delta < d := by
    dsimp [delta]
    linarith [min_le_left d r, lt_min hd hr]
  have hdelta_r : delta < r := by
    dsimp [delta]
    linarith [min_le_right d r, lt_min hd hr]
  have hsub : Icc 0 delta ⊆ O := by
    intro t ht
    apply hball
    simpa only [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1] using
      ht.2.trans_lt hdelta_r
  have hcont : ContinuousOn (fun t => ‖c t - c 0‖ ^ 2) (Icc 0 delta) :=
    ((hc.continuousOn.mono hsub).sub continuousOn_const).norm.pow 2
  have hmono : StrictMonoOn (fun t => ‖c t - c 0‖ ^ 2) (Icc 0 delta) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 delta) hcont
    intro t ht
    rw [interior_Icc] at ht
    obtain ⟨hderiv, hpos⟩ := htrans t ht.1 (ht.2.trans hdelta_d)
    rw [hderiv.deriv]
    exact hpos
  have hrho : 0 < ‖c delta - c 0‖ := by
    have hp := hmono (left_mem_Icc.mpr hdelta.le) (right_mem_Icc.mpr hdelta.le) hdelta
    have hsq : 0 < ‖c delta - c 0‖ ^ 2 := by simpa using hp
    nlinarith [norm_nonneg (c delta - c 0)]
  refine ⟨delta, ‖c delta - c 0‖, hdelta, hrho, hsub, fun epsilon he her => ?_⟩
  have hsq : epsilon ^ 2 ∈ Icc (‖c 0 - c 0‖ ^ 2) (‖c delta - c 0‖ ^ 2) := by
    simp only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    constructor <;> nlinarith
  obtain ⟨t, ht, hte⟩ := intermediate_value_Icc hdelta.le hcont hsq
  have hnorm : ‖c t - c 0‖ = epsilon := by nlinarith [norm_nonneg (c t - c 0)]
  have htpos : 0 < t := by
    by_contra h
    have htzero : t = 0 := le_antisymm (le_of_not_gt h) ht.1
    simp [htzero] at hnorm
    linarith
  have htlt : t < delta := by
    by_contra h
    have htd : t = delta := le_antisymm ht.2 (le_of_not_gt h)
    rw [htd] at hnorm
    linarith
  constructor
  · refine ⟨t, ⟨⟨htpos, htlt⟩, hnorm⟩, ?_⟩
    intro u hu
    apply hmono.injOn (Ioo_subset_Icc_self hu.1) ht
    simp only [hu.2, hnorm]
  · intro u hu _
    exact htrans u hu.1 (hu.2.trans hdelta_d)

/-- Two short outward incident parameters represent distinct points of the
actual Jordan curve, including when the center parameter is a period seam. -/
theorem realLift_ne_of_opposite_parameters (c : RegularJordanCurve) (t : ℝ)
    {l r : ℝ} (hl : 0 < l) (hr : 0 < r) (hsum : l + r < 1) :
    realLift c.parametrization (t - l) ≠ realLift c.parametrization (t + r) := by
  intro heq
  have hparam : ((t - l : ℝ) : ParameterCircle) = ((t + r : ℝ) : ParameterCircle) :=
    c.injective heq
  have hx : t - l ∈ Ico (t - l) ((t - l) + (1 : ℝ)) := by
    constructor <;> linarith
  have hy : t + r ∈ Ico (t - l) ((t - l) + (1 : ℝ)) := by
    constructor <;> linarith
  have hreal : t - l = t + r :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico hx hy).mp hparam
  linarith

/-- Both actual incident portions of a regular Jordan curve meet every
sufficiently small centered circle exactly once. Squared radial distance
has positive derivative at the two crossings, with outward-directed
parameters on both sides, including the reversed incoming portion. -/
theorem regularJoin_small_circle_crossings (c : RegularJordanCurve) (t : ℝ) :
    ∃ dl dr rho : ℝ, 0 < dl ∧ 0 < dr ∧ 0 < rho ∧
      dl < 1 / 4 ∧ dr < 1 / 4 ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < rho →
        ((∃! h : ℝ, h ∈ Ioo 0 dl ∧
          ‖realLift c.parametrization (t - h) - realLift c.parametrization t‖ = epsilon) ∧
        (∀ h ∈ Ioo 0 dl,
          ‖realLift c.parametrization (t - h) - realLift c.parametrization t‖ = epsilon →
          ∃ v : ℝ, 0 < v ∧ HasDerivAt
            (fun s => ‖realLift c.parametrization (t - s) -
              realLift c.parametrization t‖ ^ 2) v h)) ∧
        ((∃! h : ℝ, h ∈ Ioo 0 dr ∧
          ‖realLift c.parametrization (t + h) - realLift c.parametrization t‖ = epsilon) ∧
        (∀ h ∈ Ioo 0 dr,
          ‖realLift c.parametrization (t + h) - realLift c.parametrization t‖ = epsilon →
          ∃ v : ℝ, 0 < v ∧ HasDerivAt
            (fun s => ‖realLift c.parametrization (t + s) -
              realLift c.parametrization t‖ ^ 2) v h)) := by
  obtain ⟨d, l, r, hd, hl, hr, hel, her, hvl, hvr, _⟩ := c.regular_joins t
  let d0 := min d (1 / 4)
  have hd0 : 0 < d0 := lt_min hd (by norm_num)
  have hd0d : d0 ≤ d := min_le_left _ _
  have hd0small : d0 ≤ 1 / 4 := min_le_right _ _
  let cl : ℝ → Plane := fun s => l (t - s)
  let cr : ℝ → Plane := fun s => r (t + s)
  have hcl : ContDiffOn ℝ ∞ cl (Ioo (-d0) d0) := by
    apply hl.comp (contDiff_const.sub contDiff_id).contDiffOn
    intro s hs
    change t - d < t - s ∧ t - s < t + d
    constructor <;> linarith [hs.1, hs.2, hd0d]
  have hcr : ContDiffOn ℝ ∞ cr (Ioo (-d0) d0) := by
    apply hr.comp (contDiff_const.add contDiff_id).contDiffOn
    intro s hs
    change t - d < t + s ∧ t + s < t + d
    constructor <;> linarith [hs.1, hs.2, hd0d]
  have hvcl : deriv cl 0 ≠ 0 := by
    simpa [cl, deriv_comp_const_sub] using neg_ne_zero.mpr hvl
  have hvcr : deriv cr 0 ≠ 0 := by
    simpa [cr, deriv_comp_const_add] using hvr
  have hz : (0 : ℝ) ∈ Ioo (-d0) d0 := by constructor <;> linarith
  obtain ⟨dl, rl, hdl, hrl, hsubL, hL⟩ :=
    regular_arc_small_circle_unique isOpen_Ioo hz hcl hvcl
  obtain ⟨dr, rr, hdr, hrr, hsubR, hR⟩ :=
    regular_arc_small_circle_unique isOpen_Ioo hz hcr hvcr
  have hdl_d0 : dl < d0 := (hsubL (right_mem_Icc.mpr hdl.le)).2
  have hdl_d : dl < d := hdl_d0.trans_le hd0d
  have hdr_d0 : dr < d0 := (hsubR (right_mem_Icc.mpr hdr.le)).2
  have hdr_d : dr < d := hdr_d0.trans_le hd0d
  have hlzero : cl 0 = realLift c.parametrization t := by
    dsimp [cl]
    simpa using hel (by constructor <;> linarith : t ∈ Icc (t - d) t)
  have hrzero : cr 0 = realLift c.parametrization t := by
    dsimp [cr]
    simpa using her (by constructor <;> linarith : t ∈ Icc t (t + d))
  have hleq : EqOn cl (fun s => realLift c.parametrization (t - s)) (Ioo 0 dl) := by
    intro s hs
    exact hel (by constructor <;> linarith [hs.1, hs.2, hd0d])
  have hreq : EqOn cr (fun s => realLift c.parametrization (t + s)) (Ioo 0 dr) := by
    intro s hs
    exact her (by constructor <;> linarith [hs.1, hs.2, hd0d])
  have htransfer {f g : ℝ → Plane} {delta epsilon : ℝ}
      (hfg : EqOn f g (Ioo 0 delta)) (hfg0 : f 0 = g 0)
      (hu : ∃! h : ℝ, h ∈ Ioo 0 delta ∧ ‖f h - f 0‖ = epsilon)
      (htrans : ∀ h ∈ Ioo 0 delta, ‖f h - f 0‖ = epsilon →
        HasDerivAt (fun s => ‖f s - f 0‖ ^ 2)
          (2 * inner ℝ (f h - f 0) (deriv f h)) h ∧
        0 < 2 * inner ℝ (f h - f 0) (deriv f h)) :
      (∃! h : ℝ, h ∈ Ioo 0 delta ∧ ‖g h - g 0‖ = epsilon) ∧
      (∀ h ∈ Ioo 0 delta, ‖g h - g 0‖ = epsilon →
        ∃ v : ℝ, 0 < v ∧ HasDerivAt (fun s => ‖g s - g 0‖ ^ 2) v h) := by
    constructor
    · obtain ⟨h, hh, huniq⟩ := hu
      refine ⟨h, ⟨hh.1, ?_⟩, fun k hk => ?_⟩
      · rw [← hfg hh.1, ← hfg0]
        exact hh.2
      · apply huniq
        refine ⟨hk.1, ?_⟩
        rw [hfg hk.1, hfg0]
        exact hk.2
    · intro h hh heq
      have heqf : ‖f h - f 0‖ = epsilon := by rw [hfg hh, hfg0]; exact heq
      obtain ⟨hderiv, hpos⟩ := htrans h hh heqf
      refine ⟨_, hpos, hderiv.congr_of_eventuallyEq ?_⟩
      filter_upwards [isOpen_Ioo.mem_nhds hh] with s hs
      rw [hfg hs, hfg0]
  refine ⟨dl, dr, min rl rr, hdl, hdr, lt_min hrl hrr,
    hdl_d0.trans_le hd0small, hdr_d0.trans_le hd0small, fun epsilon he herho => ?_⟩
  obtain ⟨hLu, hLt⟩ := hL epsilon he (herho.trans_le (min_le_left rl rr))
  obtain ⟨hRu, hRt⟩ := hR epsilon he (herho.trans_le (min_le_right rl rr))
  constructor
  · simpa only [sub_zero] using htransfer hleq (by simpa using hlzero) hLu hLt
  · simpa only [add_zero] using htransfer hreq (by simpa using hrzero) hRu hRt


/-- Compactness and injectivity prevent additional visits to a corner disk
outside any prescribed parameter neighborhood. This is independent of the
local radial argument and also applies at the period seam. -/
theorem curve_small_ball_parameters (c : RegularJordanCurve) (q : ParameterCircle)
    {V : Set ParameterCircle} (hV : IsOpen V) (hq : q ∈ V) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ t : ParameterCircle,
      c.parametrization t ∈ ball (c.parametrization q) rho → t ∈ V := by
  have hcompact : IsCompact (c.parametrization '' Vᶜ) :=
    hV.isClosed_compl.isCompact.image c.parametrization.continuous
  have hnot : c.parametrization q ∉ c.parametrization '' Vᶜ := by
    rintro ⟨t, ht, heq⟩
    exact ht (c.injective heq ▸ hq)
  obtain ⟨rho, hrho, hball⟩ := Metric.isOpen_iff.mp hcompact.isClosed.isOpen_compl
    _ hnot
  refine ⟨rho, hrho, fun t ht => ?_⟩
  by_contra htV
  exact hball ht (mem_image_of_mem _ htV)

/-- Every sufficiently small centered circle has exactly two intersections
with the entire Jordan curve. The witnesses lie on the two actual incident
portions, and each crossing has positive outward squared radial derivative.
Compactness and injectivity exclude all other visits to the disk. -/
theorem curve_small_circle_exactly_two (c : RegularJordanCurve) (t : ℝ) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < rho →
      ∃ l r : ℝ, l ∈ Ioo 0 (1 / 4) ∧ r ∈ Ioo 0 (1 / 4) ∧
        ((t - l : ℝ) : ParameterCircle) ≠ ((t + r : ℝ) : ParameterCircle) ∧
        (∀ q : ParameterCircle,
          c.parametrization q ∈ sphere (realLift c.parametrization t) epsilon ↔
            q = ((t - l : ℝ) : ParameterCircle) ∨
            q = ((t + r : ℝ) : ParameterCircle)) ∧
        (∃ v : ℝ, 0 < v ∧ HasDerivAt
          (fun s => ‖realLift c.parametrization (t - s) -
            realLift c.parametrization t‖ ^ 2) v l) ∧
        (∃ v : ℝ, 0 < v ∧ HasDerivAt
          (fun s => ‖realLift c.parametrization (t + s) -
            realLift c.parametrization t‖ ^ 2) v r) := by
  obtain ⟨dl, dr, rho, hdl, hdr, hrho, hdlquarter, hdrquarter, hcross⟩ :=
    regularJoin_small_circle_crossings c t
  let V : Set ParameterCircle :=
    ((↑) : ℝ → ParameterCircle) '' Ioo (t - dl) (t + dr)
  have hV : IsOpen V := QuotientAddGroup.isOpenMap_coe _ isOpen_Ioo
  have htV : (t : ParameterCircle) ∈ V := by
    exact ⟨t, ⟨by linarith, by linarith⟩, rfl⟩
  obtain ⟨sigma, hsigma, hnear⟩ := curve_small_ball_parameters c (t : ParameterCircle) hV htV
  refine ⟨min rho sigma, lt_min hrho hsigma, fun epsilon he herho => ?_⟩
  obtain ⟨⟨l, hl, huniqueL⟩, htransL⟩ :=
    (hcross epsilon he (herho.trans_le (min_le_left rho sigma))).1
  obtain ⟨⟨r, hr, huniqueR⟩, htransR⟩ :=
    (hcross epsilon he (herho.trans_le (min_le_left rho sigma))).2
  have hleft : c.parametrization ((t - l : ℝ) : ParameterCircle) ∈
      sphere (realLift c.parametrization t) epsilon := by
    simpa only [mem_sphere, dist_eq_norm, realLift] using hl.2
  have hright : c.parametrization ((t + r : ℝ) : ParameterCircle) ∈
      sphere (realLift c.parametrization t) epsilon := by
    simpa only [mem_sphere, dist_eq_norm, realLift] using hr.2
  refine ⟨l, r, ⟨hl.1.1, hl.1.2.trans hdlquarter⟩,
    ⟨hr.1.1, hr.1.2.trans hdrquarter⟩, ?_, ?_, htransL l hl.1 hl.2, htransR r hr.1 hr.2⟩
  · intro hparam
    apply realLift_ne_of_opposite_parameters c t hl.1.1 hr.1.1 (by linarith [hl.1.2, hr.1.2])
    exact congrArg c.parametrization hparam
  · intro q
    constructor
    · intro hq
      have hball : c.parametrization q ∈ ball (c.parametrization (t : ParameterCircle)) sigma := by
        rw [mem_ball]
        have hdist : dist (c.parametrization q) (c.parametrization (t : ParameterCircle)) = epsilon :=
          hq
        rw [hdist]
        exact herho.trans_le (min_le_right rho sigma)
      obtain ⟨u, hu, huq⟩ := hnear q hball
      have hnorm : ‖realLift c.parametrization u - realLift c.parametrization t‖ = epsilon := by
        simpa only [← huq, mem_sphere, dist_eq_norm, realLift] using hq
      rcases lt_trichotomy u t with hut | rfl | htu
      · left
        have hparam : t - u = l := huniqueL (t - u)
          ⟨⟨by linarith, by linarith [hu.1]⟩, by simpa using hnorm⟩
        have huval : u = t - l := by linarith
        simpa [huval] using huq.symm
      · simp at hnorm
        linarith
      · right
        have hparam : u - t = r := huniqueR (u - t)
          ⟨⟨by linarith, by linarith [hu.2]⟩, by simpa using hnorm⟩
        have huval : u = t + r := by linarith
        simpa [huval] using huq.symm
    · rintro (rfl | rfl)
      · exact hleft
      · exact hright
/-- The corresponding geometric intersection is an actual pair of distinct
points of the plane. -/
theorem curve_trace_small_circle_pair (c : RegularJordanCurve) (t : ℝ) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ epsilon : ℝ, 0 < epsilon → epsilon < rho →
      ∃ x y : Plane, x ≠ y ∧
        c.trace ∩ sphere (realLift c.parametrization t) epsilon = {x, y} := by
  obtain ⟨rho, hrho, hcross⟩ := curve_small_circle_exactly_two c t
  refine ⟨rho, hrho, fun epsilon he herho => ?_⟩
  obtain ⟨l, r, _, _, hne, hpoints, _, _⟩ := hcross epsilon he herho
  refine ⟨realLift c.parametrization (t - l), realLift c.parametrization (t + r),
    (fun h => hne (c.injective h)), ?_⟩
  ext z
  constructor
  · rintro ⟨⟨q, rfl⟩, hq⟩
    rcases (hpoints q).mp hq with rfl | rfl <;> simp [realLift]
  · intro hz
    rcases Set.mem_insert_iff.mp hz with hz | hz
    · rw [hz]
      exact ⟨⟨((t - l : ℝ) : ParameterCircle), rfl⟩,
        (hpoints ((t - l : ℝ) : ParameterCircle)).mpr (Or.inl rfl)⟩
    · have hz' : z = realLift c.parametrization (t + r) := Set.mem_singleton_iff.mp hz
      rw [hz']
      exact ⟨⟨((t + r : ℝ) : ParameterCircle), rfl⟩,
        (hpoints ((t + r : ℝ) : ParameterCircle)).mpr (Or.inr rfl)⟩



/-- A Jordan curve can hit any finite set of disk centers only finitely
many times in a single half-open period. The period seam is counted once. -/
theorem realLift_finite_center_times (c : RegularJordanCurve) {N : ℕ}
    (p : Fin N → Plane) :
    {t ∈ Ioc (0 : ℝ) 1 | realLift c.parametrization t ∈ range p}.Finite := by
  apply Set.Finite.of_injOn (f := realLift c.parametrization)
    (t := range p) (fun t ht => ht.2) ?_ (finite_range p)
  intro x hx y hy hxy
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ioc (p := (1 : ℝ)) (a := (0 : ℝ))
    (by simpa using hx.1) (by simpa using hy.1)).mp (c.injective hxy)

theorem retainedParameters_measurableSet (c : RegularJordanCurve) {N : ℕ}
    (p : Fin N → Plane) (epsilon : ℝ) :
    MeasurableSet (retainedParameters c p epsilon) := by
  have heq : retainedParameters c p epsilon =
      ⋂ j, {t | epsilon ≤ dist (realLift c.parametrization t) (p j)} := by
    ext t
    simp [retainedParameters]
  rw [heq]
  exact MeasurableSet.iInter fun j =>
    isClosed_le continuous_const ((realLift_continuous c).dist continuous_const)
      |>.measurableSet

/-- Deleting shrinking disks from an original arc preserves its integral.
This uses the actual Jordan parametrization, not hypothetical retained arcs
or an assumption that the erased arc integrals already tend to zero. -/
theorem retainedComponentIntegral_tendsto (R : PlanarRegion) {U : Set Plane}
    (hRU : R.carrier ⊆ U) {omega : OneForm} (homega : ContinuousOn omega U)
    (i : Fin R.boundaryCount) {N : ℕ} (p : Fin N → Plane)
    {epsilon : ℕ → ℝ} (hlim : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n => retainedComponentIntegral omega (R.curve i) p (epsilon n))
      atTop (𝓝 (componentIntegral omega (R.curve i))) := by
  let c := R.curve i
  let f := boundaryIntegrand omega c
  let μ := volume.restrict (Ioc (0 : ℝ) 1)
  have hint : Integrable f μ := (boundary_integrable R hRU homega i).1
  have hconv : ∀ᵐ t ∂μ, Tendsto
      (fun n => (retainedParameters c p (epsilon n)).indicator f t)
      atTop (𝓝 (f t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      ae_restrict_of_ae
        ((realLift_finite_center_times c p).countable.ae_notMem volume)] with t ht hnot
    have hdist : ∀ j, 0 < dist (realLift c.parametrization t) (p j) := by
      intro j
      apply dist_pos.mpr
      intro heq
      exact hnot ⟨ht, ⟨j, heq.symm⟩⟩
    have hevent : ∀ᶠ n in atTop, t ∈ retainedParameters c p (epsilon n) := by
      apply eventually_all.mpr
      intro j
      exact (hlim.eventually (gt_mem_nhds (hdist j))).mono fun n hn => hn.le
    apply tendsto_const_nhds.congr'
    filter_upwards [hevent] with n hn
    exact (Set.indicator_of_mem hn f).symm
  have h := tendsto_integral_of_dominated_convergence (fun t => ‖f t‖)
    (fun n => (hint.indicator (retainedParameters_measurableSet c p (epsilon n))).aestronglyMeasurable)
    hint.norm (fun n => Filter.Eventually.of_forall fun t => norm_indicator_le_norm_self _ t)
    hconv
  simpa only [retainedComponentIntegral, componentIntegral,
    intervalIntegral.integral_of_le zero_le_one] using h

/-- All original components, with their actual induced signs, survive the
disk-removal limit. No condition on convexity or the angles is used. -/
theorem retainedBoundaryIntegral_tendsto (R : PlanarRegion) {U : Set Plane}
    (hRU : R.carrier ⊆ U) {omega : OneForm} (homega : ContinuousOn omega U)
    (s : Fin R.boundaryCount → ℝ) {N : ℕ} (p : Fin N → Plane)
    {epsilon : ℕ → ℝ} (hlim : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n => retainedBoundaryIntegral R omega s p (epsilon n))
      atTop (𝓝 (boundaryIntegral R omega s)) := by
  exact tendsto_finsetSum Finset.univ fun i _ =>
    tendsto_const_nhds.mul (retainedComponentIntegral_tendsto R hRU homega i p hlim)

/-- Compactness gives a uniform coefficient bound on all sufficiently small
corner disks, entirely within the original open coefficient neighborhood. -/
theorem coefficients_bounded_near_carrier (R : PlanarRegion) {U : Set Plane}
    (hU : IsOpen U) (hRU : R.carrier ⊆ U) {omega : OneForm}
    (homega : ContinuousOn omega U) :
    ∃ delta M : ℝ, 0 < delta ∧ 0 ≤ M ∧
      ∀ p ∈ R.carrier, ∀ x ∈ closedBall p delta, x ∈ U ∧ ‖omega x‖ ≤ M := by
  obtain ⟨r, hr, hrU⟩ := R.compact_closure.exists_cthickening_subset_open hU hRU
  obtain ⟨d, hd, hdcompact⟩ := R.compact_closure.exists_isCompact_cthickening
  let delta := min r d
  have hdelta : 0 < delta := lt_min hr hd
  have hcompact : IsCompact (cthickening delta R.carrier) :=
    hdcompact.of_isClosed_subset isClosed_cthickening
      (cthickening_mono (min_le_right r d) R.carrier)
  have hsub : cthickening delta R.carrier ⊆ U :=
    (cthickening_mono (min_le_left r d) R.carrier).trans hrU
  obtain ⟨M, hM⟩ := hcompact.exists_bound_of_continuousOn (homega.mono hsub)
  refine ⟨delta, max M 0, hdelta, le_max_right M 0, fun p hp x hx => ?_⟩
  have hmem := closedBall_subset_cthickening hp delta hx
  exact ⟨hsub hmem, (hM x hmem).trans (le_max_left M 0)⟩

/-- The coefficient bound on the added circle arcs follows from original
smoothness near the carrier; it is not an extra uniform-bound premise. -/
theorem circle_integrals_tendsto_zero_near_carrier (R : PlanarRegion)
    {U : Set Plane} (hU : IsOpen U) (hRU : R.carrier ⊆ U)
    {omega : OneForm} (homega : ContinuousOn omega U)
    (p : Plane) (hp : p ∈ R.carrier) {epsilon : ℕ → ℝ}
    (he : ∀ n, 0 ≤ epsilon n) (hlim : Tendsto epsilon atTop (𝓝 0))
    (a b : ℕ → ℝ) (hab : ∀ n, |b n - a n| ≤ 2 * Real.pi) :
    Tendsto (fun n => ∫ t in a n..b n, omega (circlePoint p (epsilon n) t)
      (deriv (circlePoint p (epsilon n)) t)) atTop (𝓝 0) := by
  obtain ⟨delta, M, hdelta, hM, hbound⟩ :=
    coefficients_bounded_near_carrier R hU hRU homega
  apply squeeze_zero_norm' ?_
    (show Tendsto (fun n => 2 * Real.pi * M * epsilon n) atTop (𝓝 0) by
      simpa using tendsto_const_nhds.mul hlim)
  filter_upwards [hlim.eventually (gt_mem_nhds hdelta)] with n hn
  apply circle_integral_bound p (he n) hM (hab n) omega
  intro t _
  apply (hbound p hp (circlePoint p (epsilon n) t) ?_).2
  have hdist : dist (circlePoint p (epsilon n) t) p = epsilon n := by
    have hnorm : ‖(!₂[Real.cos t, Real.sin t] : Plane)‖ = 1 := by
      have h := EuclideanSpace.real_norm_sq_eq (!₂[Real.cos t, Real.sin t] : Plane)
      simp [Fin.sum_univ_two] at h
      rcases h with h | h
      · exact h
      · have := norm_nonneg (!₂[Real.cos t, Real.sin t] : Plane)
        linarith
    simp [circlePoint, dist_eq_norm, norm_smul, hnorm, abs_of_nonneg (he n)]
  simpa only [mem_closedBall, hdist] using hn.le

/-- Finite disk removal preserves the bulk integral in the limit. The
coefficient bound is derived from smoothness on the original neighborhood. -/
theorem bulkIntegral_truncations_tendsto (R : PlanarRegion) {U : Set Plane}
    (hU : IsOpen U) (hRU : R.carrier ⊆ U) {omega : OneForm}
    (homega : ContDiffOn ℝ ∞ omega U) {N : ℕ} (p : Fin N → Plane)
    {epsilon : ℕ → ℝ} (he : ∀ n, 0 ≤ epsilon n)
    (hlim : Tendsto epsilon atTop (𝓝 0)) (K : ℕ → Set Plane)
    (hK : ∀ n, MeasurableSet (K n)) (hsub : ∀ n, K n ⊆ R.carrier)
    (hremoved : ∀ n, R.carrier \ K n ⊆ ⋃ i, closedBall (p i) (epsilon n)) :
    Tendsto (fun n => ∫ x in K n, exteriorCoefficient omega x)
      atTop (𝓝 (bulkIntegral R omega)) := by
  obtain ⟨M, hM⟩ := R.compact_closure.exists_bound_of_continuousOn
    ((exteriorCoefficient_continuousOn hU homega).mono hRU)
  let B := max M 0
  have hB : 0 ≤ B := le_max_right M 0
  have hint := bulk_integrable R hU hRU homega
  have hsmall := removed_integrals_tendsto_zero p he hlim hB
    (fun n => R.carrier \ K n) hremoved (exteriorCoefficient omega)
    (fun n x hx => (hM x hx.1).trans (le_max_left M 0))
  have hlim' := (tendsto_const_nhds (x := bulkIntegral R omega) (f := atTop)).sub hsmall
  simp only [sub_zero] at hlim'
  convert hlim' using 1
  ext n
  rw [setIntegral_sdiff (hK n) hint (hsub n)]
  exact (sub_sub_cancel _ _).symm

/-- In particular, the concrete disk-truncated carrier has the original
bulk integral as its limit. Its measurability and removed-area containment
are proved here, rather than supplied as a truncation certificate. -/
theorem bulkIntegral_truncatedCarrier_tendsto (R : PlanarRegion) {U : Set Plane}
    (hU : IsOpen U) (hRU : R.carrier ⊆ U) {omega : OneForm}
    (homega : ContDiffOn ℝ ∞ omega U) {N : ℕ} (p : Fin N → Plane)
    {epsilon : ℕ → ℝ} (he : ∀ n, 0 ≤ epsilon n)
    (hlim : Tendsto epsilon atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in truncatedCarrier R p (epsilon n), exteriorCoefficient omega x)
      atTop (𝓝 (bulkIntegral R omega)) := by
  apply bulkIntegral_truncations_tendsto R hU hRU homega p he hlim
  · intro n
    exact isClosed_closure.measurableSet.diff
      (isOpen_iUnion fun j => isOpen_ball (x := p j) (ε := epsilon n)).measurableSet
  · intro n
    exact sdiff_subset
  · intro n x hx
    have hmem : x ∈ ⋃ j, ball (p j) (epsilon n) := by
      by_contra hn
      exact hx.2 ⟨hx.1, hn⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    exact mem_iUnion.mpr ⟨j, ball_subset_closedBall hj⟩

/-- Analytic completion of the disk-removal argument. Once the geometric
construction and ordinary transverse-corner Stokes establish the displayed
truncated identities, all original integrals and the final limit identity
follow without any estimates or convergence assumptions on the form.

This helper does not construct the geometric truncated identities. The
unconditional `stokes` theorem below uses the direct graph proof instead. -/
theorem stokes_of_truncated_identities (R : PlanarRegion) {U : Set Plane}
    (hU : IsOpen U) (hRU : R.carrier ⊆ U) {omega : OneForm}
    (homega : ContDiffOn ℝ ∞ omega U) (s : Fin R.boundaryCount → ℝ)
    {N : ℕ} (p : Fin N → Plane) (hp : ∀ j, p j ∈ R.carrier)
    {epsilon : ℕ → ℝ} (he : ∀ n, 0 ≤ epsilon n)
    (hlim : Tendsto epsilon atTop (𝓝 0))
    (a b : Fin N → ℕ → ℝ) (hab : ∀ j n, |b j n - a j n| ≤ 2 * Real.pi)
    (htruncated : ∀ᶠ n in atTop,
      (∫ x in truncatedCarrier R p (epsilon n), exteriorCoefficient omega x) =
        retainedBoundaryIntegral R omega s p (epsilon n) +
          ∑ j, ∫ t in a j n..b j n, omega (circlePoint (p j) (epsilon n) t)
            (deriv (circlePoint (p j) (epsilon n)) t)) :
    IntegrableOn (exteriorCoefficient omega) R.carrier ∧
      (∀ i, IntervalIntegrable (boundaryIntegrand omega (R.curve i)) volume 0 1) ∧
      bulkIntegral R omega = boundaryIntegral R omega s := by
  refine ⟨bulk_integrable R hU hRU homega,
    boundary_integrable R hRU homega.continuousOn, ?_⟩
  have hbulk := bulkIntegral_truncatedCarrier_tendsto R hU hRU homega p he hlim
  have hretained := retainedBoundaryIntegral_tendsto R hRU homega.continuousOn s p hlim
  have hcircles : Tendsto
      (fun n => ∑ j, ∫ t in a j n..b j n, omega (circlePoint (p j) (epsilon n) t)
        (deriv (circlePoint (p j) (epsilon n)) t)) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun j _ =>
      circle_integrals_tendsto_zero_near_carrier R hU hRU homega.continuousOn
        (p j) (hp j) he hlim (a j) (b j) (hab j))
  have hrhs := hretained.add hcircles
  simp only [add_zero] at hrhs
  exact tendsto_nhds_unique hbulk (hrhs.congr' (htruncated.mono fun _ hn => hn.symm))

/-- Transport a planar Stokes proof to the actual intrinsic positive-chart
formulation. The unconditional specialization is given at the end of this file. -/
theorem surfaceChartStokes_of_stokes
    (h : P202Specs.ChartRegionStokes.Expected.stokes) :
    P202Specs.ChartRegionStokes.Expected.surfaceChartStokes.{u} := by
  intro M _ S C o c hc _ R U omega hU hRU _ homega s hs
  exact h R U (chartOneForm C c hc omega) hU hRU homega s hs

/-- A smooth form on a neighborhood of the compact carrier has a globally
smooth compactly supported extension agreeing with it locally at every
point of the carrier. -/
theorem exists_compact_oneForm_extension (R : PlanarRegion) {U : Set Plane}
    (hU : IsOpen U) (hRU : R.carrier ⊆ U) {omega : OneForm}
    (homega : ContDiffOn ℝ ∞ omega U) :
    ∃ eta : OneForm, ContDiff ℝ ∞ eta ∧ HasCompactSupport eta ∧
      ∀ x ∈ R.carrier, eta =ᶠ[𝓝 x] omega := by
  obtain ⟨K, hK, hKclosed, hRK, hKU⟩ :=
    exists_compact_closed_between R.compact_closure hU hRU
  obtain ⟨f, hf, hfzero, _⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior (I := 𝓘(ℝ, Plane))
      (n := (⊤ : ℕ∞)) isClosed_closure hRK
  have hfcompact : HasCompactSupport (f : Plane → ℝ) := by
    apply hK.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hKclosed
    intro x hx
    by_contra hn
    exact hx (hfzero x hn)
  have hfU : tsupport (f : Plane → ℝ) ⊆ U := by
    apply subset_trans _ hKU
    apply closure_minimal _ hKclosed
    intro x hx
    by_contra hn
    exact hx (hfzero x hn)
  refine ⟨fun x => f x • omega x, ?_, hfcompact.smul_right, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ tsupport (f : Plane → ℝ)
    · exact ((contMDiff_iff_contDiff.mp f.contMDiff).contDiffAt).smul
        (homega.contDiffAt (hU.mem_nhds (hfU hx)))
    · apply (contDiffAt_const (c := (0 : Plane →L[ℝ] ℝ))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      have hz : f y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [hz]
  · intro x hx
    filter_upwards [hf.filter_mono (nhds_le_nhdsSet hx)] with y hy
    simp [hy]

/-- Replacing a form by one agreeing locally on the carrier preserves the
actual bulk and every original oriented boundary integral. -/
theorem integrals_eq_of_eventuallyEq (R : PlanarRegion) {omega eta : OneForm}
    (heq : ∀ x ∈ R.carrier, eta =ᶠ[𝓝 x] omega)
    (s : Fin R.boundaryCount → ℝ) :
    bulkIntegral R eta = bulkIntegral R omega ∧
      boundaryIntegral R eta s = boundaryIntegral R omega s := by
  constructor
  · apply setIntegral_congr_fun isClosed_closure.measurableSet
    intro x hx
    have hd := (heq x hx).fderiv_eq (𝕜 := ℝ)
    simp only [exteriorCoefficient, hd]
  · unfold boundaryIntegral
    congr 1
    funext i
    congr 1
    unfold componentIntegral
    apply intervalIntegral.integral_congr
    intro t _
    have hp := (heq _ (realLift_mem_carrier R i t)).eq_of_nhds
    simp only [boundaryIntegrand, hp]

/-- It suffices to prove Stokes for globally smooth compactly supported
coordinate forms. No support hypothesis is added to the original theorem. -/
theorem stokes_of_compactSupport
    (hcompact : ∀ (R : PlanarRegion) (omega : OneForm),
      ContDiff ℝ ∞ omega → HasCompactSupport omega →
      ∀ s : Fin R.boundaryCount → ℝ, IsInducedBoundaryOrientation R s →
        bulkIntegral R omega = boundaryIntegral R omega s) :
    P202Specs.ChartRegionStokes.Expected.stokes := by
  intro R U omega hU hRU homega s hs
  obtain ⟨eta, heta, hsupport, heq⟩ := exists_compact_oneForm_extension R hU hRU homega
  obtain ⟨hbulk, hboundary⟩ := integrals_eq_of_eventuallyEq R heq s
  exact ⟨bulk_integrable R hU hRU homega,
    boundary_integrable R hRU homega.continuousOn,
    hbulk.symm.trans ((hcompact R eta heta hsupport s hs).trans hboundary)⟩



open P202Specs.PlanarRegionTopology P202Specs.ChartRegionStokes

 theorem integral_fderiv_eq_zero_of_compactSupport {f : Plane → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (v : Plane) :
    (∫ x, fderiv ℝ f x v) = 0 := by
  have hi : Integrable (fun x => fderiv ℝ f x v) :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v)
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : Plane => (1 : ℝ)) (g := f) (v := v)
    (by simpa using (integrable_zero Plane ℝ volume))
    (by simpa using hi)
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hc)
    (by intros; exact differentiableAt_const _)
    (by intros; exact hf.differentiable one_ne_zero _)
  simpa using h

 theorem exteriorCoefficient_sum {ι : Type*} (a : Finset ι)
    (omega : ι → OneForm) (x : Plane)
    (h : ∀ i ∈ a, DifferentiableAt ℝ (omega i) x) :
    exteriorCoefficient (fun y => ∑ i ∈ a, omega i y) x =
      ∑ i ∈ a, exteriorCoefficient (omega i) x := by
  simp only [exteriorCoefficient, fderiv_fun_sum h, sum_apply,
    Finset.sum_sub_distrib]

 theorem boundaryIntegrand_sum {ι : Type*} (a : Finset ι)
    (omega : ι → OneForm) (c : RegularJordanCurve) (t : ℝ) :
    boundaryIntegrand (fun y => ∑ i ∈ a, omega i y) c t =
      ∑ i ∈ a, boundaryIntegrand (omega i) c t := by
  simp only [boundaryIntegrand]
  split_ifs <;> simp

 theorem bulkIntegral_sum {ι : Type*} (a : Finset ι) (R : PlanarRegion)
    (omega : ι → OneForm) (ho : ∀ i ∈ a, ContDiff ℝ ∞ (omega i)) :
    bulkIntegral R (fun y => ∑ i ∈ a, omega i y) = ∑ i ∈ a, bulkIntegral R (omega i) := by
  unfold bulkIntegral
  rw [show (fun x => exteriorCoefficient (fun y => ∑ i ∈ a, omega i y) x) =
      (fun x => ∑ i ∈ a, exteriorCoefficient (omega i) x) by
    funext x
    exact exteriorCoefficient_sum a omega x (fun i hi => (ho i hi).differentiable (by simp) x)]
  rw [integral_finsetSum]
  intro i hi
  exact bulk_integrable R isOpen_univ (subset_univ _) (ho i hi).contDiffOn

 theorem boundaryIntegral_sum {ι : Type*} (a : Finset ι) (R : PlanarRegion)
    (omega : ι → OneForm) (ho : ∀ i ∈ a, Continuous (omega i))
    (s : Fin R.boundaryCount → ℝ) :
    boundaryIntegral R (fun y => ∑ i ∈ a, omega i y) s =
      ∑ i ∈ a, boundaryIntegral R (omega i) s := by
  unfold boundaryIntegral componentIntegral
  simp_rw [boundaryIntegrand_sum]
  simp_rw [intervalIntegral.integral_finsetSum (s := a) (fun i hi =>
    boundary_integrable R (subset_univ _) (ho i hi).continuousOn _)]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

 theorem exteriorCoefficient_congr_nhds {omega eta : OneForm} {x : Plane}
    (h : omega =ᶠ[𝓝 x] eta) : exteriorCoefficient omega x = exteriorCoefficient eta x := by
  simp only [exteriorCoefficient, h.fderiv_eq]

 theorem stokes_of_finite_localization {ι : Type*} (a : Finset ι)
    (R : PlanarRegion) {U : Set Plane} (hU : IsOpen U) (hRU : R.carrier ⊆ U)
    (omega : OneForm) (homega : ContDiffOn ℝ ∞ omega U)
    (s : Fin R.boundaryCount → ℝ) (eta : ι → OneForm)
    (he : ∀ i ∈ a, ContDiff ℝ ∞ (eta i))
    (hsum : ∀ x ∈ R.carrier, (fun y => ∑ i ∈ a, eta i y) =ᶠ[𝓝 x] omega)
    (hloc : ∀ i ∈ a, bulkIntegral R (eta i) = boundaryIntegral R (eta i) s) :
    IntegrableOn (exteriorCoefficient omega) R.carrier ∧
      (∀ i, IntervalIntegrable (boundaryIntegrand omega (R.curve i)) volume 0 1) ∧
      bulkIntegral R omega = boundaryIntegral R omega s := by
  refine ⟨bulk_integrable R hU hRU homega,
    boundary_integrable R hRU homega.continuousOn, ?_⟩
  calc
    bulkIntegral R omega = bulkIntegral R (fun y => ∑ i ∈ a, eta i y) := by
      apply setIntegral_congr_fun R.compact_closure.isClosed.measurableSet
      intro x hx
      exact (exteriorCoefficient_congr_nhds (hsum x hx)).symm
    _ = ∑ i ∈ a, bulkIntegral R (eta i) := bulkIntegral_sum a R eta he
    _ = ∑ i ∈ a, boundaryIntegral R (eta i) s := Finset.sum_congr rfl hloc
    _ = boundaryIntegral R (fun y => ∑ i ∈ a, eta i y) s :=
      (boundaryIntegral_sum a R eta (fun i hi => (he i hi).continuous) s).symm
    _ = boundaryIntegral R omega s := by
      unfold boundaryIntegral componentIntegral
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [boundaryIntegrand]
      split_ifs
      · rfl
      · rw [(hsum _ (realLift_mem_carrier R i t)).eq_of_nhds]

 theorem scalarCoefficient_fderiv {omega : OneForm} {x : Plane}
    (h : DifferentiableAt ℝ omega x) (u v : Plane) :
    fderiv ℝ (fun y => omega y v) x u = fderiv ℝ omega x u v := by
  rw [fderiv_clm_apply h (differentiableAt_const v)]
  simp

 theorem exteriorCoefficient_integrable {omega : OneForm}
    (ho : ContDiff ℝ 1 omega) (hc : HasCompactSupport omega) :
    Integrable (exteriorCoefficient omega) := by
  have hf : Continuous (fun x => fderiv ℝ omega x (coordinateFrame 0) (coordinateFrame 1)) :=
    ((ho.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply continuous_const
  have hg : Continuous (fun x => fderiv ℝ omega x (coordinateFrame 1) (coordinateFrame 0)) :=
    ((ho.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply continuous_const
  apply (hf.sub hg).integrable_of_hasCompactSupport
  apply hc.mono'
  intro x hx
  by_contra hn
  have hz := fderiv_of_notMem_tsupport ℝ hn
  exact hx (by simp [exteriorCoefficient, hz])

 theorem integral_exteriorCoefficient_eq_zero {omega : OneForm}
    (ho : ContDiff ℝ 1 omega) (hc : HasCompactSupport omega) :
    (∫ x, exteriorCoefficient omega x) = 0 := by
  let P : Plane → ℝ := fun x => omega x (coordinateFrame 0)
  let Q : Plane → ℝ := fun x => omega x (coordinateFrame 1)
  have hP : ContDiff ℝ 1 P := ho.clm_apply contDiff_const
  have hQ : ContDiff ℝ 1 Q := ho.clm_apply contDiff_const
  have cP : HasCompactSupport P := hc.comp_left (g := fun α : Plane →L[ℝ] ℝ => α (coordinateFrame 0)) (by simp)
  have cQ : HasCompactSupport Q := hc.comp_left (g := fun α : Plane →L[ℝ] ℝ => α (coordinateFrame 1)) (by simp)
  have hPe : Integrable (fun x => fderiv ℝ P x (coordinateFrame 1)) :=
    ((hP.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (cP.fderiv_apply ℝ _)
  have hQe : Integrable (fun x => fderiv ℝ Q x (coordinateFrame 0)) :=
    ((hQ.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (cQ.fderiv_apply ℝ _)
  have hex : exteriorCoefficient omega = fun x =>
      fderiv ℝ Q x (coordinateFrame 0) - fderiv ℝ P x (coordinateFrame 1) := by
    funext x
    simp only [exteriorCoefficient, P, Q,
      scalarCoefficient_fderiv (ho.differentiable one_ne_zero x)]
  rw [hex, integral_sub hQe hPe,
    integral_fderiv_eq_zero_of_compactSupport hQ cQ,
    integral_fderiv_eq_zero_of_compactSupport hP cP, sub_self]

 theorem interior_supported_stokes (R : PlanarRegion) {omega : OneForm}
    (ho : ContDiff ℝ 1 omega) (hc : HasCompactSupport omega)
    (hsub : tsupport omega ⊆ R.domain) (s : Fin R.boundaryCount → ℝ) :
    bulkIntegral R omega = boundaryIntegral R omega s := by
  have hbulk : bulkIntegral R omega = 0 := by
    unfold bulkIntegral
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero,
      integral_exteriorCoefficient_eq_zero ho hc]
    intro x hx
    have hn : x ∉ tsupport omega := fun ht =>
      hx (subset_closure (hsub ht))
    simp [exteriorCoefficient, fderiv_of_notMem_tsupport ℝ hn]
  have hboundary : boundaryIntegral R omega s = 0 := by
    unfold boundaryIntegral componentIntegral
    apply Finset.sum_eq_zero
    intro i _
    suffices hzero : (fun t => boundaryIntegrand omega (R.curve i) t) = 0 by
      simp [hzero]
    funext t
    have hb : realLift (R.curve i).parametrization t ∈ frontier R.domain := by
      rw [R.boundary_eq]
      exact mem_iUnion.mpr ⟨i, mem_range_self _⟩
    have hn : realLift (R.curve i).parametrization t ∉ tsupport omega := by
      intro ht
      exact (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr R.open_domain)) hb (hsub ht)
    have hz := image_eq_zero_of_notMem_tsupport hn
    simp [boundaryIntegrand, hz]
  exact hbulk.trans hboundary.symm

set_option maxHeartbeats 1000000 in
 theorem finite_oneForm_decomposition {ι : Type*} (U : ι → Set Plane)
    (hU : ∀ i, IsOpen (U i)) (hcover : (univ : Set Plane) ⊆ ⋃ i, U i)
    {omega : OneForm} (ho : ContDiff ℝ ∞ omega) (hc : HasCompactSupport omega) :
    ∃ (a : Finset ι) (eta : ι → OneForm),
      (∀ i, ContDiff ℝ ∞ (eta i)) ∧ (∀ i, HasCompactSupport (eta i)) ∧
      (∀ i, tsupport (eta i) ⊆ U i) ∧
      omega = fun x => ∑ i ∈ a, eta i x := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ, Plane)) isClosed_univ U hU hcover
  let a : Finset ι := (ρ.locallyFinite.finite_nonempty_inter_compact hc).toFinset
  let eta : ι → OneForm := fun i x => ρ i x • omega x
  refine ⟨a, eta, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (ρ i).contMDiff.contDiff.smul ho
  · intro i
    change HasCompactSupport ((fun x => ρ i x) • omega)
    exact hc.smul_left
  · intro i
    change tsupport ((fun x => ρ i x) • omega) ⊆ U i
    exact (tsupport_smul_subset_left (fun x => ρ i x) omega).trans (hρ i)
  · funext x
    by_cases hx : omega x = 0
    · simp [eta, hx]
    · have hsupp : Function.support (fun i => ρ i x) ⊆ a := by
        intro i hi
        change i ∈ (ρ.locallyFinite.finite_nonempty_inter_compact hc).toFinset
        rw [Set.Finite.mem_toFinset]
        exact ⟨x, hi, subset_tsupport _ hx⟩
      calc
        omega x = (∑ᶠ i, ρ i x) • omega x := by rw [ρ.sum_eq_one (mem_univ x), one_smul]
        _ = (∑ i ∈ a, ρ i x) • omega x := by rw [finsum_eq_sum_of_support_subset _ hsupp]
        _ = ∑ i ∈ a, eta i x := by simp only [Finset.sum_smul, eta]

 theorem compactSupported_stokes_of_local (R : PlanarRegion)
    (s : Fin R.boundaryCount → ℝ)
    (hlocal : ∀ x : Plane, ∃ O : Set Plane, IsOpen O ∧ x ∈ O ∧
      ∀ eta : OneForm, ContDiff ℝ ∞ eta → HasCompactSupport eta →
        tsupport eta ⊆ O → bulkIntegral R eta = boundaryIntegral R eta s)
    {omega : OneForm} (ho : ContDiff ℝ ∞ omega) (hc : HasCompactSupport omega) :
    bulkIntegral R omega = boundaryIntegral R omega s := by
  classical
  choose O hO hxO hlocalO using hlocal
  obtain ⟨a, eta, he, hceta, hsub, hsum⟩ := finite_oneForm_decomposition O hO
    (fun x _ => mem_iUnion.mpr ⟨x, hxO x⟩) ho hc
  exact (stokes_of_finite_localization a R isOpen_univ (subset_univ _) omega ho.contDiffOn s eta
    (fun i _ => he i) (fun x _ => by rw [← hsum])
    (fun i _ => hlocalO i (eta i) (he i) (hceta i) (hsub i))).2.2

 theorem exterior_supported_stokes (R : PlanarRegion) {omega : OneForm}
    (hsub : tsupport omega ⊆ R.carrierᶜ) (s : Fin R.boundaryCount → ℝ) :
    bulkIntegral R omega = boundaryIntegral R omega s := by
  have hn : ∀ x ∈ R.carrier, x ∉ tsupport omega := fun x hx ht => hsub ht hx
  have hbulk : bulkIntegral R omega = 0 := by
    unfold bulkIntegral
    calc
      _ = ∫ x in R.carrier, (0 : ℝ) := by
        apply setIntegral_congr_fun R.compact_closure.isClosed.measurableSet
        intro x hx
        simp [exteriorCoefficient, fderiv_of_notMem_tsupport ℝ (hn x hx)]
      _ = 0 := by simp
  have hboundary : boundaryIntegral R omega s = 0 := by
    unfold boundaryIntegral componentIntegral
    apply Finset.sum_eq_zero
    intro i _
    suffices hzero : (fun t => boundaryIntegrand omega (R.curve i) t) = 0 by simp [hzero]
    funext t
    have hz := image_eq_zero_of_notMem_tsupport (hn _ (realLift_mem_carrier R i t))
    simp [boundaryIntegrand, hz]
  exact hbulk.trans hboundary.symm




open P202Specs.PlanarRegionTopology P202Specs.BoundaryGraphDirections
open P202Specs.ContinuousGraphFlux

theorem other_component_zero
    {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O)
    {f : Plane → ℝ} (hfO : Function.support f ⊆ O)
    {j : Fin R.boundaryCount} (hji : j ≠ i) (e : Plane) :
    (∫ u in (0 : ℝ)..1, f (realLift (R.curve j).parametrization u) *
      inner ℝ e (deriv (realLift (R.curve j).parametrization) u)) = 0 := by
  have hz (u : ℝ) : f (realLift (R.curve j).parametrization u) = 0 := by
    by_contra h
    exact hji (G.local_visits j (u : ParameterCircle) (hfO h)).1
  simp_rw [hz, zero_mul]
  simp

theorem local_graph_trace
    {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) (hs : s i = 1 ∨ s i = -1)
    {f : Plane → ℝ} (hf : Continuous f) (hfO : Function.support f ⊆ O) :
    (∫ x : ℝ, f (frame 0 G.arc.axis (x, G.height x))) =
      s i * (∫ u in (0 : ℝ)..1, f (realLift (R.curve i).parametrization u) *
        inner ℝ G.arc.axis (deriv (realLift (R.curve i).parametrization) u)) := by
  let a := t - G.arc.radius
  let b := t + G.arc.radius
  let c := R.curve i
  let γ := realLift c.parametrization
  let π := arcProjection c G.arc.axis
  let K : ℝ → ℝ := fun x => f (frame 0 G.arc.axis (x, G.height x))
  let D : ℝ → ℝ := fun u => f (γ u) * inner ℝ G.arc.axis (deriv γ u)
  have hab : a < b := by dsimp [a, b]; linarith [G.arc.radius_pos]
  have hshort : b - a < 1 := by dsimp [a, b]; linarith [G.arc.short]
  have hframe (x y : ℝ) : G.frame.map !₂[x,y] = frame 0 G.arc.axis (x,y) := by
    simp [G.frame.formula, frame]
  have hπ : projection c 0 G.arc.axis = π := by
    funext u
    simp [projection, arcProjection, π]
  have hsub : (∫ u in a..b, D u) = ∫ x in π a..π b, K x := by
    have hh := P202.ContinuousGraphFlux.parameter_substitution c 0 G.arc.axis G.height
      G.continuous_height f hf a b (by rw [abs_of_pos (sub_pos.mpr hab)]; exact hshort)
      (fun u hu => by
        rw [uIcc_of_le hab.le] at hu
        simpa only [hπ, ← hframe] using G.arc_identity u hu)
    simpa only [hπ, D, K, γ] using hh
  have hDperiod : Function.Periodic D 1 := by
    intro u
    dsimp [D, γ, c]
    rw [G.periodic u, G.periodic_derivative u]
  have hzero_tail : (∫ u in b..a+1, D u) = 0 := by
    have hba : b ≤ a + 1 := by linarith
    apply (intervalIntegral.integral_congr_Ioo_of_le hba ?_).trans
      (by simp : (∫ u in b..a+1, (0 : ℝ)) = 0)
    intro u hu
    have hz : f (γ u) = 0 := by
      by_contra h
      obtain ⟨v, hv, -⟩ := (G.local_visits i (u : ParameterCircle) (hfO h)).2
      have hcoe : v = u :=
        (AddCircle.coe_eq_coe_iff_of_mem_Ico
          (show v ∈ Ico a (a+1) from ⟨hv.1.1.le, by linarith [hv.1.2]⟩)
          (show u ∈ Ico a (a+1) from ⟨by linarith [hu.1], hu.2⟩)).mp hv.2
      have hvb : v < b := hv.1.2
      linarith [hu.1]
    simp [D, hz]
  have hfull : (∫ u in (0 : ℝ)..1, D u) = ∫ u in a..b, D u := by
    calc
      _ = ∫ u in a..a+1, D u := by
        simpa using hDperiod.intervalIntegral_add_eq 0 a
      _ = (∫ u in a..b, D u) + ∫ u in b..a+1, D u :=
        (intervalIntegral.integral_add_adjacent_intervals
          (P202.ContinuousGraphFlux.curve_integrable c G.arc.axis hf a b)
          (P202.ContinuousGraphFlux.curve_integrable c G.arc.axis hf b (a+1))).symm
      _ = _ := by rw [hzero_tail, add_zero]
  have hKloc (x : ℝ) (hx : K x ≠ 0) : ∃ u ∈ Icc a b, π u = x := by
    have hO : frame 0 G.arc.axis (x, G.height x) ∈ O := hfO hx
    have hgraph : frame 0 G.arc.axis (x, G.height x) ∈ R.boundary ∩ O := by
      rw [G.boundary_eq]
      exact ⟨⟨!₂[x,G.height x], by simp, hframe _ _⟩, hO⟩
    rw [G.subarc_eq] at hgraph
    obtain ⟨u, hu, heq⟩ := hgraph.1
    refine ⟨u, hu, ?_⟩
    have hsame := (G.arc_identity u hu).symm.trans heq
    rw [← hframe] at hsame
    have hcoords := G.frame.map.injective hsame
    simpa only [Matrix.cons_val_zero] using congrArg (fun z : Plane => z 0) hcoords
  rcases hs with hs | hs
  · have hmono := G.increasing hs
    have hπab : π a ≤ π b := hmono.monotoneOn ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
    have hKzero : ∀ x, x ∉ Icc (π a) (π b) → K x = 0 := by
      intro x hx
      by_contra h
      obtain ⟨u, hu, rfl⟩ := hKloc x h
      exact hx ⟨hmono.monotoneOn ⟨le_rfl, hab.le⟩ hu hu.1,
        hmono.monotoneOn hu ⟨hab.le, le_rfl⟩ hu.2⟩
    have hKI : (∫ x : ℝ, K x) = ∫ x in π a..π b, K x := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hKzero,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hπab]
    change (∫ x : ℝ, K x) = s i * (∫ u in (0 : ℝ)..1, D u)
    rw [hs, one_mul, hfull, hsub, hKI]
  · have hanti := G.decreasing hs
    have hπba : π b ≤ π a := hanti.antitoneOn ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩ hab.le
    have hKzero : ∀ x, x ∉ Icc (π b) (π a) → K x = 0 := by
      intro x hx
      by_contra h
      obtain ⟨u, hu, rfl⟩ := hKloc x h
      exact hx ⟨hanti.antitoneOn hu ⟨hab.le, le_rfl⟩ hu.2,
        hanti.antitoneOn ⟨le_rfl, hab.le⟩ hu hu.1⟩
    have hKI : (∫ x : ℝ, K x) = ∫ x in π b..π a, K x := by
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hKzero,
        integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hπba]
    change (∫ x : ℝ, K x) = s i * (∫ u in (0 : ℝ)..1, D u)
    rw [hs, neg_one_mul, hfull, hsub, ← intervalIntegral.integral_symm, hKI]

open P202Specs.ChartRegionStokes

theorem local_graph_boundaryIntegral
    {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) (hs : s i = 1 ∨ s i = -1)
    {f : Plane → ℝ} (hf : Continuous f) (hfO : Function.support f ⊆ O) :
    (∫ x : ℝ, f (frame 0 G.arc.axis (x, G.height x))) =
      boundaryIntegral R (fun z => f z • innerSL ℝ G.arc.axis) s := by
  rw [local_graph_trace G hs hf hfO]
  symm
  rw [boundaryIntegral]
  rw [Finset.sum_eq_single i]
  · congr 1
    rw [P202.ChartRegionStokes.componentIntegral_eq_unmasked]
    simp
  · intro j _ hji
    rw [P202.ChartRegionStokes.componentIntegral_eq_unmasked]
    simpa using congrArg (fun x : ℝ => s j * x)
      (other_component_zero G hfO hji G.arc.axis)
  · simp




open P202Specs.PlanarRegionTopology P202Specs.ChartRegionStokes
open P202Specs.BoundaryGraphDirections P202Specs.ContinuousGraphFlux

lemma local_carrier_eq_closedEpigraph {R : PlanarRegion}
    {s : Fin R.boundaryCount → ℝ} {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) :
    R.carrier ∩ O = closedEpigraph 0 G.arc.axis G.height ∩ O := by
  have hF (z : Plane) : G.frame.map z = frame 0 G.arc.axis (z 0,z 1) := by
    simp [G.frame.formula, frame]
  ext x
  rw [show R.carrier = R.domain ∪ R.boundary from closure_eq_self_union_frontier R.domain]
  constructor
  · rintro ⟨hx | hx,hO⟩
    · obtain ⟨z,hz,hzx⟩ := (G.domain_eq ▸ (show x ∈ R.domain ∩ O from ⟨hx,hO⟩)).1
      exact ⟨⟨(z 0,z 1), (show G.height (z 0) ≤ z 1 from le_of_lt hz), (hF z).symm.trans hzx⟩,hO⟩
    · obtain ⟨z,hz,hzx⟩ := (G.boundary_eq ▸ (show x ∈ R.boundary ∩ O from ⟨hx,hO⟩)).1
      exact ⟨⟨(z 0,z 1), (show G.height (z 0) ≤ z 1 from le_of_eq hz.symm), (hF z).symm.trans hzx⟩,hO⟩
  · rintro ⟨⟨q,hq,hqx⟩,hO⟩
    have hfq : G.frame.map !₂[q.1,q.2] = x := by
      simpa only [hF, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using hqx
    change G.height q.1 ≤ q.2 at hq
    rcases lt_or_eq_of_le hq with hlt | heq
    · have hmem : x ∈ R.domain ∩ O := G.domain_eq.symm ▸
        (show x ∈ (G.frame.map '' {z : Plane | G.height (z 0) < z 1}) ∩ O from
          ⟨⟨!₂[q.1,q.2],hlt,hfq⟩,hO⟩)
      exact ⟨Or.inl hmem.1,hO⟩
    · have hmem : x ∈ R.boundary ∩ O := G.boundary_eq.symm ▸
        (show x ∈ (G.frame.map '' {z : Plane | z 1 = G.height (z 0)}) ∩ O from
          ⟨⟨!₂[q.1,q.2],heq.symm,hfq⟩,hO⟩)
      exact ⟨Or.inr hmem.1,hO⟩

lemma closedEpigraph_isClosed (p e : Plane) (he : ‖e‖ = 1)
    (g : ℝ → ℝ) (hg : Continuous g) : IsClosed (closedEpigraph p e g) := by
  let H := P202.ContinuousGraphFlux.frameHomeomorph p e he
  have hH : (H : (ℝ × ℝ) → Plane) = frame p e :=
    funext (P202.ContinuousGraphFlux.frameHomeomorph_apply p e he)
  change IsClosed (frame p e '' {q : ℝ × ℝ | g q.1 ≤ q.2})
  rw [← hH]
  exact H.isClosedMap _ (isClosed_le (hg.comp continuous_fst) continuous_snd)

lemma setIntegral_eq_of_local_eq {A B O : Set Plane} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ∩ O = B ∩ O) {f : Plane → ℝ}
    (hf : Function.support f ⊆ O) : (∫ x in A, f x) = ∫ x in B, f x := by
  have hzero (x : Plane) (hx : x ∉ O) : f x = 0 := by
    apply Function.notMem_support.mp
    exact fun h => hx (hf h)
  calc
    _ = ∫ x in A ∩ O, f x :=
      setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hA inter_subset_left
        (fun x hx => hzero x (fun h => hx.2 ⟨hx.1,h⟩))
    _ = ∫ x in B ∩ O, f x := by rw [hAB]
    _ = ∫ x in B, f x :=
      (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hB inter_subset_left
        (fun x hx => hzero x (fun h => hx.2 ⟨hx.1,h⟩))).symm

lemma local_scalar_bulk {R : PlanarRegion}
    {s : Fin R.boundaryCount → ℝ} {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) {f : Plane → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) (hO : tsupport f ⊆ O) :
    (∫ x in R.carrier, fderiv ℝ f x (quarterTurn G.arc.axis)) =
      -(∫ x : ℝ, f (frame 0 G.arc.axis (x,G.height x))) := by
  have hl := setIntegral_eq_of_local_eq
    (A := R.carrier) (B := closedEpigraph 0 G.arc.axis G.height)
    isClosed_closure.measurableSet
    (closedEpigraph_isClosed 0 G.arc.axis G.arc.unit_axis G.height G.continuous_height).measurableSet
    (local_carrier_eq_closedEpigraph G)
    (f := fun x => fderiv ℝ f x (quarterTurn G.arc.axis))
    ((subset_tsupport _).trans
      ((tsupport_fderiv_apply_subset ℝ _).trans hO))
  exact hl.trans (P202.ContinuousGraphFlux.verticalFlux 0 G.arc.axis G.arc.unit_axis
    G.height G.continuous_height f hf hc).2.2.2.2.2

/-- Scalar form whose exterior derivative is the constant inward-direction derivative. -/
def scalarOneForm (e : Plane) (f : Plane → ℝ) : OneForm :=
  fun x => (-f x) • innerSL ℝ e

lemma scalarOneForm_exterior (e : Plane) {f : Plane → ℝ}
    (hf : Differentiable ℝ f) (x : Plane) :
    exteriorCoefficient (scalarOneForm e f) x = fderiv ℝ f x (quarterTurn e) := by
  have hder := ((hf x).hasFDerivAt.neg.smul_const (innerSL ℝ e)).fderiv
  simp only [Pi.neg_apply] at hder
  rw [show scalarOneForm e f = (fun x => (-f x) • innerSL ℝ e) from rfl]
  unfold exteriorCoefficient
  rw [hder]
  simp [coordinateFrame, quarterTurn, innerSL_apply_apply, real_inner_comm,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  rw [show (!₂[-e 1,e 0] : Plane) =
    (-e 1) • EuclideanSpace.single 0 1 + (e 0) • EuclideanSpace.single 1 1 by
      ext i; fin_cases i <;> simp]
  simp only [map_add, map_smul, smul_eq_mul]
  ring


lemma plane_coordinates (v : Plane) :
    v = (v 0) • coordinateFrame 0 + (v 1) • coordinateFrame 1 := by
  ext j; fin_cases j <;> simp [coordinateFrame]

lemma covector_coordinates (α : Plane →L[ℝ] ℝ) (v : Plane) :
    α v = (v 0) * α (coordinateFrame 0) + (v 1) * α (coordinateFrame 1) := by
  conv_lhs => rw [plane_coordinates v]
  simp [map_add, map_smul]

/-- Rotation of coefficient covector into the divergence vector. -/
def formVector : (Plane →L[ℝ] ℝ) →L[ℝ] Plane where
  toFun α := !₂[α (coordinateFrame 1), -α (coordinateFrame 0)]
  map_add' α β := by ext j; fin_cases j <;> simp <;> ring
  map_smul' r α := by ext j; fin_cases j <;> simp
  cont := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    apply continuous_pi
    intro j
    fin_cases j <;> fun_prop

lemma formVector_injective : Function.Injective formVector := by
  intro α β h
  have h0 := congrArg (fun v : Plane => v 0) h
  have h1 := congrArg (fun v : Plane => v 1) h
  simp only [formVector, ContinuousLinearMap.coe_mk', LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    neg_inj] at h0 h1
  ext v
  rw [covector_coordinates α v, covector_coordinates β v, h0, h1]

lemma formVector_scalarOneForm (e : Plane) (f : Plane → ℝ) (x : Plane) :
    formVector (scalarOneForm e f x) = f x • quarterTurn e := by
  ext j
  fin_cases j <;> simp [formVector, scalarOneForm, quarterTurn, coordinateFrame,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct] <;> ring

def directionBasis {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ} {p : Plane}
    (G : TwoDirectionBoundaryGraphs R s p) : Basis (Fin 2) ℝ Plane :=
  basisOfLinearIndependentOfCardEqFinrank G.independent (by simp)

@[simp] lemma directionBasis_apply {R : PlanarRegion} {s : Fin R.boundaryCount → ℝ}
    {p : Plane} (G : TwoDirectionBoundaryGraphs R s p) (k : Fin 2) :
    directionBasis G k = quarterTurn (G.graphs k).arc.axis := by
  simp [directionBasis]

/-- Fixed continuous linear extraction of the coefficients in two transverse directions. -/
def formCoefficient (b : Basis (Fin 2) ℝ Plane) (k : Fin 2) :
    (Plane →L[ℝ] ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj k).comp (b.equivFunL.toContinuousLinearMap.comp formVector)

lemma two_direction_decomposition {R : PlanarRegion}
    {s : Fin R.boundaryCount → ℝ} {p : Plane}
    (G : TwoDirectionBoundaryGraphs R s p) (omega : OneForm) :
    omega = ∑ k : Fin 2, scalarOneForm (G.graphs k).arc.axis
      (fun x => formCoefficient (directionBasis G) k (omega x)) := by
  funext x
  apply formVector_injective
  simp only [Finset.sum_apply, map_sum, formVector_scalarOneForm]
  have hb := (directionBasis G).sum_repr (formVector (omega x))
  change formVector (omega x) = ∑ k : Fin 2,
    ((directionBasis G).repr (formVector (omega x))) k • quarterTurn (G.graphs k).arc.axis
  simpa only [directionBasis_apply] using hb.symm

lemma formCoefficient_contDiff {b : Basis (Fin 2) ℝ Plane} {omega : OneForm}
    (homega : ContDiff ℝ ∞ omega) (k : Fin 2) :
    ContDiff ℝ ∞ (fun x => formCoefficient b k (omega x)) :=
  (formCoefficient b k).contDiff.comp homega

lemma formCoefficient_tsupport {b : Basis (Fin 2) ℝ Plane} (omega : OneForm) (k : Fin 2) :
    tsupport (fun x => formCoefficient b k (omega x)) ⊆ tsupport omega :=
  tsupport_comp_subset (g := formCoefficient b k) (map_zero _) omega


lemma scalarOneForm_contDiff {e : Plane} {f : Plane → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (scalarOneForm e f) :=
  hf.neg.smul contDiff_const

lemma scalar_supported_stokes {R : PlanarRegion}
    {s : Fin R.boundaryCount → ℝ} {i : Fin R.boundaryCount} {t : ℝ} {O : Set Plane}
    (G : LocalDirectedBoundaryGraph R s i t O) (hs : s i = 1 ∨ s i = -1)
    {f : Plane → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hO : tsupport f ⊆ O) :
    bulkIntegral R (scalarOneForm G.arc.axis f) =
      boundaryIntegral R (scalarOneForm G.arc.axis f) s := by
  have htrace := local_graph_boundaryIntegral G hs (f := fun x => -f x)
    hf.continuous.neg (by
      intro x hx
      apply hO
      apply subset_tsupport f
      exact neg_ne_zero.mp hx)
  have htrace' : -(∫ x : ℝ, f (frame 0 G.arc.axis (x,G.height x))) =
      boundaryIntegral R (scalarOneForm G.arc.axis f) s := by
    change -(∫ x : ℝ, f (frame 0 G.arc.axis (x,G.height x))) =
      boundaryIntegral R (fun z => (-f z) • innerSL ℝ G.arc.axis) s
    simpa only [integral_neg] using htrace
  unfold bulkIntegral
  have hcoeff : exteriorCoefficient (scalarOneForm G.arc.axis f) =
      (fun x => fderiv ℝ f x (quarterTurn G.arc.axis)) := by
    funext x
    exact scalarOneForm_exterior G.arc.axis (hf.differentiable (by simp)) x
  rw [hcoeff]
  exact (local_scalar_bulk G (hf.of_le (by simp)) hc hO).trans htrace'

/-- Local Stokes, including at joins and reflex corners, from two original graph directions. -/
theorem two_direction_supported_stokes {R : PlanarRegion}
    {s : Fin R.boundaryCount → ℝ} {p : Plane} (G : TwoDirectionBoundaryGraphs R s p)
    (hs : IsInducedBoundaryOrientation R s)
    {omega : OneForm} (ho : ContDiff ℝ ∞ omega) (hc : HasCompactSupport omega)
    (hsub : tsupport omega ⊆ G.neighborhood) :
    bulkIntegral R omega = boundaryIntegral R omega s := by
  let f : Fin 2 → Plane → ℝ := fun k x => formCoefficient (directionBasis G) k (omega x)
  let eta : Fin 2 → OneForm := fun k => scalarOneForm (G.graphs k).arc.axis (f k)
  have hf : ∀ k, ContDiff ℝ ∞ (f k) := fun k => formCoefficient_contDiff ho k
  have he : ∀ k, ContDiff ℝ ∞ (eta k) := fun k => scalarOneForm_contDiff (hf k)
  have hcf : ∀ k, HasCompactSupport (f k) := fun k =>
    hc.comp_left (g := formCoefficient (directionBasis G) k) (map_zero _)
  have hsf : ∀ k, tsupport (f k) ⊆ G.neighborhood := fun k =>
    (formCoefficient_tsupport omega k).trans hsub
  have hdecomp : omega = (fun x => ∑ k : Fin 2, eta k x) :=
    two_direction_decomposition G omega
  calc
    bulkIntegral R omega = bulkIntegral R (fun x => ∑ k : Fin 2, eta k x) :=
      congrArg (bulkIntegral R) hdecomp
    _ = ∑ k : Fin 2, bulkIntegral R (eta k) :=
      bulkIntegral_sum Finset.univ R eta (fun k _ => he k)
    _ = ∑ k : Fin 2, boundaryIntegral R (eta k) s := by
      apply Finset.sum_congr rfl
      intro k _
      exact scalar_supported_stokes (G.graphs k) (hs G.component).1 (hf k) (hcf k) (hsf k)
    _ = boundaryIntegral R (fun x => ∑ k : Fin 2, eta k x) s :=
      (boundaryIntegral_sum Finset.univ R eta (fun k _ => (he k).continuous) s).symm
    _ = boundaryIntegral R omega s := congrArg (fun w => boundaryIntegral R w s) hdecomp.symm



/-- Every ambient point has a neighborhood on which compactly supported
forms satisfy Stokes. Boundary patches use the two actual oriented graph
representations, including at the noncuspidal corners. -/
theorem local_stokes_neighborhood (R : PlanarRegion)
    (s : Fin R.boundaryCount → ℝ) (hs : IsInducedBoundaryOrientation R s)
    (x : Plane) : ∃ O : Set Plane, IsOpen O ∧ x ∈ O ∧
      ∀ eta : OneForm, ContDiff ℝ ∞ eta → HasCompactSupport eta →
        tsupport eta ⊆ O → bulkIntegral R eta = boundaryIntegral R eta s := by
  classical
  by_cases hb : x ∈ R.boundary
  · obtain ⟨G⟩ := P202.BoundaryGraphDirections.boundaryGraphDirections R s hs x hb
    exact ⟨G.neighborhood, G.open_neighborhood, G.mem_neighborhood,
      fun eta he hc hsub => two_direction_supported_stokes G hs he hc hsub⟩
  · by_cases hi : x ∈ R.domain
    · exact ⟨R.domain, R.open_domain, hi, fun eta he hc hsub =>
        interior_supported_stokes R (he.of_le (by simp)) hc hsub s⟩
    · have hout : x ∈ R.carrierᶜ := by
        change x ∉ closure R.domain
        rw [closure_eq_self_union_frontier]
        exact not_or.mpr ⟨hi, hb⟩
      exact ⟨R.carrierᶜ, isClosed_closure.isOpen_compl, hout,
        fun eta _ _ hsub => exterior_supported_stokes R hsub s⟩

/-- Stokes for the original compact planar region, with its induced signs
on all boundary components. The continuous graph proof covers reflex
corners directly and never deletes an incident arc. -/
theorem stokes : P202Specs.ChartRegionStokes.Expected.stokes := by
  apply stokes_of_compactSupport
  intro R omega homega hsupport s hs
  exact compactSupported_stokes_of_local R s
    (local_stokes_neighborhood R s hs) homega hsupport

/-- Positive-chart specialization for the actual intrinsic surface form. -/
theorem surfaceChartStokes :
    P202Specs.ChartRegionStokes.Expected.surfaceChartStokes.{u} :=
  surfaceChartStokes_of_stokes stokes

end P202.ChartRegionStokes
