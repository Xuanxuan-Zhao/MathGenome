import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonlinearCompactExistence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.Ascoli
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.Schauder
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
universe u v

namespace ExpandedFA.PartV.NonlinearCompactExistence

/-- The compact-image consequence of the accepted Schauder theorem, using
completeness only to make the closed convex hull compact. -/
theorem fixedPoint_of_compact_image
    {E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {D : Set E} (hne : D.Nonempty) (hclosed : IsClosed D) (hconvex : Convex ℝ D)
    (V : D → E) (hV : Continuous V) (hinv : ∀ x, V x ∈ D)
    (hc : IsCompact (closure (range V))) : ∃ x : D, V x = x.val := by
  let K := closure (convexHull ℝ (range V))
  have hKD : K ⊆ D :=
    closure_minimal (convexHull_min (range_subset_iff.mpr hinv) hconvex) hclosed
  have hKc : IsCompact K := by
    exact (hc.totallyBounded.subset subset_closure).convexHull.closure.isCompact_of_isClosed
      isClosed_closure
  have hKn : K.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨V ⟨x, hx⟩, subset_closure (subset_convexHull ℝ _ (mem_range_self _))⟩
  let W : K → K := fun x =>
    ⟨V ⟨x.val, hKD x.property⟩, subset_closure (subset_convexHull ℝ _ (mem_range_self _))⟩
  have hW : Continuous W := by
    apply Continuous.subtype_mk
    exact hV.comp (continuous_subtype_val.subtype_mk _)
  obtain ⟨x, hx⟩ := ExpandedFA.P1.Schauder.schauder_tychonoff ℝ E
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ K hKn hKc
      (convex_convexHull ℝ _).closure W hW
  exact ⟨⟨x.val, hKD x.property⟩, congrArg Subtype.val hx⟩

variable {𝕜 : Type u} [RCLike 𝕜] {T R : ℝ}

lemma continuous_trianglePoint :
    Continuous (fun p : Time T × ℝ => trianglePoint p.1 p.2) := by
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_fst).prodMk
    (continuous_const.max ((continuous_subtype_val.comp continuous_fst).min continuous_snd))

lemma continuous_state :
    Continuous (fun p : Ball 𝕜 T R × Time T => state p.1 p.2) := by
  apply Continuous.subtype_mk
  exact continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

lemma continuous_integrand (hT : 0 ≤ T) (G : Kernel 𝕜 T R) :
    Continuous (fun p : (Ball 𝕜 T R × Time T) × ℝ => integrand hT G p.1.1 p.1.2 p.2) := by
  apply G.continuous.comp
  exact (continuous_trianglePoint.comp
    (continuous_fst.snd.prodMk (continuous_subtype_val.comp ((show Continuous (projIcc 0 T hT) from continuous_projIcc).comp continuous_snd)))).prodMk
    (continuous_state.comp
      (continuous_fst.fst.prodMk ((show Continuous (projIcc 0 T hT) from continuous_projIcc).comp continuous_snd)))

lemma integrand_restriction (hT : 0 ≤ T) (G : Kernel 𝕜 T R)
    (u : Ball 𝕜 T R) (t : Time T) (s : ℝ) (hs : s ∈ Icc 0 t.val) :
    integrand hT G u t s =
      G (⟨(t.val, s), hs.1, hs.2, t.property.2⟩,
        state u ⟨s, hs.1, hs.2.trans t.property.2⟩) := by
  unfold integrand
  rw [projIcc_of_mem hT ⟨hs.1, hs.2.trans t.property.2⟩]
  congr 2
  apply Subtype.ext
  simp [trianglePoint, min_eq_right hs.2, max_eq_right hs.1]

lemma intervalIntegrable_integrand (hT : 0 ≤ T) (G : Kernel 𝕜 T R)
    (u : Ball 𝕜 T R) (t : Time T) (a b : ℝ) :
    IntervalIntegrable (integrand hT G u t) volume a b :=
  ((continuous_integrand hT G).comp
    ((continuous_const : Continuous (fun _ : ℝ => (u, t))).prodMk continuous_id)).intervalIntegrable a b

lemma continuous_rhs (hT : 0 ≤ T) (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) :
    Continuous (fun p : Ball 𝕜 T R × Time T => rhs hT f G p.1 p.2) := by
  exact (f.continuous.comp continuous_snd).add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (continuous_integrand hT G) (continuous_subtype_val.comp continuous_snd))

/-- The actual ordinary Volterra integral map into the supremum norm space. -/
def ordinaryMap (hT : 0 ≤ T) (f : Curve 𝕜 T) (G : Kernel 𝕜 T R)
    (u : Ball 𝕜 T R) : Curve 𝕜 T :=
  ⟨rhs hT f G u, (continuous_rhs hT f G).comp (continuous_const.prodMk continuous_id)⟩

lemma continuous_ordinaryMap (hT : 0 ≤ T) (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) :
    Continuous (ordinaryMap hT f G) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_rhs hT f G)

lemma ordinary_integral_bound (hT : 0 ≤ T) (G : Kernel 𝕜 T R)
    (u : Ball 𝕜 T R) (t : Time T) :
    ‖∫ s in 0..t.val, integrand hT G u t s‖ ≤ t.val * ‖G‖ := by
  have h : ‖∫ s in 0..t.val, integrand hT G u t s‖ ≤ ‖G‖ * |t.val - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s _ => G.norm_coe_le_norm _)
  simpa only [sub_zero, abs_of_nonneg t.property.1, mul_comm ‖G‖] using h

lemma ordinaryMap_norm_le (hT : 0 ≤ T) (f : Curve 𝕜 T) (G : Kernel 𝕜 T R)
    (u : Ball 𝕜 T R) : ‖ordinaryMap hT f G u‖ ≤ ‖f‖ + T * ‖G‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  calc
    _ ≤ ‖f t‖ + ‖∫ s in 0..t.val, integrand hT G u t s‖ := norm_add_le _ _
    _ ≤ ‖f‖ + t.val * ‖G‖ := add_le_add (f.norm_coe_le_norm t)
      (ordinary_integral_bound hT G u t)
    _ ≤ ‖f‖ + T * ‖G‖ := by gcongr; exact t.property.2

/-- Compactly parameterized kernel sections. The state variable is free, so
their uniform continuity does not require equicontinuity of the input ball. -/
def kernelSection (G : Kernel 𝕜 T R) (t : Time T) :
    C(Time T × Metric.closedBall (0 : 𝕜) R, 𝕜) :=
  ⟨fun p => G (trianglePoint t p.1, p.2), by
    apply G.continuous.comp
    exact (continuous_trianglePoint.comp
      (continuous_const.prodMk (continuous_subtype_val.comp continuous_fst))).prodMk continuous_snd⟩

lemma continuous_kernelSection (G : Kernel 𝕜 T R) : Continuous (kernelSection G) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply G.continuous.comp
  exact (continuous_trianglePoint.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd.fst))).prodMk continuous_snd.snd

lemma integrand_sub_bound (hT : 0 ≤ T) (G : Kernel 𝕜 T R)
    (u : Ball 𝕜 T R) (t t' : Time T) (s : ℝ) :
    ‖integrand hT G u t s - integrand hT G u t' s‖ ≤
      ‖kernelSection G t - kernelSection G t'‖ := by
  exact (kernelSection G t - kernelSection G t').norm_coe_le_norm
    (projIcc 0 T hT s, state u (projIcc 0 T hT s))

lemma ordinaryMap_increment (hT : 0 ≤ T) (f : Curve 𝕜 T) (G : Kernel 𝕜 T R)
    (u : Ball 𝕜 T R) (t t' : Time T) :
    ‖ordinaryMap hT f G u t - ordinaryMap hT f G u t'‖ ≤
      ‖f t - f t'‖ + T * ‖kernelSection G t - kernelSection G t'‖ +
        ‖G‖ * |t.val - t'.val| := by
  have hsplit : (∫ s in 0..t.val, integrand hT G u t s) -
      (∫ s in 0..t'.val, integrand hT G u t' s) =
      (∫ s in 0..t.val, integrand hT G u t s - integrand hT G u t' s) +
      (∫ s in t'.val..t.val, integrand hT G u t' s) := by
    rw [intervalIntegral.integral_sub
      (intervalIntegrable_integrand hT G u t _ _)
      (intervalIntegrable_integrand hT G u t' _ _),
      ← intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_integrand hT G u t' 0 t'.val)
        (intervalIntegrable_integrand hT G u t' t'.val t.val)]
    abel
  have hfirst : ‖∫ s in 0..t.val, integrand hT G u t s - integrand hT G u t' s‖ ≤
      T * ‖kernelSection G t - kernelSection G t'‖ := by
    calc
      _ ≤ ‖kernelSection G t - kernelSection G t'‖ * |t.val - 0| :=
        intervalIntegral.norm_integral_le_of_norm_le_const
          (fun s _ => integrand_sub_bound hT G u t t' s)
      _ ≤ T * ‖kernelSection G t - kernelSection G t'‖ := by
        rw [sub_zero, abs_of_nonneg t.property.1, mul_comm]
        exact mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg _)
  have hsecond : ‖∫ s in t'.val..t.val, integrand hT G u t' s‖ ≤
      ‖G‖ * |t.val - t'.val| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun s _ => G.norm_coe_le_norm _)
  change ‖(f t + _) - (f t' + _)‖ ≤ _
  rw [add_sub_add_comm, hsplit]
  rw [add_assoc]
  exact (norm_add_le _ _).trans
    (add_le_add le_rfl ((norm_add_le _ _).trans (add_le_add hfirst hsecond)))


lemma equicontinuous_ordinaryMap (hT : 0 ≤ T) (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) :
    Equicontinuous (fun u : Ball 𝕜 T R => (ordinaryMap hT f G u : Time T → 𝕜)) := by
  intro x
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  let b : Time T → ℝ := fun y => ‖f y - f x‖ +
    T * ‖kernelSection G y - kernelSection G x‖ + ‖G‖ * |y.val - x.val|
  have hb : Continuous b := by
    exact ((f.continuous.sub continuous_const).norm.add
      (((continuous_kernelSection G).sub continuous_const).norm.const_mul T)).add
      ((continuous_subtype_val.sub continuous_const).abs.const_mul ‖G‖)
  have hx : b x = 0 := by simp [b]
  have hev : ∀ᶠ y in 𝓝 x, b y < ε := by
    have h := hb.continuousAt.eventually (gt_mem_nhds (show b x < ε by rwa [hx]))
    exact h
  filter_upwards [hev] with y hy u
  rw [dist_comm, dist_eq_norm]
  exact (ordinaryMap_increment hT f G u y x).trans_lt hy

lemma compact_closure_ordinaryMap (hT : 0 ≤ T) (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) :
    IsCompact (closure (range (ordinaryMap hT f G))) := by
  apply (ExpandedFA.PartV.Ascoli.arzela_ascoli 𝕜 (Time T)
    (range (ordinaryMap hT f G))).mpr
  constructor
  · refine ⟨‖f‖ + T * ‖G‖, by positivity, ?_⟩
    rintro g ⟨u, rfl⟩ t
    exact ((ordinaryMap hT f G u).norm_coe_le_norm t).trans
      (ordinaryMap_norm_le hT f G u)
  · intro x
    rw [Metric.equicontinuousAt_iff_right]
    have h := equicontinuous_ordinaryMap hT f G x
    rw [Metric.equicontinuousAt_iff_right] at h
    intro ε hε
    filter_upwards [h ε hε] with y hy g
    obtain ⟨u, hu⟩ := g.property
    rw [← hu]
    exact hy u

/-- Continuous scalar Volterra existence on the full prescribed interval,
without any Lipschitz assumption. -/
theorem ordinary_existence : Spec.OrdinaryExistence.{u} := by
  intro 𝕜 _ T R hT f G hinv
  have hR : 0 ≤ R := (add_nonneg (norm_nonneg _) (mul_nonneg hT (norm_nonneg _))).trans hinv
  let V := ordinaryMap hT f G
  have hmaps : ∀ u : Ball 𝕜 T R, V u ∈ Metric.closedBall (0 : Curve 𝕜 T) R := by
    intro u
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (ordinaryMap_norm_le hT f G u).trans hinv
  obtain ⟨u, hu⟩ := fixedPoint_of_compact_image
    (D := Metric.closedBall (0 : Curve 𝕜 T) R)
    (Metric.nonempty_closedBall.mpr hR) Metric.isClosed_closedBall
    (convex_closedBall (0 : Curve 𝕜 T) R) V (continuous_ordinaryMap hT f G)
    hmaps (compact_closure_ordinaryMap hT f G)
  exact ⟨V, fun _ _ => rfl, continuous_ordinaryMap hT f G,
    compact_closure_ordinaryMap hT f G, fun u => (ordinaryMap_norm_le hT f G u).trans hinv,
    u, hu⟩

/-! Singular weights are approached in L¹ by continuous nonnegative weights.
This gives a uniform approximation of the nonlinear maps on the whole input
ball, including when α < 1. -/

def regularWeight (α : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  (max 0 r) ^ α / (max 0 r + 1 / ((n : ℝ) + 1))

lemma continuous_regularWeight {α : ℝ} (hα : 0 < α) (n : ℕ) :
    Continuous (regularWeight α n) := by
  apply Continuous.div
  · exact (Real.continuous_rpow_const hα.le).comp (continuous_const.max continuous_id)
  · exact (continuous_const.max continuous_id).add continuous_const
  · intro r
    exact ne_of_gt (add_pos_of_nonneg_of_pos (le_max_left _ _) (by positivity))

lemma regularWeight_bounds {α r : ℝ} (n : ℕ) (hr : 0 < r) :
    0 ≤ regularWeight α n r ∧ regularWeight α n r ≤ r ^ (α - 1) := by
  rw [regularWeight, max_eq_right hr.le]
  have hpow := Real.rpow_pos_of_pos hr α
  constructor
  · positivity
  · rw [Real.rpow_sub hr, Real.rpow_one]
    apply div_le_div_of_nonneg_left hpow.le hr
    linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]

lemma regularWeight_tendsto {α r : ℝ} (hr : 0 < r) :
    Tendsto (fun n => regularWeight α n r) atTop (𝓝 (r ^ (α - 1))) := by
  simp only [regularWeight, max_eq_right hr.le]
  have hd : Tendsto (fun n : ℕ => r + 1 / ((n : ℝ) + 1)) atTop (𝓝 r) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)))
  convert tendsto_const_nhds.div hd hr.ne' using 1
  rw [Real.rpow_sub hr, Real.rpow_one]

lemma intervalIntegrable_weight {α : ℝ} (hα : 0 < α) (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => (t - s) ^ (α - 1)) volume 0 t := by
  have h : IntervalIntegrable (fun r : ℝ => r ^ (α - 1)) volume t 0 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  simpa only [sub_self, sub_zero] using h.comp_sub_left t

lemma weight_mass {α : ℝ} (hα : 0 < α) {t : ℝ} (ht : 0 ≤ t) :
    (∫ s in 0..t, (t - s) ^ (α - 1)) = t ^ α / α := by
  rw [intervalIntegral.integral_comp_sub_left (fun r : ℝ => r ^ (α - 1)) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by linarith : -1 < α - 1))]
  simp [sub_add_cancel, Real.zero_rpow hα.ne']

lemma intervalIntegrable_fractional (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    (G : Kernel 𝕜 T R) (u : Ball 𝕜 T R) (t : Time T) :
    IntervalIntegrable (fun s : ℝ => (t.val - s) ^ (α - 1) • integrand hT G u t s)
      volume 0 t.val :=
  (intervalIntegrable_weight hα t.val).smul_continuousOn
    (((continuous_integrand hT G).comp
      ((continuous_const : Continuous (fun _ : ℝ => (u, t))).prodMk continuous_id)).continuousOn)

lemma fractional_integral_bound (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    (G : Kernel 𝕜 T R) (u : Ball 𝕜 T R) (t : Time T) :
    ‖∫ s in 0..t.val, (t.val - s) ^ (α - 1) • integrand hT G u t s‖ ≤
      (t.val ^ α / α) * ‖G‖ := by
  calc
    _ ≤ ∫ s in 0..t.val, (t.val - s) ^ (α - 1) * ‖G‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le t.property.1
      · apply Eventually.of_forall
        intro s hs
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
          (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)]
        exact mul_le_mul_of_nonneg_left (G.norm_coe_le_norm _)
          (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)
      · exact (intervalIntegrable_weight hα t.val).mul_const _
    _ = (t.val ^ α / α) * ‖G‖ := by
      rw [intervalIntegral.integral_mul_const, weight_mass hα t.property.1]

/-- Uniform scalar error budget for all upper endpoints 0 ≤ t ≤ T. -/
def weightError (T α : ℝ) (n : ℕ) : ℝ :=
  ∫ r in 0..T, |r ^ (α - 1) - regularWeight α n r|

lemma intervalIntegrable_weightError {α : ℝ} (hα : 0 < α) (n : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun r : ℝ => |r ^ (α - 1) - regularWeight α n r|) volume a b :=
  ((intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < α - 1)).sub
    ((continuous_regularWeight hα n).intervalIntegrable a b)).abs

lemma weightError_nonneg (hT : 0 ≤ T) (α : ℝ) (n : ℕ) :
    0 ≤ weightError T α n :=
  intervalIntegral.integral_nonneg hT (fun _ _ => abs_nonneg _)

lemma weightError_tendsto (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α) :
    Tendsto (weightError T α) atTop (𝓝 0) := by
  have hi : Integrable (fun r : ℝ => r ^ (α - 1)) (volume.restrict (Ioc 0 T)) := by
    have h := intervalIntegral.intervalIntegrable_rpow'
      (a := 0) (b := T) (by linarith : -1 < α - 1)
    rw [intervalIntegrable_iff, uIoc_of_le hT] at h
    exact h
  have hlim := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc 0 T)) (fun r : ℝ => r ^ (α - 1))
    (F := fun n r => |r ^ (α - 1) - regularWeight α n r|) (f := fun _ => 0)
    (fun n => (intervalIntegrable_weightError hα n 0 T).1.aestronglyMeasurable)
    hi ?_ ?_
  · change Tendsto (fun n => ∫ r in 0..T, |r ^ (α - 1) - regularWeight α n r|) _ _
    simpa only [intervalIntegral.integral_of_le hT, integral_zero] using hlim
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    obtain ⟨h0, hle⟩ := regularWeight_bounds (α := α) n hr.1
    rw [Real.norm_eq_abs, abs_abs, abs_of_nonneg (sub_nonneg.mpr hle)]
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    simpa only [sub_self, abs_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => r ^ (α - 1)) atTop
        (𝓝 (r ^ (α - 1)))).sub (regularWeight_tendsto (α := α) hr.1)).abs

/-- Continuous kernels with a bounded approximation to the singular factor. -/
def regularKernel {α : ℝ} (hα : 0 < α) (G : Kernel 𝕜 T R) (n : ℕ) : Kernel 𝕜 T R :=
  ⟨fun p => regularWeight α n (p.1.val.1 - p.1.val.2) • G p, by
    apply Continuous.smul _ G.continuous
    exact (continuous_regularWeight hα n).comp
      (((continuous_subtype_val.comp continuous_fst).fst).sub
        ((continuous_subtype_val.comp continuous_fst).snd))⟩

lemma ordinaryMap_regularKernel (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) (n : ℕ)
    (u : Ball 𝕜 T R) (t : Time T) :
    ordinaryMap hT f (regularKernel hα G n) u t =
      f t + ∫ s in 0..t.val, regularWeight α n (t.val - s) • integrand hT G u t s := by
  change f t + _ = f t + _
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  rw [uIcc_of_le t.property.1] at hs
  change integrand hT (regularKernel hα G n) u t s =
    regularWeight α n (t.val - s) • integrand hT G u t s
  simp only [integrand_restriction hT (regularKernel hα G n) u t s hs,
    integrand_restriction hT G u t s hs]
  rfl

lemma fractional_approx_bound (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) (n : ℕ)
    (u : Ball 𝕜 T R) (t : Time T) :
    ‖fractionalRhs hT α f G u t - ordinaryMap hT f (regularKernel hα G n) u t‖ ≤
      weightError T α n * ‖G‖ := by
  rw [ordinaryMap_regularKernel hT hα f G n u t]
  unfold fractionalRhs
  have hreg : IntervalIntegrable
      (fun s : ℝ => regularWeight α n (t.val - s) • integrand hT G u t s)
      volume 0 t.val := by
    exact (((continuous_regularWeight hα n).comp
      ((continuous_const : Continuous (fun _ : ℝ => t.val)).sub continuous_id)).smul
      ((continuous_integrand hT G).comp
        ((continuous_const : Continuous (fun _ : ℝ => (u, t))).prodMk continuous_id)))
      |>.intervalIntegrable 0 t.val
  rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
    (intervalIntegrable_fractional hT hα G u t) hreg]

  calc
    _ ≤ ∫ s in 0..t.val,
        |(t.val - s) ^ (α - 1) - regularWeight α n (t.val - s)| * ‖G‖ := by
      apply intervalIntegral.norm_integral_le_of_norm_le t.property.1
      · apply Eventually.of_forall
        intro s _
        rw [← sub_smul, norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (G.norm_coe_le_norm _) (abs_nonneg _)
      · have hi : IntervalIntegrable
            (fun r : ℝ => |r ^ (α - 1) - regularWeight α n r|) volume t.val 0 :=
          intervalIntegrable_weightError hα n _ _
        simpa only [sub_self, sub_zero] using (hi.comp_sub_left t.val).mul_const ‖G‖
    _ = (∫ r in 0..t.val, |r ^ (α - 1) - regularWeight α n r|) * ‖G‖ := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_comp_sub_left
          (fun r : ℝ => |r ^ (α - 1) - regularWeight α n r|) t.val]
      simp only [sub_self, sub_zero]
    _ ≤ weightError T α n * ‖G‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact intervalIntegral.integral_mono_interval le_rfl t.property.1 t.property.2
        (Eventually.of_forall (fun r => abs_nonneg _))
        (intervalIntegrable_weightError hα n 0 T)

lemma fractional_uniform_approx (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) :
    TendstoUniformly
      (fun n (p : Ball 𝕜 T R × Time T) => ordinaryMap hT f (regularKernel hα G n) p.1 p.2)
      (fun p => fractionalRhs hT α f G p.1 p.2) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hz : Tendsto (fun n => weightError T α n * ‖G‖) atTop (𝓝 0) := by
    simpa only [zero_mul] using (weightError_tendsto hT hα).mul_const ‖G‖
  filter_upwards [hz.eventually (gt_mem_nhds hε)] with n hn p
  rw [dist_eq_norm]
  exact (fractional_approx_bound hT hα f G n p.1 p.2).trans_lt hn

lemma continuous_fractionalRhs (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) :
    Continuous (fun p : Ball 𝕜 T R × Time T => fractionalRhs hT α f G p.1 p.2) :=
  (fractional_uniform_approx hT hα f G).continuous
    (Frequently.of_forall (fun n => continuous_rhs hT f (regularKernel hα G n)))

/-- The actual weakly singular integral map, whose continuity has been proved. -/
def fractionalMap (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) (u : Ball 𝕜 T R) : Curve 𝕜 T :=
  ⟨fractionalRhs hT α f G u,
    (continuous_fractionalRhs hT hα f G).comp (continuous_const.prodMk continuous_id)⟩

lemma continuous_fractionalMap (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) : Continuous (fractionalMap hT hα f G) :=
  ContinuousMap.continuous_of_continuous_uncurry _ (continuous_fractionalRhs hT hα f G)

lemma fractionalMap_norm_le (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) (u : Ball 𝕜 T R) :
    ‖fractionalMap hT hα f G u‖ ≤ ‖f‖ + (T ^ α / α) * ‖G‖ := by
  apply (ContinuousMap.norm_le _ (by positivity)).mpr
  intro t
  calc
    _ ≤ ‖f t‖ + ‖∫ s in 0..t.val, (t.val - s) ^ (α - 1) • integrand hT G u t s‖ :=
      norm_add_le _ _
    _ ≤ ‖f‖ + (t.val ^ α / α) * ‖G‖ :=
      add_le_add (f.norm_coe_le_norm t) (fractional_integral_bound hT hα G u t)
    _ ≤ ‖f‖ + (T ^ α / α) * ‖G‖ := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact div_le_div_of_nonneg_right
        (Real.rpow_le_rpow t.property.1 t.property.2 hα.le) hα.le

lemma compact_closure_fractionalMap (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) :
    IsCompact (closure (range (fractionalMap hT hα f G))) := by
  have ht : TotallyBounded (range (fractionalMap hT hα f G)) := by
    apply Metric.totallyBounded_iff.mpr
    intro ε hε
    have hz : Tendsto (fun n => weightError T α n * ‖G‖) atTop (𝓝 0) := by
      simpa only [zero_mul] using (weightError_tendsto hT hα).mul_const ‖G‖
    obtain ⟨n, hn⟩ := (hz.eventually (gt_mem_nhds (half_pos hε))).exists
    have happ (u : Ball 𝕜 T R) : dist (fractionalMap hT hα f G u)
        (ordinaryMap hT f (regularKernel hα G n) u) < ε / 2 := by
      apply lt_of_le_of_lt _ hn
      apply (ContinuousMap.dist_le (mul_nonneg (weightError_nonneg hT α n) (norm_nonneg G))).mpr
      intro t
      rw [dist_eq_norm]
      exact fractional_approx_bound hT hα f G n u t
    have htb := (compact_closure_ordinaryMap hT f (regularKernel hα G n)).totallyBounded.subset
      (s₁ := range (ordinaryMap hT f (regularKernel hα G n))) subset_closure
    obtain ⟨s, hs, hcover⟩ := Metric.totallyBounded_iff.mp htb (ε / 2) (half_pos hε)
    refine ⟨s, hs, ?_⟩
    rintro g ⟨u, rfl⟩
    obtain ⟨c, hc, huc⟩ := mem_iUnion₂.mp (hcover (mem_range_self u))
    apply mem_iUnion₂.mpr
    refine ⟨c, hc, ?_⟩
    have hc' : dist (ordinaryMap hT f (regularKernel hα G n) u) c < ε / 2 := huc
    exact (dist_triangle _ _ _).trans_lt (by linarith [happ u])
  exact ht.closure.isCompact_of_isClosed isClosed_closure

/-- Equicontinuity of the singular image, also obtained from its proved
compact closure by the accepted converse of Arzelà–Ascoli. -/
lemma equicontinuous_fractional_image (hT : 0 ≤ T) {α : ℝ} (hα : 0 < α)
    (f : Curve 𝕜 T) (G : Kernel 𝕜 T R) :
    Equicontinuous (fun (g : range (fractionalMap hT hα f G)) (t : Time T) => g.val t) :=
  ExpandedFA.PartV.Ascoli.equicontinuous_of_isCompact_closure
    (compact_closure_fractionalMap hT hα f G)

/-- Weakly singular scalar Volterra existence for every α > 0. -/
theorem fractional_existence : Spec.FractionalExistence.{u} := by
  intro 𝕜 _ T R α hT hα f G hinv
  have hR : 0 ≤ R := (show 0 ≤ ‖f‖ + (T ^ α / α) * ‖G‖ by positivity).trans hinv
  let V := fractionalMap hT hα f G
  have hmaps : ∀ u : Ball 𝕜 T R, V u ∈ Metric.closedBall (0 : Curve 𝕜 T) R := by
    intro u
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (fractionalMap_norm_le hT hα f G u).trans hinv
  obtain ⟨u, hu⟩ := fixedPoint_of_compact_image
    (D := Metric.closedBall (0 : Curve 𝕜 T) R)
    (Metric.nonempty_closedBall.mpr hR) Metric.isClosed_closedBall
    (convex_closedBall (0 : Curve 𝕜 T) R) V (continuous_fractionalMap hT hα f G)
    hmaps (compact_closure_fractionalMap hT hα f G)
  exact ⟨V, fun _ _ => rfl, continuous_fractionalMap hT hα f G,
    compact_closure_fractionalMap hT hα f G,
    fun u => (fractionalMap_norm_le hT hα f G u).trans hinv, u, hu⟩

end ExpandedFA.PartV.NonlinearCompactExistence
