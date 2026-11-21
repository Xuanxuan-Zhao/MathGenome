import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.SemigroupGrowthAndGenerator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Semigroups.C0SemigroupAndGenerator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerIntegral
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.P1.C07UniformBoundedness
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! Growth, strong continuity, and the closed densely defined generator of a
real/complex Banach C₀ semigroup (paper.tex, `fa2:p3:semigroup-basics`).
The integrated orbit operators and their averaging limits are constructed here;
none of the conclusions are assumed as part of the semigroup data. -/

noncomputable section
open Filter Topology MeasureTheory Set
open scoped NNReal

namespace ExpandedFA.Semigroups
variable {𝕜 X : Type*} [RCLike 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

local instance : NormedSpace ℝ X := NormedSpace.restrictScalars ℝ 𝕜 X
local instance : IsScalarTower ℝ 𝕜 X := IsScalarTower.restrictScalars ℝ 𝕜 X

namespace C0Semigroup

@[simp] theorem zero_apply (T : C0Semigroup 𝕜 X) (x : X) : T.operators 0 x = x := by
  rw [T.at_zero]; rfl

theorem add_apply (T : C0Semigroup 𝕜 X) (t s : ℝ≥0) (x : X) :
    T.operators (t + s) x = T.operators t (T.operators s x) := by
  rw [T.add_time]; rfl

theorem operators_commute (T : C0Semigroup 𝕜 X) (t s : ℝ≥0) (x : X) :
    T.operators t (T.operators s x) = T.operators s (T.operators t x) := by
  rw [← T.add_apply, ← T.add_apply, add_comm]

theorem differenceQuotient_commute (T : C0Semigroup 𝕜 X) (t : ℝ≥0) (h : ℝ) (x : X) :
    differenceQuotient T h (T.operators t x) = T.operators t (differenceQuotient T h x) := by
  change (algebraMap ℝ 𝕜 h)⁻¹ • (T.operators h.toNNReal (T.operators t x) - T.operators t x) =
    T.operators t ((algebraMap ℝ 𝕜 h)⁻¹ • (T.operators h.toNNReal x - x))
  simp only [map_smul, map_sub]
  rw [T.operators_commute]

theorem hasGeneratorLimit_map (T : C0Semigroup 𝕜 X) (t : ℝ≥0) {x y : X}
    (h : HasGeneratorLimit T x y) :
    HasGeneratorLimit T (T.operators t x) (T.operators t y) := by
  change Tendsto (fun h => differenceQuotient T h (T.operators t x)) _ _
  change Tendsto (fun h => differenceQuotient T h x) _ _ at h
  have ht := (T.operators t).continuous.continuousAt.tendsto.comp h
  simpa only [Function.comp_def, ← T.differenceQuotient_commute] using ht

/-- The zero-time strong limit forces an operator-norm bound on a whole
right neighborhood. Otherwise Banach–Steinhaus applied to a violating sequence
contradicts its pointwise convergence. -/
theorem locally_bounded (T : C0Semigroup 𝕜 X) :
    ∃ δ C : ℝ, 0 < δ ∧ 1 ≤ C ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ δ → ‖T.operators t‖ ≤ C := by
  classical
  by_contra hn
  have bad : ∀ n : ℕ, ∃ t : ℝ, 0 < t ∧ t ≤ 1 / ((n : ℝ) + 1) ∧
      (n : ℝ) + 1 < ‖T.operators t.toNNReal‖ := by
    intro n
    by_contra h
    push Not at h
    apply hn
    refine ⟨1 / ((n : ℝ) + 1), (n : ℝ) + 1, by positivity, by linarith [Nat.cast_nonneg (α := ℝ) n], ?_⟩
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      rw [T.at_zero]
      exact (ContinuousLinearMap.norm_id_le).trans (by linarith [Nat.cast_nonneg (α := ℝ) n])
    · simpa using h (t : ℝ) (by exact_mod_cast (pos_iff_ne_zero.mpr ht0)) ht
  choose u hu using bad
  have hu0 : Tendsto u atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => (hu n).1.le) (fun n => (hu n).2.1)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hupos : Tendsto u atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hu0, Eventually.of_forall (fun n => (hu n).1)⟩
  have pointwise : ∀ x : X, ∃ C : ℝ, ∀ n : ℕ, ‖T.operators (u n).toNNReal x‖ ≤ C := by
    intro x
    obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ ((T.strong_zero x).comp hupos)).exists_norm_le
    exact ⟨C, fun n => hC _ (mem_range_self n)⟩
  obtain ⟨C, hC⟩ := banach_steinhaus pointwise
  obtain ⟨n, hnC⟩ := exists_nat_gt C
  exact (not_lt_of_ge (hC n)) (lt_trans (by linarith : C < (n : ℝ) + 1) (hu n).2.2)

theorem norm_nsmul_time_le (T : C0Semigroup 𝕜 X) {r : ℝ≥0} {C : ℝ}
    (hC : 0 ≤ C) (hr : ‖T.operators r‖ ≤ C) (n : ℕ) :
    ‖T.operators (n • r)‖ ≤ C ^ n := by
  induction n with
  | zero => simpa only [zero_nsmul, T.at_zero, pow_zero] using
      (ContinuousLinearMap.norm_id_le (𝕜 := 𝕜) (E := X))
  | succ n ih =>
      rw [succ_nsmul, T.add_time, pow_succ]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul ih hr (norm_nonneg _) (pow_nonneg hC _))

theorem exponential_bound (T : C0Semigroup 𝕜 X) :
    ∃ M ω : ℝ, HasExponentialBound T M ω := by
  obtain ⟨δ, C, hδ, hC, hbound⟩ := T.locally_bounded
  refine ⟨Real.exp C, C / δ, ?_, ?_⟩
  · exact Real.one_le_exp (by linarith)
  · intro t
    let n : ℕ := ⌊(t : ℝ) / δ⌋₊ + 1
    have hn : 0 < (n : ℝ) := by dsimp [n]; positivity
    have hfloor := Nat.floor_le (div_nonneg t.coe_nonneg hδ.le)
    have hfloor' := Nat.lt_floor_add_one ((t : ℝ) / δ)
    have hnle : (n : ℝ) ≤ (t : ℝ) / δ + 1 := by dsimp [n]; push_cast; linarith
    have htn : (t : ℝ) ≤ (n : ℝ) * δ := by
      apply (div_le_iff₀ hδ).mp
      simpa only [n, Nat.cast_add, Nat.cast_one] using hfloor'.le
    let r : ℝ≥0 := ⟨(t : ℝ) / n, div_nonneg t.coe_nonneg hn.le⟩
    have hrδ : (r : ℝ) ≤ δ := (div_le_iff₀ hn).mpr (by simpa [mul_comm] using htn)
    have hnr : n • r = t := by
      apply NNReal.coe_injective
      simp only [nsmul_eq_mul]
      change (n : ℝ) * ((t : ℝ) / n) = (t : ℝ)
      exact mul_div_cancel₀ _ hn.ne'
    have hpow : C ^ n ≤ Real.exp (C * n) := by
      rw [mul_comm C, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by linarith : 0 ≤ C)
        (le_trans (by linarith : C ≤ C + 1) (Real.add_one_le_exp C)) n
    calc
      ‖T.operators t‖ = ‖T.operators (n • r)‖ := by rw [hnr]
      _ ≤ C ^ n := T.norm_nsmul_time_le (by linarith) (hbound r hrδ) n
      _ ≤ Real.exp (C * n) := hpow
      _ ≤ Real.exp (C * ((t : ℝ) / δ + 1)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hnle (by linarith))
      _ = Real.exp C * Real.exp (C / δ * (t : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- Bounded operator norms on every compact time interval, including zero. -/
theorem bounded_on_interval (T : C0Semigroup 𝕜 X) (b : ℝ≥0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ s : ℝ≥0, s ≤ b → ‖T.operators s‖ ≤ C := by
  obtain ⟨M, ω, hM, hbound⟩ := T.exponential_bound
  refine ⟨M * Real.exp (max ω 0 * (b : ℝ)), ?_, ?_⟩
  · exact one_le_mul_of_one_le_of_one_le hM
      (Real.one_le_exp (mul_nonneg (le_max_right _ _) b.coe_nonneg))
  · intro s hs
    apply (hbound s).trans
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_right (le_max_left _ _) s.coe_nonneg).trans
      (mul_le_mul_of_nonneg_left (by exact_mod_cast hs) (le_max_right _ _))

theorem continuousAt_zero (T : C0Semigroup 𝕜 X) (x : X) :
    ContinuousAt (fun t : ℝ≥0 => T.operators t x) 0 := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhdsWithin_nhds.mp (T.strong_zero x) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  by_cases ht0 : t = 0
  · subst t; simpa using hε
  · have hp : 0 < (t : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ht0)
    simpa only [Real.toNNReal_coe, T.zero_apply] using
      hd (show (t : ℝ) ∈ Ioi 0 from hp) (by simpa [NNReal.dist_eq] using ht)

/-- The operator bound controls both the left and the right time increments. -/
theorem continuous_orbit (T : C0Semigroup 𝕜 X) (x : X) :
    Continuous (fun t : ℝ≥0 => T.operators t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := T.bounded_on_interval (t + 1)
  have hCp : 0 < C := by linarith
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp (T.continuousAt_zero x)
    (ε / C) (div_pos hε hCp)
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro s hs
  have hst : dist s t < δ := lt_of_lt_of_le hs (min_le_left _ _)
  have hs1 : dist s t < 1 := lt_of_lt_of_le hs (min_le_right _ _)
  have hsb : s ≤ t + 1 := by
    rw [NNReal.dist_eq, abs_lt] at hs1
    exact_mod_cast (by linarith [hs1.2] : (s : ℝ) ≤ (t : ℝ) + 1)
  by_cases hts : t ≤ s
  · have heq : T.operators s x - T.operators t x =
        T.operators t (T.operators (s - t) x - x) := by
      rw [map_sub, ← T.add_apply, add_tsub_cancel_of_le hts]
    have hd' : ‖T.operators (s - t) x - x‖ < ε / C := by
      have hdist : dist (s - t) 0 = dist s t := by
        simp [NNReal.dist_eq, NNReal.coe_sub hts]
      have := hd (hdist.symm ▸ hst)
      simpa only [T.zero_apply, dist_eq_norm] using this
    rw [dist_eq_norm, heq]
    calc
      _ ≤ ‖T.operators t‖ * ‖T.operators (s - t) x - x‖ := (T.operators t).le_opNorm _
      _ ≤ C * ‖T.operators (s - t) x - x‖ :=
        mul_le_mul_of_nonneg_right (hbound t (le_add_of_nonneg_right zero_le_one)) (norm_nonneg _)
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hd' hCp
      _ = ε := mul_div_cancel₀ ε hCp.ne'
  · have hst' : s ≤ t := le_of_not_ge hts
    have heq : T.operators t x - T.operators s x =
        T.operators s (T.operators (t - s) x - x) := by
      rw [map_sub, ← T.add_apply, add_tsub_cancel_of_le hst']
    have hd' : ‖T.operators (t - s) x - x‖ < ε / C := by
      have hdist : dist (t - s) 0 = dist s t := by
        rw [dist_comm s t]
        simp [NNReal.dist_eq, NNReal.coe_sub hst']
      have := hd (hdist.symm ▸ hst)
      simpa only [T.zero_apply, dist_eq_norm] using this
    rw [dist_comm, dist_eq_norm, heq]
    calc
      _ ≤ ‖T.operators s‖ * ‖T.operators (t - s) x - x‖ := (T.operators s).le_opNorm _
      _ ≤ C * ‖T.operators (t - s) x - x‖ :=
        mul_le_mul_of_nonneg_right (hbound s hsb) (norm_nonneg _)
      _ < C * (ε / C) := mul_lt_mul_of_pos_left hd' hCp
      _ = ε := mul_div_cancel₀ ε hCp.ne'

theorem continuous_real_orbit (T : C0Semigroup 𝕜 X) (x : X) :
    Continuous (fun t : ℝ => T.operators t.toNNReal x) :=
  (T.continuous_orbit x).comp continuous_real_toNNReal

/-- The real-time quotient agrees with the scalar-linear generator quotient. -/
theorem differenceQuotient_real (T : C0Semigroup 𝕜 X) (h : ℝ) (x : X) :
    differenceQuotient T h x = h⁻¹ • (T.operators h.toNNReal x - x) := by
  change (algebraMap ℝ 𝕜 h)⁻¹ • (T.operators h.toNNReal x - x) =
    h⁻¹ • (T.operators h.toNNReal x - x)
  rw [← map_inv₀]
  rfl

/-- Only the right generator limit is used at this stage. -/
theorem hasDerivWithinAt_orbit_right (T : C0Semigroup 𝕜 X)
    (x : (generator T).domain) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => T.operators s.toNNReal x)
      (T.operators t.toNNReal (generator T x)) (Ioi t) t := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  have hsub : Tendsto (fun s : ℝ => s - t) (𝓝[>] t) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · convert! ((tendsto_id.mono_left nhdsWithin_le_nhds :
        Tendsto (fun s : ℝ => s) (𝓝[>] t) (𝓝 t)).sub_const t) using 1; simp
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.mpr (show t < s from hs)
  have hlim := (T.hasGeneratorLimit_map t.toNNReal (generator_has_limit T x)).comp hsub
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  change differenceQuotient T (s - t) (T.operators t.toNNReal x) = _
  rw [T.differenceQuotient_real]
  rw [slope_def_module]
  congr 1
  rw [← T.add_apply]
  congr 3
  apply NNReal.coe_injective
  rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.mpr hs.le), Real.coe_toNNReal _ ht,
    Real.coe_toNNReal _ (ht.trans hs.le)]
  ring

/-- Integrating the right derivative already gives the full orbit identity. -/
theorem orbit_integral_identity (T : C0Semigroup 𝕜 X) (x : (generator T).domain)
    (t : ℝ≥0) :
    T.operators t x - (x : X) =
      ∫ s in (0 : ℝ)..(t : ℝ), T.operators s.toNNReal (generator T x) := by
  have heq := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.coe_nonneg
    (T.continuous_real_orbit x).continuousOn
    (fun s hs => T.hasDerivWithinAt_orbit_right x s hs.1.le)
    ((T.continuous_real_orbit (generator T x)).intervalIntegrable _ _)
  simpa only [Real.toNNReal_coe, Real.toNNReal_zero, T.zero_apply] using heq.symm

/-- The integral formula upgrades right differentiability to differentiability
within the whole nonnegative time axis, including its initial endpoint. -/
theorem hasDerivWithinAt_orbit (T : C0Semigroup 𝕜 X) (x : (generator T).domain)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s : ℝ => T.operators s.toNNReal x)
      (T.operators t.toNNReal (generator T x)) (Ici 0) t := by
  have hc := T.continuous_real_orbit (generator T x)
  have hd := (intervalIntegral.integral_hasDerivAt_right
    (hc.intervalIntegrable 0 t) hc.aestronglyMeasurable.stronglyMeasurableAtFilter
      hc.continuousAt).const_add (x : X)
  apply hd.hasDerivWithinAt.congr
  · intro s hs
    have hid := T.orbit_integral_identity x s.toNNReal
    rw [Real.coe_toNNReal _ hs] at hid
    simpa only [add_comm] using (eq_add_of_sub_eq hid)
  · have hid := T.orbit_integral_identity x t.toNNReal
    rw [Real.coe_toNNReal _ ht] at hid
    simpa only [add_comm] using (eq_add_of_sub_eq hid)

/-- Integration along an orbit is a bounded scalar-linear operator for each
finite time. Its construction uses strong continuity, not norm continuity of T. -/
def integratedOperator (T : C0Semigroup 𝕜 X) (t : ℝ≥0) : X →L[𝕜] X := by
  let L : X →ₗ[𝕜] X :=
    { toFun := fun x => ∫ s in (0 : ℝ)..(t : ℝ), T.operators s.toNNReal x
      map_add' := by
        intro x y
        simp only [map_add]
        exact intervalIntegral.integral_add
          ((T.continuous_real_orbit x).intervalIntegrable _ _)
          ((T.continuous_real_orbit y).intervalIntegrable _ _)
      map_smul' := by
        intro c x
        simp only [map_smul, RingHom.id_apply]
        exact intervalIntegral.integral_smul c (fun s => T.operators s.toNNReal x) }
  apply L.mkContinuousOfExistsBound
  obtain ⟨C, hC, hbound⟩ := T.bounded_on_interval t
  refine ⟨C * (t : ℝ), fun x => ?_⟩
  change ‖∫ s in (0 : ℝ)..(t : ℝ), T.operators s.toNNReal x‖ ≤ _
  calc
    _ ≤ (C * ‖x‖) * |(t : ℝ) - 0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const (fun s hs => by
        rw [uIoc_of_le t.coe_nonneg] at hs
        exact ((T.operators s.toNNReal).le_opNorm x).trans
          (mul_le_mul_of_nonneg_right (hbound _ (by
            simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2)) (norm_nonneg _)))
    _ = C * (t : ℝ) * ‖x‖ := by rw [sub_zero, abs_of_nonneg t.coe_nonneg]; ring

@[simp] theorem integratedOperator_apply (T : C0Semigroup 𝕜 X) (t : ℝ≥0) (x : X) :
    T.integratedOperator t x = ∫ s in (0 : ℝ)..(t : ℝ), T.operators s.toNNReal x := rfl

/-- The primitive has a genuine real derivative, since the orbit was extended
continuously to negative times by its initial value. -/
theorem hasDerivAt_integral (T : C0Semigroup 𝕜 X) (x : X) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, T.operators s.toNNReal x)
      (T.operators t.toNNReal x) t := by
  have hc := T.continuous_real_orbit x
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- A characterization of the exact generator graph by bounded integral
identities. This gives a closed-set proof without choosing approximating sequences. -/
theorem hasGeneratorLimit_iff_integrated (T : C0Semigroup 𝕜 X) (x y : X) :
    HasGeneratorLimit T x y ↔
      ∀ t : ℝ≥0, T.operators t x - x = T.integratedOperator t y := by
  constructor
  · intro h t
    have hx : x ∈ (generator T).domain := ⟨y, h⟩
    have hAx : generator T ⟨x, hx⟩ = y :=
      generator_limit_unique T _ _ _ (generator_has_limit T ⟨x, hx⟩) h
    simpa only [hAx, integratedOperator_apply] using T.orbit_integral_identity ⟨x, hx⟩ t
  · intro h
    have hd := (T.hasDerivAt_integral y 0).tendsto_slope_zero_right
    change Tendsto (fun h => differenceQuotient T h x) (𝓝[>] 0) (𝓝 y)
    apply (show Tendsto (fun h : ℝ => h⁻¹ •
        ((∫ s in (0 : ℝ)..h, T.operators s.toNNReal y) - 0))
        (𝓝[>] 0) (𝓝 y) from by simpa using hd).congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [T.differenceQuotient_real, sub_zero]
    have hid := h r.toNNReal
    rw [integratedOperator_apply, Real.coe_toNNReal _ (le_of_lt hr)] at hid
    rw [hid]

theorem generator_graph_closed (T : C0Semigroup 𝕜 X) :
    Unbounded.IsClosed (generator T) := by
  change _root_.IsClosed ((generator T).graph : Set (X × X))
  have hset : ((generator T).graph : Set (X × X)) =
      ⋂ t : ℝ≥0, {z : X × X | T.operators t z.1 - z.1 = T.integratedOperator t z.2} := by
    ext ⟨x, y⟩
    change (x, y) ∈ (C0SemigroupSpec.generatorValue T).graph ↔ _
    rw [mem_generator_graph_iff]
    change HasGeneratorLimit T x y ↔ _
    rw [T.hasGeneratorLimit_iff_integrated]
    simp
  rw [hset]
  apply isClosed_iInter
  intro t
  exact isClosed_eq ((T.operators t).continuous.comp continuous_fst |>.sub continuous_fst)
    ((T.integratedOperator t).continuous.comp continuous_snd)

/-- Translating an integrated orbit exposes its two boundary pieces. -/
theorem operators_integratedOperator (T : C0Semigroup 𝕜 X) (h t : ℝ≥0) (x : X) :
    T.operators h (T.integratedOperator t x) =
      (∫ s in (0 : ℝ)..((t : ℝ) + h), T.operators s.toNNReal x) -
        ∫ s in (0 : ℝ)..(h : ℝ), T.operators s.toNNReal x := by
  rw [T.integratedOperator_apply]
  calc
    _ = ∫ s in (0 : ℝ)..(t : ℝ), T.operators h (T.operators s.toNNReal x) :=
      ((T.operators h).intervalIntegral_comp_comm
        ((T.continuous_real_orbit x).intervalIntegrable _ _)).symm
    _ = ∫ s in (0 : ℝ)..(t : ℝ), T.operators (s + (h : ℝ)).toNNReal x := by
      apply intervalIntegral.integral_congr
      intro s hs
      rw [uIcc_of_le t.coe_nonneg] at hs
      change T.operators h (T.operators s.toNNReal x) = T.operators (s + (h : ℝ)).toNNReal x
      rw [← T.add_apply]
      congr 2
      apply NNReal.coe_injective
      rw [NNReal.coe_add, Real.coe_toNNReal _ hs.1,
        Real.coe_toNNReal _ (add_nonneg hs.1 h.coe_nonneg)]
      ring
    _ = ∫ s in (h : ℝ)..((t : ℝ) + h), T.operators s.toNNReal x := by
      simpa only [zero_add] using
        intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := (t : ℝ))
          (fun s : ℝ => T.operators s.toNNReal x) (h : ℝ)
    _ = _ := (intervalIntegral.integral_interval_sub_left
      ((T.continuous_real_orbit x).intervalIntegrable _ _)
      ((T.continuous_real_orbit x).intervalIntegrable _ _)).symm

/-- Every unnormalized orbit average is in the exact derivative domain. -/
theorem integratedOperator_hasGeneratorLimit (T : C0Semigroup 𝕜 X) (t : ℝ≥0) (x : X) :
    HasGeneratorLimit T (T.integratedOperator t x) (T.operators t x - x) := by
  have ht := (T.hasDerivAt_integral x ((t : ℝ) + 0)).comp_const_add (t : ℝ) 0
  have hd := ht.sub (T.hasDerivAt_integral x 0)
  have hlim := hd.tendsto_slope_zero_right
  change Tendsto (fun h => differenceQuotient T h (T.integratedOperator t x))
    (𝓝[>] 0) (𝓝 (T.operators t x - x))
  apply (show Tendsto (fun h : ℝ => h⁻¹ •
      (((∫ s in (0 : ℝ)..((t : ℝ) + h), T.operators s.toNNReal x) -
          ∫ s in (0 : ℝ)..h, T.operators s.toNNReal x) - T.integratedOperator t x))
      (𝓝[>] 0) (𝓝 (T.operators t x - x)) from by
        simpa only [Pi.sub_apply, zero_add, add_zero, Real.toNNReal_coe, Real.toNNReal_zero,
          T.zero_apply, intervalIntegral.integral_same, sub_zero, integratedOperator_apply] using hlim).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [T.differenceQuotient_real, T.operators_integratedOperator]
  rw [Real.coe_toNNReal _ (le_of_lt hr)]

theorem integratedOperator_mem_domain (T : C0Semigroup 𝕜 X) (t : ℝ≥0) (x : X) :
    T.integratedOperator t x ∈ (generator T).domain :=
  ⟨_, T.integratedOperator_hasGeneratorLimit t x⟩

/-- Normalized orbit integrals converge to the initial vector. -/
theorem tendsto_orbit_average (T : C0Semigroup 𝕜 X) (x : X) :
    Tendsto (fun h : ℝ => h⁻¹ • T.integratedOperator h.toNNReal x)
      (𝓝[>] 0) (𝓝 x) := by
  have hlim := (T.hasDerivAt_integral x 0).tendsto_slope_zero_right
  apply (show Tendsto (fun h : ℝ => h⁻¹ •
      ∫ s in (0 : ℝ)..h, T.operators s.toNNReal x) (𝓝[>] 0) (𝓝 x) from by
        simpa only [zero_add, Real.toNNReal_zero, T.zero_apply,
          intervalIntegral.integral_same, sub_zero] using hlim).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  rw [T.integratedOperator_apply, Real.coe_toNNReal _ (le_of_lt hr)]

theorem generator_domain_dense (T : C0Semigroup 𝕜 X) :
    Unbounded.DenselyDefined (generator T) := by
  intro x
  apply mem_closure_of_tendsto (T.tendsto_orbit_average x)
  apply Eventually.of_forall
  intro r
  change (algebraMap ℝ 𝕜 r⁻¹) • T.integratedOperator r.toNNReal x ∈ (generator T).domain
  exact (generator T).domain.smul_mem _ (T.integratedOperator_mem_domain r.toNNReal x)

end C0Semigroup

namespace SemigroupGrowthAndGenerator

theorem strong_continuity : SemigroupGrowthSpec.StrongContinuity (𝕜 := 𝕜) (X := X) := by
  intro T x
  exact T.continuous_orbit x

theorem exponential_growth : SemigroupGrowthSpec.ExponentialGrowth (𝕜 := 𝕜) (X := X) := by
  intro T
  exact T.exponential_bound

theorem domain_invariant : SemigroupGrowthSpec.DomainInvariant (𝕜 := 𝕜) (X := X) := by
  intro T t x hx
  obtain ⟨y, hy⟩ := (mem_generator_domain_iff T x).mp hx
  exact (mem_generator_domain_iff T _).mpr ⟨_, T.hasGeneratorLimit_map t hy⟩

theorem generator_commutes : SemigroupGrowthSpec.GeneratorCommutes (𝕜 := 𝕜) (X := X) := by
  intro T t x hx
  exact generator_limit_unique T _ _ _ (generator_has_limit T ⟨_, hx⟩)
    (T.hasGeneratorLimit_map t (generator_has_limit T x))

theorem orbit_derivative : SemigroupGrowthSpec.OrbitDerivative (𝕜 := 𝕜) (X := X) := by
  intro T x t ht
  exact T.hasDerivWithinAt_orbit x t ht

theorem integrated_derivative : SemigroupGrowthSpec.IntegratedDerivative (𝕜 := 𝕜) (X := X) := by
  intro T x t
  exact T.orbit_integral_identity x t

theorem generator_dense : SemigroupGrowthSpec.GeneratorDense (𝕜 := 𝕜) (X := X) := by
  intro T
  exact T.generator_domain_dense

theorem generator_closed : SemigroupGrowthSpec.GeneratorClosed (𝕜 := 𝕜) (X := X) := by
  intro T
  exact T.generator_graph_closed

theorem graph_continuity : SemigroupGrowthSpec.GraphContinuity (𝕜 := 𝕜) (X := X) := by
  intro T x
  let u : ℝ≥0 → Unbounded.GraphDomain (SemigroupGrowthSpec.A T) := fun t =>
    (⟨T.operators t x, domain_invariant T t x x.2⟩ : (SemigroupGrowthSpec.A T).domain)
  have hu : ∀ t, (Unbounded.GraphDomain.toDomain _ (u t) : X) = T.operators t x :=
    fun _ => rfl
  have hAu : ∀ t, SemigroupGrowthSpec.A T (Unbounded.GraphDomain.toDomain _ (u t)) =
      T.operators t (SemigroupGrowthSpec.A T x) := fun t => generator_commutes T t x _
  refine ⟨u, hu, hAu, ?_⟩
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp (T.continuous_orbit x).continuousAt
    (ε / 2) (by positivity)
  obtain ⟨η, hη, he⟩ := Metric.continuousAt_iff.mp
    (T.continuous_orbit (SemigroupGrowthSpec.A T x)).continuousAt (ε / 2) (by positivity)
  refine ⟨min δ η, lt_min hδ hη, ?_⟩
  intro s hs
  have h1 := hd (lt_of_lt_of_le hs (min_le_left _ _))
  have h2 := he (lt_of_lt_of_le hs (min_le_right _ _))
  rw [dist_eq_norm, Unbounded.GraphDomain.norm_eq]
  change ‖(Unbounded.GraphDomain.toDomain _ (u s) : X) -
    (Unbounded.GraphDomain.toDomain _ (u t) : X)‖ +
    ‖SemigroupGrowthSpec.A T (Unbounded.GraphDomain.toDomain _ (u s) -
      Unbounded.GraphDomain.toDomain _ (u t))‖ < ε
  rw [(SemigroupGrowthSpec.A T).map_sub, hu, hu, hAu, hAu]
  rw [dist_eq_norm] at h1 h2
  linarith

end SemigroupGrowthAndGenerator
end ExpandedFA.Semigroups
