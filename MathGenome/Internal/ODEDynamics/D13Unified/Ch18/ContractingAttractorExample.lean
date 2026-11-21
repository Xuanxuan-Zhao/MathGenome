import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch18.ContractingAttractorExample
import MathGenome.Internal.ODEDynamics.D13Unified.Ch18.TrappingAttractor
import MathGenome.Internal.ODEDynamics.D13Unified.Ch18.GrowthDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch17.ChaosDefinitions
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable section
open Set Filter
open scoped Topology
namespace D13Unified.Ch18.ContractingAttractorExample
open Ch18.AttractorDefinition Ch18.TrappingLimit Ch18.GrowthDefinitions

theorem iterate_formula (n : ℕ) (x : ℝ) : F^[n] x = (1 / 2 : ℝ)^n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [F, pow_succ]
    ring

private lemma continuous_F : Continuous F := continuous_id.div_const 2

private lemma powers_tendsto : Tendsto (fun n : ℕ => (1 / 2 : ℝ)^n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private lemma powers_le_one (n : ℕ) : (1 / 2 : ℝ)^n ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

theorem trapping : IsCompact K ∧ K.Nonempty ∧ F '' K ⊆ interior K := by
  refine ⟨isCompact_Icc, ⟨0, by norm_num [K]⟩, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  rw [K, interior_Icc]
  rcases hx with ⟨hlo, hhi⟩
  change -1 < x / 2 ∧ x / 2 < 1
  constructor <;> linarith

theorem trapping_limit : trappingLimit F K = {0} := by
  change (⋂ n : ℕ, F^[n] '' K) = {0}
  apply Set.Subset.antisymm
  · intro x hx
    have hb : ∀ n : ℕ, |x| ≤ (1 / 2 : ℝ)^n := by
      intro n
      obtain ⟨y, hy, rfl⟩ := mem_iInter.mp hx n
      rw [iterate_formula, abs_mul, abs_of_nonneg (pow_nonneg (by norm_num) _)]
      have hyabs : |y| ≤ 1 := abs_le.mpr hy
      simpa using mul_le_mul_of_nonneg_left hyabs (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) n)
    exact mem_singleton_iff.mpr (abs_eq_zero.mp (le_antisymm (ge_of_tendsto powers_tendsto (Eventually.of_forall hb)) (abs_nonneg x)))
  · rintro x (rfl : x = 0)
    apply mem_iInter.mpr
    intro n
    refine ⟨0, by norm_num [K], ?_⟩
    simp [iterate_formula]

theorem stable_attractor : StableAttractor F {0} := by
  have h := (Ch18.TrappingAttractor.compact_trapping_attractor F K continuous_F
    trapping.1 trapping.2.1 trapping.2.2).1
  simpa only [trapping_limit] using h

theorem basin_univ : basin F {0} = univ := by
  apply eq_univ_of_forall
  intro x
  apply (mem_basin_iff_dist F {0} (singleton_nonempty 0) x).mpr
  simpa [iterate_formula, Metric.infDist_singleton, Real.dist_eq, abs_mul,
    abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) _)] using
    powers_tendsto.mul_const |x|

theorem directional_rate (x : smoothMap.domain) (v : ℝ) (hv : v ≠ 0)
    (n : ℕ) (hn : 0 < n) :
    discreteDirectionalRate smoothMap x v hv n hn = ((-Real.log 2 : ℝ) : EReal) := by
  change Specs.D13Unified.Ch18.GrowthDefinitions.discreteDirectionalRate smoothMap x v hv n hn = _
  rw [discreteDirectionalRate_formula]
  have hd : fderiv ℝ (smoothMap.value^[n]) x =
      (1 / 2 : ℝ)^n • ContinuousLinearMap.id ℝ ℝ := by
    have heq : smoothMap.value^[n] = fun y => (1 / 2 : ℝ)^n • y :=
      funext (iterate_formula n)
    rw [heq]
    exact ((hasFDerivAt_id (x : ℝ)).const_smul ((1 / 2 : ℝ)^n)).fderiv
  rw [hd]
  have hp : 0 < (1 / 2 : ℝ)^n := pow_pos (by norm_num) n
  have hr : ‖((1 / 2 : ℝ)^n • ContinuousLinearMap.id ℝ ℝ) v‖ / ‖v‖ =
      (1 / 2 : ℝ)^n := by
    simp only [smul_apply, ContinuousLinearMap.id_apply,
      norm_smul, Real.norm_eq_abs, abs_of_pos hp]
    exact mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hv)
  rw [hr, logarithmicRate_nonzero _ _ hp.ne']
  congr 1
  rw [Real.log_pow, Real.log_div (by norm_num) (by norm_num), Real.log_one]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  field_simp
  simp

theorem directional_exponent : Specs.D13Unified.Ch18.ContractingAttractorExample.directional_exponentStatement := by
  intro x v hv
  have h : HasDiscreteDirectionalExponent smoothMap x v hv ((-Real.log 2 : ℝ) : EReal) := by
    change Tendsto _ _ _
    simp_rw [directional_rate]
    exact tendsto_const_nhds
  exact ⟨h, (discreteDirectionalExponent_some_iff _ _ _ _ _).mpr h⟩

theorem not_sensitive : ¬ Ch17.ChaosDefinitions.SensitiveDependence F := by
  rw [Ch17.ChaosDefinitions.sensitiveDependence_iff_balls]
  rintro ⟨δ, hδ, h⟩
  obtain ⟨y, hy, n, hn⟩ := h 0 δ hδ
  have hbound : dist (F^[n] 0) (F^[n] y) ≤ dist y 0 := by
    simp only [iterate_formula, mul_zero, Real.dist_eq, zero_sub, abs_neg,
      sub_zero, abs_mul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) _)]
    exact mul_le_of_le_one_left (abs_nonneg y) (powers_le_one n)
  exact (not_lt_of_ge (hbound.trans hy.le)) hn

theorem not_chaotic : ¬ Ch17.ChaosDefinitions.Chaotic F := by
  intro h
  exact not_sensitive h.2.2

end D13Unified.Ch18.ContractingAttractorExample
