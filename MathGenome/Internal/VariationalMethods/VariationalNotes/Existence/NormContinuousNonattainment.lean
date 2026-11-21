import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.NormContinuousNonattainment
import MathGenome.Internal.VariationalMethods.VariationalNotes.Existence.ReflexiveWeakCompactness
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open Set Filter
open scoped Topology InnerProductSpace
namespace VariationalNotes.Existence.NormContinuousNonattainment

abbrev Space := Specs.Space

def positiveIndex : Specs.positiveIndexType := Specs.positiveIndex
def weight : Specs.weightType := Specs.weight
def quadratic : Specs.quadraticType := Specs.quadratic
def objective : Specs.objectiveType := Specs.objective
def feasible : Specs.feasibleType := Specs.feasible
def unitVector : Specs.unitVectorType := Specs.unitVector

theorem index_shift : Specs.index_shift := by
  intro n
  rfl

lemma weight_pos (n : ℕ) : 0 < weight n := by
  dsimp [weight, Specs.weight]
  positivity

lemma weight_le_one (n : ℕ) : weight n ≤ 1 := by
  dsimp [weight, Specs.weight]
  apply (div_le_one (by positivity)).2
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

lemma summable_squares (x : Space) : Summable (fun n => (x n) ^ 2) := by
  simpa [RCLike.inner_apply, pow_two] using
    (lp.summable_inner (𝕜 := ℝ) x x)

lemma sum_squares (x : Space) : ∑' n, (x n) ^ 2 = ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp [pow_two]

lemma series_summable (x : Space) :
    Summable (fun n : ℕ => (x n) ^ 2 / ((n : ℝ) + 1)) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ (summable_squares x)
  intro n
  apply div_le_self (sq_nonneg _)
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

/-- Multiplication by the bounded diagonal with entries 1/(n+1). -/
def diagonalLinear : Space →ₗ[ℝ] Space where
  toFun x := ⟨fun n => weight n * x n, (lp.memℓp x).mono' (fun n => by
    rw [norm_mul, Real.norm_of_nonneg (weight_pos n).le]
    exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one n))⟩
  map_add' x y := by ext n; change weight n * (x n + y n) = weight n * x n + weight n * y n; ring
  map_smul' c x := by ext n; simp [mul_left_comm]

lemma diagonalLinear_bound (x : Space) : ‖diagonalLinear x‖ ≤ ‖x‖ := by
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro n
  change ‖weight n * x n‖ ≤ ‖x n‖
  rw [norm_mul, Real.norm_of_nonneg (weight_pos n).le]
  exact mul_le_of_le_one_left (norm_nonneg _) (weight_le_one n)

def diagonal : Space →L[ℝ] Space :=
  diagonalLinear.mkContinuous 1 (fun x => by simpa using diagonalLinear_bound x)

lemma diagonal_apply (x : Space) (n : ℕ) : diagonal x n = weight n * x n := rfl

lemma quadratic_inner (x : Space) : quadratic x = inner ℝ x (diagonal x) := by
  change (∑' n, x n ^ 2 / ((n : ℝ) + 1)) = _
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro n
  simp only [diagonal_apply, RCLike.inner_apply, conj_trivial, weight, Specs.weight]
  ring


theorem positive_index_formula : Specs.positive_index_formula := by
  intro x
  rw [← Specs.positiveIndex.tsum_eq]
  change (∑' n, x n ^ 2 / ((n : ℝ) + 1)) = _
  apply tsum_congr
  intro n
  simp only [Equiv.symm_apply_apply]
  congr 2
  change (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ)
  simp

theorem series_and_diagonal : Specs.series_and_diagonal := by
  refine ⟨series_summable, diagonal, ?_, diagonal_apply, quadratic_inner⟩
  exact LinearMap.mkContinuous_norm_le _ zero_le_one _

lemma quadratic_nonneg (x : Space) : 0 ≤ quadratic x := by
  exact tsum_nonneg (fun n => by positivity)

lemma quadratic_le (x : Space) : quadratic x ≤ ‖x‖ ^ 2 := by
  rw [← sum_squares]
  apply (series_summable x).tsum_le_tsum _ (summable_squares x)
  intro n
  apply div_le_self (sq_nonneg _)
  have := Nat.cast_nonneg (α := ℝ) n
  linarith

lemma quadratic_eq_zero (x : Space) : quadratic x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    apply lp.ext
    funext n
    have h := (series_summable x).le_tsum n (fun m _ => by positivity)
    change x n ^ 2 / ((n : ℝ) + 1) ≤ quadratic x at h
    rw [hx] at h
    have he : x n ^ 2 / ((n : ℝ) + 1) = 0 := le_antisymm h (by positivity)
    have hd : (n : ℝ) + 1 ≠ 0 := by positivity
    have := (div_eq_zero_iff).mp he
    simpa using (sq_eq_zero_iff.mp (this.resolve_right hd))
  · rintro rfl
    simp [quadratic, Specs.quadratic]

theorem quadratic_bounds : Specs.quadratic_bounds := by
  intro x
  exact ⟨quadratic_nonneg x, quadratic_le x, quadratic_eq_zero x⟩

theorem norm_continuous : Specs.norm_continuous := by
  have hq : Continuous quadratic := by
    have he : quadratic = (fun x : Space => inner ℝ x (diagonal x)) :=
      funext quadratic_inner
    rw [he]
    exact continuous_id.inner diagonal.continuous
  change Continuous (fun x : Space => 1 - ‖x‖ ^ 2 + quadratic x)
  exact (continuous_const.sub (continuous_norm.pow 2)).add hq

lemma objective_zero : objective 0 = 1 := by
  simp [objective, Specs.objective, Specs.quadratic]

theorem positive_on_ball : Specs.positive_on_ball := by
  intro x hx
  change ‖x‖ ≤ 1 at hx
  change 0 < 1 - ‖x‖ ^ 2 + quadratic x
  by_cases h : x = 0
  · subst x
    simp [quadratic, Specs.quadratic]
  · have hq : 0 < quadratic x := lt_of_le_of_ne (quadratic_nonneg x)
      (Ne.symm (fun hq => h ((quadratic_eq_zero x).mp hq)))
    have hn := norm_nonneg x
    nlinarith

lemma norm_unitVector (n : ℕ) : ‖unitVector n‖ = 1 := by
  simp [unitVector, Specs.unitVector]

lemma quadratic_unitVector (n : ℕ) : quadratic (unitVector n) = weight n := by
  change (∑' m, (lp.single (E := fun _ : ℕ => ℝ) 2 n 1 m) ^ 2 / ((m : ℝ) + 1)) = _
  rw [tsum_eq_single n]
  · simp [weight, Specs.weight]
  · intro m hm
    simp [lp.single_apply, Pi.single_eq_of_ne hm]

theorem unit_values : Specs.unit_values := by
  intro n
  refine ⟨?_, ?_⟩
  · change ‖unitVector n‖ ≤ 1
    rw [norm_unitVector]
  · change 1 - ‖unitVector n‖ ^ 2 + quadratic (unitVector n) = _
    rw [norm_unitVector, quadratic_unitVector]
    simp [weight, Specs.weight]

theorem zero_and_value_limit : Specs.zero_and_value_limit := by
  refine ⟨objective_zero, ?_⟩
  change Tendsto (fun n => objective (unitVector n)) atTop (𝓝 0)
  simp_rw [show ∀ n, objective (unitVector n) = 1 / ((n : ℝ) + 1) from
    fun n => (unit_values n).2]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

theorem infimum_zero : Specs.infimum_zero := by
  have hglb : IsGLB (objective '' feasible) 0 := by
    refine ⟨?_, ?_⟩
    · rintro a ⟨x, hx, rfl⟩
      exact (positive_on_ball x hx).le
    · intro a ha
      apply ge_of_tendsto zero_and_value_limit.2
      exact Eventually.of_forall (fun n => ha ⟨unitVector n, (unit_values n).1, rfl⟩)
  exact ⟨hglb, hglb.csInf_eq ⟨objective (unitVector 0),
    unitVector 0, (unit_values 0).1, rfl⟩⟩

theorem no_minimum : Specs.no_minimum := by
  rintro ⟨x, hx, hxmin⟩
  have hle : objective x ≤ 0 := infimum_zero.1.2 (by
    rintro a ⟨y, hy, rfl⟩
    exact hxmin y hy)
  exact (not_le_of_gt (positive_on_ball x hx)) hle


/-- Square summability makes each coordinate of a fixed vector tend to zero. -/
lemma coordinate_limit (x : Space) : Tendsto (fun n => x n) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp
    (summable_squares x).tendsto_atTop_zero
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using hs

theorem weak_unit_limit : Specs.weak_unit_limit := by
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto
    (topDualPairing ℝ Space).flip (separatingDual_iff_injective.mp inferInstance)).2
  intro f
  change Tendsto (fun n => f (unitVector n)) atTop (𝓝 (f 0))
  rw [map_zero]
  let x : Space := (InnerProductSpace.toDual ℝ Space).symm f
  have hf (n : ℕ) : f (unitVector n) = x n := by
    rw [← InnerProductSpace.toDual_symm_apply]
    change inner ℝ x (lp.single 2 n 1) = x n
    rw [lp.inner_single_right]
    simp
  simp_rw [hf]
  exact coordinate_limit x

/-- Real Hilbert spaces are reflexive for the canonical evaluation map.
We establish the exact upstream surjectivity interface using Riesz twice. -/
lemma space_reflexive : VariationalNotes.Existence.Specs.IsReflexive Space := by
  intro F
  let R := (InnerProductSpace.toDual ℝ Space).toContinuousLinearEquiv
  let g : Space →L[ℝ] ℝ := F.comp R.toContinuousLinearMap
  let x : Space := (InnerProductSpace.toDual ℝ Space).symm g
  refine ⟨x, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  change f x = F f
  let y : Space := (InnerProductSpace.toDual ℝ Space).symm f
  calc
    f x = inner ℝ y x := (InnerProductSpace.toDual_symm_apply).symm
    _ = inner ℝ x y := real_inner_comm _ _
    _ = g y := InnerProductSpace.toDual_symm_apply
    _ = F f := by
      change F ((InnerProductSpace.toDual ℝ Space) ((InnerProductSpace.toDual ℝ Space).symm f)) = F f
      simp

lemma feasible_eq_closedBall : feasible = Metric.closedBall (0 : Space) 1 := by
  ext x
  simp [feasible, Specs.feasible, Metric.mem_closedBall, dist_zero_right]

theorem ball_geometry : Specs.ball_geometry := by
  change IsClosed feasible ∧ Bornology.IsBounded feasible ∧
    IsCompact ((toWeakSpace ℝ Space) '' feasible)
  rw [feasible_eq_closedBall]
  exact ⟨Metric.isClosed_closedBall, Metric.isBounded_closedBall,
    VariationalNotes.Existence.reflexive_closedBall_isWeaklyCompact Space space_reflexive 0 1⟩

theorem not_weak_lowerSemicontinuous : Specs.not_weak_lowerSemicontinuous := by
  intro h
  have hz : (0 : Space) ∈ feasible := by simp [feasible, Specs.feasible]
  have he := h (toWeakSpace ℝ Space 0) ⟨0, hz, rfl⟩ (1 / 2 : ℝ) (by
    change (1 / 2 : ℝ) < objective 0
    rw [objective_zero]
    norm_num)
  have ht : Tendsto (fun n => toWeakSpace ℝ Space (unitVector n)) atTop
      (𝓝[(toWeakSpace ℝ Space) '' feasible] (toWeakSpace ℝ Space 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨weak_unit_limit, Eventually.of_forall (fun n =>
      ⟨unitVector n, (unit_values n).1, rfl⟩)⟩
  have hlarge := ht.eventually he
  have hsmall := zero_and_value_limit.2.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨n, hn, hn'⟩ := (hlarge.and hsmall).exists
  change (1 / 2 : ℝ) < objective (unitVector n) at hn
  change objective (unitVector n) < (1 / 2 : ℝ) at hn'
  linarith

end VariationalNotes.Existence.NormContinuousNonattainment
