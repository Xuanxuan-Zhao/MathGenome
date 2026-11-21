import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.InterpolationNorm
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.Lagrange
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs

noncomputable section
open Polynomial
open scoped BigOperators
namespace NumAnalysis206.Approximation

abbrev lebesgueFunction := @Specs.NumAnalysis206.Approximation.lebesgueFunction

def lebesgueConstant {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b) : ℝ :=
  Specs.NumAnalysis206.Approximation.lebesgueConstantValue x

def interpolationOperator {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b) :
    IntervalContinuous a b →L[ℝ] IntervalContinuous a b :=
  Specs.NumAnalysis206.Approximation.interpolationOperatorValue x

variable {a b : ℝ} {n : ℕ} (x : Fin (n + 1) → Set.Icc a b)

@[simp] theorem interpolationOperator_apply (f : IntervalContinuous a b) (t : Set.Icc a b) :
    interpolationOperator x f t = ∑ i, f (x i) * (cardinal Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ) := by
  simp [interpolationOperator, Specs.NumAnalysis206.Approximation.interpolationOperatorValue,
    ContinuousMap.sum_apply, cardinal]

theorem interpolation_formula (f : IntervalContinuous a b) (t : Set.Icc a b) :
    interpolationOperator x f t =
      (interpolant Finset.univ (fun j => (x j : ℝ)) (fun j => f (x j))).eval (t : ℝ) := by
  simp [interpolationOperator_apply, interpolant, Polynomial.eval_finsetSum]

private theorem real_nodes_inj (hx : Function.Injective x) :
    Set.InjOn (fun j => (x j : ℝ)) (Finset.univ : Finset (Fin (n+1))) := by
  intro i _ j _ h
  exact hx (Subtype.ext h)

theorem interpolation_nodes (hx : Function.Injective x) (f : IntervalContinuous a b)
    (i : Fin (n + 1)) : interpolationOperator x f (x i) = f (x i) := by
  rw [interpolation_formula]
  exact interpolant_eval _ _ _ (real_nodes_inj x hx) i (Finset.mem_univ i)

theorem interpolation_range (hx : Function.Injective x) (f : IntervalContinuous a b) :
    interpolationOperator x f ∈ polynomialSpace a b n := by
  let p := interpolant Finset.univ (fun j => (x j : ℝ)) (fun j => f (x j))
  refine ⟨p, ?_, ?_⟩
  · apply Polynomial.mem_degreeLE.mpr
    apply (degree_le_iff_lt_card (Finset.univ : Finset (Fin (n+1))) n (by simp) p).2
    exact interpolant_degree_lt _ _ _ (real_nodes_inj x hx)
  · ext t
    exact (interpolation_formula x f t).symm

theorem interpolation_reproduces (hx : Function.Injective x) (p : ℝ[X])
    (hp : p.degree ≤ (n : WithBot ℕ)) :
    interpolationOperator x (p.toContinuousMapOn (Set.Icc a b)) =
      p.toContinuousMapOn (Set.Icc a b) := by
  have heq := (interpolant_unique Finset.univ (fun j => (x j : ℝ))
    (fun j => p.eval (x j)) n (real_nodes_inj x hx) (by simp) p).1 ⟨hp, by simp⟩
  ext t
  rw [interpolation_formula]
  simpa using congrArg (fun q : ℝ[X] => q.eval (t : ℝ)) heq.symm

private theorem lebesgueFunction_nonneg (t : Set.Icc a b) : 0 ≤ lebesgueFunction x t := by
  dsimp [lebesgueFunction, Specs.NumAnalysis206.Approximation.lebesgueFunction]
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem lebesgueFunction_le (t : Set.Icc a b) : lebesgueFunction x t ≤ lebesgueConstant x := by
  exact le_trans (le_abs_self _) ((lebesgueFunction x).norm_coe_le_norm t)

theorem lebesgue_maximum (hab : a < b) : ∃ t : Set.Icc a b,
    lebesgueConstant x = lebesgueFunction x t ∧
    ∀ u : Set.Icc a b, lebesgueFunction x u ≤ lebesgueConstant x := by
  obtain ⟨t, _, ht⟩ := isCompact_univ.exists_isMaxOn
    (show (Set.univ : Set (Set.Icc a b)).Nonempty from ⟨⟨a, le_rfl, hab.le⟩, trivial⟩)
    (lebesgueFunction x).continuous.continuousOn
  refine ⟨t, le_antisymm ?_ ?_, lebesgueFunction_le x⟩
  · apply (lebesgueFunction x).norm_le (lebesgueFunction_nonneg x t) |>.mpr
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg (lebesgueFunction_nonneg x u)]
    exact ht (Set.mem_univ u)
  · exact lebesgueFunction_le x t

/-- The upper operator bound follows pointwise from the triangle inequality. -/
theorem interpolation_bound (f : IntervalContinuous a b) :
    ‖interpolationOperator x f‖ ≤ lebesgueConstant x * ‖f‖ := by
  apply ((interpolationOperator x f).norm_le
    (mul_nonneg (norm_nonneg (lebesgueFunction x)) (norm_nonneg f))).2
  intro t
  rw [interpolationOperator_apply]
  calc
    ‖∑ i, f (x i) * (cardinal Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ)‖
        ≤ ∑ i, ‖f (x i) * (cardinal Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ)‖ :=
      norm_sum_le _ _
    _ = ∑ i, |(cardinal Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ)| * ‖f (x i)‖ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [norm_mul, Real.norm_eq_abs]
      exact mul_comm _ _
    _ ≤ ∑ i, |(cardinal Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ)| * ‖f‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (x i)) (abs_nonneg _)
    _ = lebesgueFunction x t * ‖f‖ := by
      change _ = (∑ i, |(cardinal Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ)|) * ‖f‖
      rw [Finset.sum_mul]
    _ ≤ lebesgueConstant x * ‖f‖ :=
      mul_le_mul_of_nonneg_right (lebesgueFunction_le x t) (norm_nonneg f)

/-- Clamping an interpolating polynomial extends finite data in [-1,1]
without increasing the uniform norm beyond one. -/
private theorem exists_unit_extension (hx : Function.Injective x)
    (d : Fin (n + 1) → ℝ) (hd : ∀ i, |d i| ≤ 1) :
    ∃ f : IntervalContinuous a b, ‖f‖ ≤ 1 ∧ ∀ i, f (x i) = d i := by
  let p := interpolant Finset.univ (fun j => (x j : ℝ)) d
  let f : IntervalContinuous a b :=
    ⟨fun t => max (-1) (min 1 (p.eval (t : ℝ))), by fun_prop⟩
  refine ⟨f, (f.norm_le zero_le_one).2 ?_, ?_⟩
  · intro t
    change |max (-1 : ℝ) (min 1 (p.eval (t : ℝ)))| ≤ 1
    exact abs_le.mpr ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · intro i
    change max (-1 : ℝ) (min 1 (p.eval (x i : ℝ))) = d i
    have hi : p.eval (x i : ℝ) = d i :=
      interpolant_eval _ _ _ (real_nodes_inj x hx) i (Finset.mem_univ i)
    rw [hi, min_eq_right (abs_le.mp (hd i)).2,
      max_eq_right (abs_le.mp (hd i)).1]

/-- Every value of the Lebesgue function is witnessed by a unit-ball input. -/
theorem lebesgueFunction_le_operatorNorm (hx : Function.Injective x) (t : Set.Icc a b) :
    lebesgueFunction x t ≤ ‖interpolationOperator x‖ := by
  let d : Fin (n+1) → ℝ := fun i =>
    if 0 ≤ (cardinal Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ) then 1 else -1
  obtain ⟨f, hf, hnodes⟩ := exists_unit_extension x hx d (by
    intro i
    dsimp [d]
    split_ifs <;> norm_num)
  have hval : interpolationOperator x f t = lebesgueFunction x t := by
    rw [interpolationOperator_apply]
    change (∑ i, f (x i) * (cardinal Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ)) =
      ∑ i, |(cardinal Finset.univ (fun j => (x j : ℝ)) i).eval (t : ℝ)|
    apply Finset.sum_congr rfl
    intro i _
    rw [hnodes]
    dsimp [d]
    split_ifs with hi
    · simp [abs_of_nonneg hi]
    · simp [abs_of_neg (lt_of_not_ge hi)]
  calc
    lebesgueFunction x t ≤ ‖interpolationOperator x f t‖ := by
      rw [hval, Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ ‖interpolationOperator x f‖ := (interpolationOperator x f).norm_coe_le_norm t
    _ ≤ ‖interpolationOperator x‖ := (interpolationOperator x).unit_le_opNorm f hf

theorem interpolation_norm (hab : a < b) (hx : Function.Injective x) :
    ‖interpolationOperator x‖ = lebesgueConstant x := by
  apply le_antisymm
  · exact (interpolationOperator x).opNorm_le_bound (norm_nonneg _) (interpolation_bound x)
  · obtain ⟨t, ht, _⟩ := lebesgue_maximum x hab
    rw [ht]
    exact lebesgueFunction_le_operatorNorm x hx t

set_option backward.isDefEq.respectTransparency false in
/-- Interpolation also takes values in the polynomial subspace with its inherited norm. -/
theorem polynomial_valued_realization (hab : a < b) (hx : Function.Injective x) :
    ∃ J : IntervalContinuous a b →L[ℝ] polynomialSpace a b n,
      (∀ f, (J f : IntervalContinuous a b) = interpolationOperator x f) ∧
      ‖J‖ = lebesgueConstant x := by
  let J := (interpolationOperator x).codRestrict (polynomialSpace a b n)
    (interpolation_range x hx)
  refine ⟨J, fun _ => rfl, ?_⟩
  rw [← interpolation_norm x hab hx]
  apply le_antisymm
  · exact J.opNorm_le_bound (interpolationOperator x).opNorm_nonneg (fun f => (interpolationOperator x).le_opNorm f)
  · exact (interpolationOperator x).opNorm_le_bound J.opNorm_nonneg (fun f => J.le_opNorm f)

end NumAnalysis206.Approximation
