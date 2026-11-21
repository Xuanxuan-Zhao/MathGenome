import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch03.UniformContinuity
import MathGenome.Internal.SingleVariableAnalysis.SingleVariableAnalysis.Ch07.RealPowers
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Lipschitz

/-!
# Lipschitz and Hölder estimates

K03.03.lipschitz, paper.tex:600–609. The metric proof uses continuity of
C t^α at zero, so it includes C = 0 without division by C. This supplies
one radius for every pair in E. It even works for α > 1, though the
source statement is retained with 0 < α ≤ 1.

The rpow bridge identifies every nonnegative distance with the upstream
positive-base construction or its prescribed value zero. The identifications
with LipschitzOnWith and HolderOnWith are proved from their actual distance
and extended-distance definitions. The absolute-value example reuses the
reverse triangle inequality and Mathlib's proof that its two one-sided
slopes at zero prevent ordinary differentiability.
-/
namespace SingleVariableAnalysis
open scoped NNReal ENNReal
universe u v

theorem nonnegative_partialRealPower_eq_rpow (d α : ℝ) (hd : 0 ≤ d) (hα : 0 < α) :
    partialRealPower d α = some (d ^ α) := by
  obtain rfl | hd := hd.eq_or_lt
  · rw [partialRealPower_zero α hα, Real.zero_rpow hα.ne']
  · rw [partialRealPower_positive d hd, realPower_eq_rpow d hd]

theorem holder_estimate_uniformContinuous
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (C α : ℝ)
    (_hC : 0 ≤ C) (hα : 0 < α) (_hα1 : α ≤ 1)
    (hf : ∀ x ∈ E, ∀ y ∈ E, dist (f x) (f y) ≤ C * dist x y ^ α) :
    RelativeUniformContinuous f E := by
  have hc : ContinuousAt (fun t : ℝ => C * t ^ α) 0 :=
    continuousAt_const.mul (Real.continuous_rpow_const hα.le).continuousAt
  have hz : C * (0 : ℝ) ^ α = 0 := by rw [Real.zero_rpow hα.ne', mul_zero]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := Metric.continuousAt_iff.mp hc ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have hd : dist (dist x y) (0 : ℝ) < δ := by
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] using hxy
  have hb' : |C * dist x y ^ α| < ε := by
    simpa only [Real.dist_eq, hz, sub_zero] using hb hd
  exact (hf x hx y hy).trans_lt ((le_abs_self _).trans_lt hb')

theorem real_holder_estimate_uniformContinuous
    {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (C α : ℝ)
    (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : ∀ x ∈ E, ∀ y ∈ E, |f x - f y| ≤ C * dist x y ^ α) :
    RelativeUniformContinuous f E := by
  apply holder_estimate_uniformContinuous f E C α hC hα hα1
  simpa only [Real.dist_eq] using hf

theorem complex_holder_estimate_uniformContinuous
    {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (C α : ℝ)
    (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : ∀ x ∈ E, ∀ y ∈ E, ‖f x - f y‖ ≤ C * dist x y ^ α) :
    RelativeUniformContinuous f E := by
  apply holder_estimate_uniformContinuous f E C α hC hα hα1
  simpa only [dist_eq_norm] using hf

theorem holder_estimate_zero_iff
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (α : ℝ) :
    (∀ x ∈ E, ∀ y ∈ E, dist (f x) (f y) ≤ 0 * dist x y ^ α) ↔
      ∀ x ∈ E, ∀ y ∈ E, f x = f y := by
  simp only [zero_mul, dist_le_zero]

theorem holder_estimate_one_iff_lipschitzOnWith
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (C : ℝ≥0) :
    (∀ x ∈ E, ∀ y ∈ E, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (1 : ℝ)) ↔
      LipschitzOnWith C f E := by
  simpa only [Real.rpow_one] using
    (lipschitzOnWith_iff_dist_le_mul (f := f) (s := E) (K := C)).symm

theorem holder_estimate_iff_holderOnWith
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (C α : ℝ≥0) :
    (∀ x ∈ E, ∀ y ∈ E,
      dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ)) ↔ HolderOnWith C α f E := by
  constructor
  · intro h x hx y hy
    rw [edist_nndist, edist_nndist,
      ← ENNReal.coe_rpow_of_nonneg _ α.coe_nonneg, ← ENNReal.coe_mul,
      ENNReal.coe_le_coe]
    exact_mod_cast h x hx y hy
  · intro h x hx y hy
    exact h.dist_le hx hy

theorem abs_one_lipschitz : LipschitzWith 1 (abs : ℝ → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [NNReal.coe_one, one_mul, Real.dist_eq] using abs_abs_sub_abs_le x y

/-- The absolute-value counterexample in the Lipschitz section. Its name is
separate from the derivative chapter's declaration of the same fact. -/
theorem lipschitz_example_abs_not_differentiable_zero : ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0 :=
  not_differentiableAt_abs_zero

theorem abs_differenceQuotient_pos (h : ℝ) (hh : 0 < h) :
    (|h| - |(0 : ℝ)|) / h = 1 := by
  rw [abs_of_pos hh, abs_zero, sub_zero, div_self hh.ne']

theorem abs_differenceQuotient_neg (h : ℝ) (hh : h < 0) :
    (|h| - |(0 : ℝ)|) / h = -1 := by
  rw [abs_of_neg hh, abs_zero, sub_zero, neg_div, div_self hh.ne]

end SingleVariableAnalysis
