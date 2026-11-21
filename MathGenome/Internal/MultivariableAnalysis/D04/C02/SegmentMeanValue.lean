import MathGenome.Internal.MultivariableAnalysis.D04.C02.DerivativeBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.SegmentMeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

noncomputable section
open Set
namespace D04

private theorem segment_interior_point {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a b : X) (hne : a ≠ b) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    a + t • (b - a) ∈ segment ℝ a b ∧
      a + t • (b - a) ≠ a ∧ a + t • (b - a) ≠ b := by
  have hs : a + t • (b - a) ∈ openSegment ℝ a b := by
    rw [openSegment_eq_image']
    exact ⟨t, ht, rfl⟩
  refine ⟨openSegment_subset_segment ℝ a b hs, ?_, ?_⟩
  · intro he
    rw [he] at hs
    exact hne (left_mem_openSegment_iff.mp hs)
  · intro he
    rw [he] at hs
    exact hne (right_mem_openSegment_iff.mp hs)

/-- Scalar MVT on a line, with continuity at its endpoints and derivatives
only for parameters strictly between them. -/
private theorem scalar_line_mean_value {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f : X → ℝ) (A : X → X →L[ℝ] ℝ) (a b : X)
    (hc : ContinuousOn f (segment ℝ a b))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasFDerivAt f (A (a + t • (b - a)))
      (a + t • (b - a))) :
    ∃ t ∈ Ioo (0 : ℝ) 1, f b - f a = A (a + t • (b - a)) (b - a) := by
  have hl : Continuous (fun t : ℝ => a + t • (b - a)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  have hc' : ContinuousOn (fun t : ℝ => f (a + t • (b - a))) (Icc 0 1) := by
    apply hc.comp hl.continuousOn
    intro t ht
    rw [segment_eq_image']
    exact ⟨t, ht, rfl⟩
  have hd' (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun t : ℝ => f (a + t • (b - a)))
        (A (a + t • (b - a)) (b - a)) t := by
    have hline : HasDerivAt (fun s : ℝ => a + s • (b - a)) (b - a) t := by
      simpa using ((hasDerivAt_id t).smul_const (b - a)).const_add a
    exact (hd t ht).comp_hasDerivAt t hline
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope _ _ zero_lt_one hc' hd'
  exact ⟨t, ht, by simpa using he.symm⟩

theorem scalar_segment_mean_value {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (a b : E n) (hU : IsOpen U) (hs : segment ℝ a b ⊆ U) (hne : a ≠ b)
    (hc : ContinuousOn f (segment ℝ a b))
    (hd : ∀ x ∈ segment ℝ a b, x ≠ a → x ≠ b → TotalDifferentiableAt U f x) :
    ∃ t ∈ Ioo (0 : ℝ) 1,
      f b - f a = totalDerivative f (a + t • (b - a)) (b - a) := by
  apply scalar_line_mean_value f (totalDerivative f) a b hc
  intro t ht
  obtain ⟨hx, hxa, hxb⟩ := segment_interior_point a b hne ht
  exact ((totalDifferentiableAt_iff_differentiableAt U f _ hU (hs hx)).mp
    (hd _ hx hxa hxb)).hasFDerivAt

theorem segment_mean_value_bound {n m : ℕ} (U : Set (E n)) (f : E n → E m)
    (a b : E n) (M : ℝ) (hU : IsOpen U) (hs : segment ℝ a b ⊆ U)
    (hc : ContinuousOn f (segment ℝ a b))
    (hd : ∀ x ∈ segment ℝ a b, x ≠ a → x ≠ b → TotalDifferentiableAt U f x)
    (hM : ∀ x ∈ segment ℝ a b, x ≠ a → x ≠ b → ‖totalDerivative f x‖ ≤ M) :
    ‖f b - f a‖ ≤ M * ‖b - a‖ := by
  by_cases hab : a = b
  · subst b
    simp
  have hd' (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasFDerivAt f (totalDerivative f (a + t • (b - a))) (a + t • (b - a)) := by
    obtain ⟨hx, hxa, hxb⟩ := segment_interior_point a b hab ht
    exact ((totalDifferentiableAt_iff_differentiableAt U f _ hU (hs hx)).mp
      (hd _ hx hxa hxb)).hasFDerivAt
  have hM' (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      ‖totalDerivative f (a + t • (b - a))‖ ≤ M := by
    obtain ⟨hx, hxa, hxb⟩ := segment_interior_point a b hab ht
    exact hM _ hx hxa hxb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM' (1 / 2) (by constructor <;> norm_num))
  let z := f b - f a
  by_cases hz : z = 0
  · change ‖z‖ ≤ _
    rw [hz, norm_zero]
    exact mul_nonneg hM0 (norm_nonneg _)
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  obtain ⟨t, ht, he⟩ := scalar_line_mean_value (fun x => inner ℝ z (f x))
    (fun x => (innerSL ℝ z).comp (totalDerivative f x)) a b
    ((innerSL ℝ z).continuous.comp_continuousOn hc)
    (fun t ht => (innerSL ℝ z).hasFDerivAt.comp _ (hd' t ht))
  have he' : ‖z‖ ^ 2 = inner ℝ z (totalDerivative f (a + t • (b - a)) (b - a)) := by
    change inner ℝ z (f b) - inner ℝ z (f a) = _ at he
    rw [← inner_sub_right] at he
    change inner ℝ z z = _ at he
    rwa [real_inner_self_eq_norm_sq] at he
  have hb := (real_inner_le_norm z (totalDerivative f (a + t • (b - a)) (b - a))).trans
    (mul_le_mul_of_nonneg_left
      (((totalDerivative f (a + t • (b - a))).le_opNorm (b - a)).trans
        (mul_le_mul_of_nonneg_right (hM' t ht) (norm_nonneg _))) (norm_nonneg z))
  rw [← he'] at hb
  change ‖z‖ ≤ M * ‖b - a‖
  nlinarith

/-- The polynomial curve used in the paper's counterexample. -/
def meanValueCounterexample : Specs.D04.C02.SegmentMeanValue.meanValueCounterexampleType :=
  Specs.D04.C02.SegmentMeanValue.meanValueCounterexampleValue

theorem meanValueCounterexample_hasDerivAt (c : ℝ) :
    HasDerivAt meanValueCounterexample (WithLp.toLp 2 ![2 * c, 3 * c ^ 2]) c := by
  have hp : HasDerivAt (fun t : ℝ => (![t ^ 2, t ^ 3] : Fin 2 → ℝ))
      (![2 * c, 3 * c ^ 2] : Fin 2 → ℝ) c := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using! (hasDerivAt_id c).pow 2
    · simpa using! (hasDerivAt_id c).pow 3
  exact (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 _).comp_hasDerivAt c hp

theorem meanValueCounterexample_continuous : Continuous meanValueCounterexample :=
  continuous_iff_continuousAt.mpr fun c => (meanValueCounterexample_hasDerivAt c).continuousAt

/-- A common point would force both 1 = 2c and 1 = 3c². -/
theorem vector_mean_value_no_common_point :
    ¬ ∃ c ∈ Ioo (0 : ℝ) 1,
      meanValueCounterexample 1 - meanValueCounterexample 0 =
        totalDerivative meanValueCounterexample c (1 - 0) := by
  rintro ⟨c, _, he⟩
  have hder : totalDerivative meanValueCounterexample c (1 - 0) =
      WithLp.toLp 2 (![2 * c, 3 * c ^ 2] : Fin 2 → ℝ) := by
    change fderiv ℝ meanValueCounterexample c (1 - 0) = _
    simpa using! (meanValueCounterexample_hasDerivAt c).deriv
  rw [hder] at he
  have h₁ := congrArg (fun v : E 2 => v 0) he
  have h₂ := congrArg (fun v : E 2 => v 1) he
  change (1 : ℝ) ^ 2 - 0 ^ 2 = 2 * c at h₁
  change (1 : ℝ) ^ 3 - 0 ^ 3 = 3 * c ^ 2 at h₂
  norm_num at h₁ h₂
  nlinarith

end D04
