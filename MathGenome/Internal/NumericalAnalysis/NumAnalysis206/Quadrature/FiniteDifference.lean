import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Quadrature.FiniteDifference
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.IntervalTaylor
import Mathlib.Tactic.FieldSimp

namespace NumAnalysis206.Quadrature
open Set
open NumAnalysis206.Approximation

variable {x h η M : ℝ} {f y : ℝ → ℝ} {D : ℕ → ℝ → ℝ}

/-- Central difference with a uniform third-derivative bound and sample errors. -/
theorem central_difference_bound (hh : 0 < h) (_hη : 0 ≤ η)
    (hD : IntervalJet (x - h) (x + h) 3 f D)
    (hM : ∀ t ∈ Icc (x - h) (x + h), |D 3 t| ≤ M)
    (hyp : |y (x + h) - f (x + h)| ≤ η)
    (hym : |y (x - h) - f (x - h)| ≤ η) :
    |(y (x + h) - y (x - h)) / (2 * h) - D 1 x| ≤ M * h ^ 2 / 6 + η / h := by
  have hab : x - h ≤ x + h := by linarith
  have hx : x ∈ Icc (x - h) (x + h) := ⟨by linarith, by linarith⟩
  have hp := jet_taylor_bound hab (by omega : 1 ≤ 3) hD hx
    (right_mem_Icc.mpr hab) (fun t ht => hM t (by
      rw [uIcc_of_le hx.2] at ht
      exact ⟨hx.1.trans ht.1, ht.2⟩))
  have hm := jet_taylor_bound hab (by omega : 1 ≤ 3) hD hx
    (left_mem_Icc.mpr hab) (fun t ht => hM t (by
      rw [uIcc_of_ge hx.1] at ht
      exact ⟨ht.1, ht.2.trans hx.2⟩))
  have hzero : D 0 x = f x := hD.1 hx
  simp [jetTaylorSum, IntervalTaylorSpec.sumValue, Finset.sum_range_succ,
    Nat.factorial, hzero, abs_of_pos hh, abs_of_neg (neg_neg_of_pos hh)] at hp hm
  have hn : |y (x + h) - y (x - h) - 2 * h * D 1 x| ≤ M * h ^ 3 / 3 + 2 * η := by
    rcases abs_le.mp hp with ⟨hp₁, hp₂⟩
    rcases abs_le.mp hm with ⟨hm₁, hm₂⟩
    rcases abs_le.mp hyp with ⟨hy₁, hy₂⟩
    rcases abs_le.mp hym with ⟨hz₁, hz₂⟩
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  calc
    _ = |y (x + h) - y (x - h) - 2 * h * D 1 x| / (2 * h) := by
      have heq : (y (x + h) - y (x - h)) / (2 * h) - D 1 x =
          (y (x + h) - y (x - h) - 2 * h * D 1 x) / (2 * h) := by
        field_simp
      rw [heq, abs_div, abs_of_pos (show 0 < 2 * h by positivity)]
    _ ≤ (M * h ^ 3 / 3 + 2 * η) / (2 * h) :=
      div_le_div_of_nonneg_right hn (by positivity)
    _ = M * h ^ 2 / 6 + η / h := by field_simp; ring

/-- Forward difference with a uniform second-derivative bound and sample errors. -/
theorem forward_difference_bound (hh : 0 < h) (_hη : 0 ≤ η)
    (hD : IntervalJet x (x + h) 2 f D)
    (hM : ∀ t ∈ Icc x (x + h), |D 2 t| ≤ M)
    (hyp : |y (x + h) - f (x + h)| ≤ η)
    (hyx : |y x - f x| ≤ η) :
    |(y (x + h) - y x) / h - D 1 x| ≤ M * h / 2 + 2 * η / h := by
  have hab : x ≤ x + h := by linarith
  have hx : x ∈ Icc x (x + h) := left_mem_Icc.mpr hab
  have hp := jet_taylor_bound hab (by omega : 1 ≤ 2) hD hx
    (right_mem_Icc.mpr hab) (fun t ht => hM t (by
      rwa [uIcc_of_le hab] at ht))
  have hzero : D 0 x = f x := hD.1 hx
  simp [jetTaylorSum, IntervalTaylorSpec.sumValue, Finset.sum_range_succ,
    Nat.factorial, hzero, abs_of_pos hh] at hp
  have hn : |y (x + h) - y x - h * D 1 x| ≤ M * h ^ 2 / 2 + 2 * η := by
    rcases abs_le.mp hp with ⟨hp₁, hp₂⟩
    rcases abs_le.mp hyp with ⟨hy₁, hy₂⟩
    rcases abs_le.mp hyx with ⟨hz₁, hz₂⟩
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  calc
    _ = |y (x + h) - y x - h * D 1 x| / h := by
      have heq : (y (x + h) - y x) / h - D 1 x =
          (y (x + h) - y x - h * D 1 x) / h := by
        field_simp
      rw [heq, abs_div, abs_of_pos hh]
    _ ≤ (M * h ^ 2 / 2 + 2 * η) / h := div_le_div_of_nonneg_right hn hh.le
    _ = M * h / 2 + 2 * η / h := by field_simp

/-- The source's central estimate, with the actual supremum on the stencil. -/
theorem central_difference_sup (hh : 0 < h) (hη : 0 ≤ η)
    (hD : IntervalJet (x - h) (x + h) 3 f D)
    (hyp : |y (x + h) - f (x + h)| ≤ η)
    (hym : |y (x - h) - f (x - h)| ≤ η) :
    |(y (x + h) - y (x - h)) / (2 * h) - D 1 x| ≤
      sSup ((fun t => |D 3 t|) '' Icc (x - h) (x + h)) * h ^ 2 / 6 + η / h := by
  apply central_difference_bound hh hη hD ?_ hyp hym
  intro t ht
  exact le_csSup (isCompact_Icc.bddAbove_image (hD.2.1 3 le_rfl).abs)
    (mem_image_of_mem _ ht)

/-- The source's forward estimate, with the actual supremum on the stencil. -/
theorem forward_difference_sup (hh : 0 < h) (hη : 0 ≤ η)
    (hD : IntervalJet x (x + h) 2 f D)
    (hyp : |y (x + h) - f (x + h)| ≤ η)
    (hyx : |y x - f x| ≤ η) :
    |(y (x + h) - y x) / h - D 1 x| ≤
      sSup ((fun t => |D 2 t|) '' Icc x (x + h)) * h / 2 + 2 * η / h := by
  apply forward_difference_bound hh hη hD ?_ hyp hyx
  intro t ht
  exact le_csSup (isCompact_Icc.bddAbove_image (hD.2.1 2 le_rfl).abs)
    (mem_image_of_mem _ ht)

end NumAnalysis206.Quadrature
