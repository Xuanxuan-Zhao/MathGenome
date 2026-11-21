import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
The diagonal clause of paper.tex, Proposition `fa2:p3:fourier-four-points`
(lines 15473–15500). `Sequence p` is the usual complex sequence space,
including the bounded sequences when `p = ∞`. A coefficient sequence in
`Sequence ∞` is exactly an arbitrary bounded scalar sequence.
-/

noncomputable section
open scoped ENNReal

namespace ExpandedFA.Models.DiagonalLpSpectrumSpec

abbrev Sequence (p : ℝ≥0∞) := lp (fun _ : ℕ => ℂ) p

/-- Pointwise multiplication preserves ℓᵖ under a bounded coefficient sequence. -/
def diagonalLinear (p : ℝ≥0∞) (a : Sequence ∞) : Sequence p →ₗ[ℂ] Sequence p where
  toFun x := ⟨fun n => a n * x n, by
    apply ((lp.memℓp x).norm.const_smul ‖a‖).mono
    intro n
    change ‖a n * x n‖ ≤ ‖a‖ * ‖x n‖
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (lp.norm_apply_le_norm ENNReal.top_ne_zero a n) (norm_nonneg _)⟩
  map_add' x y := by
    apply lp.ext
    funext n
    exact mul_add _ _ _
  map_smul' c x := by
    apply lp.ext
    funext n
    change a n * (c * x n) = c * (a n * x n)
    exact mul_left_comm _ _ _

/-- A bound valid for finite p and for the supremum norm. -/
theorem diagonalLinear_bound (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (a : Sequence ∞) (x : Sequence p) :
    ‖diagonalLinear p a x‖ ≤ ‖a‖ * ‖x‖ := by
  calc
    _ ≤ ‖‖a‖ • x‖ := by
      apply lp.norm_mono (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
      intro n
      change ‖a n * x n‖ ≤ ‖‖a‖ • x n‖
      rw [norm_mul, norm_smul, Real.norm_eq_abs, abs_norm]
      exact mul_le_mul_of_nonneg_right
        (lp.norm_apply_le_norm ENNReal.top_ne_zero a n) (norm_nonneg _)
    _ = ‖a‖ * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_norm]

/-- The bounded diagonal operator, defined on the whole of ℓᵖ. -/
def diagonalValue (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Sequence ∞) :
    Sequence p →L[ℂ] Sequence p :=
  (diagonalLinear p a).mkContinuous ‖a‖ (diagonalLinear_bound p a)

/-- Fully quantified type and value for the operator construction. -/
def DiagonalType := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (_a : Sequence ∞),
  Sequence p →L[ℂ] Sequence p

def DiagonalApply : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Sequence ∞)
    (x : Sequence p) (n : ℕ), diagonalValue p a x n = a n * x n

def DiagonalNormBound : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Sequence ∞),
  ‖diagonalValue p a‖ ≤ ‖a‖

/-- There is no restriction `p ≠ ∞` in this statement. -/
def SpectrumLaw : Prop := ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : Sequence ∞),
  spectrum ℂ (diagonalValue p a) = closure (Set.range fun n => a n)

/-- The same assertion presented with a raw sequence and its boundedness proof. -/
def BoundedSequenceSpectrumLaw : Prop :=
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)] (a : ℕ → ℂ)
    (ha : BddAbove (Set.range fun n => ‖a n‖)),
    spectrum ℂ (diagonalValue p ⟨a, memℓp_infty ha⟩) = closure (Set.range a)

end ExpandedFA.Models.DiagonalLpSpectrumSpec
