import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent statement of paper.tex, Lemma `p102:u5-moser-1d`.

Functions are represented on `ℝ`; their values on the negative half-line are
irrelevant. Local absolute continuity includes the endpoint zero. All integrals
use Lebesgue measure; deleting the singleton endpoint does not change them.
Using the nonnegative extended integral in the conclusion
expresses both integrability and the bound, without the convention that a
nonintegrable Bochner integral is zero.
-/

open Set MeasureTheory

noncomputable section

namespace P102.Sobolev.Moser

/-- The ordinary real derivative, fixed once for the half-line representation. -/
def slope (w : ℝ → ℝ) : ℝ → ℝ := deriv w

/-- Exactly the hypotheses on the function in the one-dimensional estimate. -/
structure Admissible (d : ℕ) (w : ℝ → ℝ) : Prop where
  locallyAC : ∀ R : ℝ, 0 ≤ R → AbsolutelyContinuousOnInterval w 0 R
  nonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ w t
  zero : w 0 = 0
  energy_le_one :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (|slope w t| ^ d)) ≤ 1

/-- The exponent `b = (d - 1) / d` from the manuscript. -/
def exponent (d : ℕ) : ℝ := ((d : ℝ) - 1) / d

/-- The full estimate; the real constant is uniform in every admissible `w`. -/
def OneDimensionalEstimate : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ C : ℝ, 0 ≤ C ∧
    ∀ w : ℝ → ℝ, Admissible d w →
      (∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal (Real.exp ((w t) ^ (1 / exponent d) - t))) ≤ ENNReal.ofReal C

end P102.Sobolev.Moser
