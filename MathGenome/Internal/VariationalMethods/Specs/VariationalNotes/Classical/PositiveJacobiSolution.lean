import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! The Jacobi stage of paper.tex, Theorem 7.9 (`thm:v07-06-01`) (lines 3419–3450).
The first state coordinate is v and the second is its momentum q = Pv'.
Derivatives are taken within the actual closed interval, so initial derivatives
are right derivatives. Ambient representatives are unique only on [a,b]. -/

namespace VariationalNotes.Classical.Jacobi
open Set

/-- The continuous first-order formulation of (Pv')' = Vv. -/
def IsSolution (P V : ℝ → ℝ) (a b : ℝ) (Y : ℝ → ℝ × ℝ) : Prop :=
  ContinuousOn Y (Icc a b) ∧
    ∀ t ∈ Icc a b, HasDerivWithinAt Y
      ((Y t).2 / P t, V t * (Y t).1) (Icc a b) t

end VariationalNotes.Classical.Jacobi

namespace Specs.VariationalNotes.Classical.Jacobi
open Set _root_.VariationalNotes.Classical.Jacobi

/-- Existence and uniqueness of the normalized Jacobi field, its sign in the
absence of conjugate points, and construction of a solution positive even at a.
The coefficient hypotheses are precisely those isolated from the source. -/
def PositiveJacobiSolution : Prop :=
  ∀ (a b : ℝ) (P V : ℝ → ℝ), a < b →
    ContDiffOn ℝ 1 P (Icc a b) → ContinuousOn V (Icc a b) →
    (∀ t ∈ Icc a b, 0 < P t) →
    ∃ Y₀ : ℝ → ℝ × ℝ,
      IsSolution P V a b Y₀ ∧ Y₀ a = (0, P a) ∧
      HasDerivWithinAt (fun t => (Y₀ t).1) 1 (Icc a b) a ∧
      (∀ Z : ℝ → ℝ × ℝ, IsSolution P V a b Z → Z a = (0, P a) →
        EqOn Z Y₀ (Icc a b)) ∧
      ((∀ t ∈ Ioc a b, (Y₀ t).1 ≠ 0) →
        (∀ t ∈ Ioc a b, 0 < (Y₀ t).1) ∧
        ∃ Y : ℝ → ℝ × ℝ, IsSolution P V a b Y ∧
          ∀ t ∈ Icc a b, 0 < (Y t).1)

end Specs.VariationalNotes.Classical.Jacobi
