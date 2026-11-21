import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.QuadraticEventualReduction
import MathGenome.Internal.ElementaryNumberTheory.Specs.P203Specs.Ch05.PeriodicQuadraticAlgebra
import Mathlib.Data.Set.Finite.Basic

/-! The eventual-periodicity criterion of paper.tex, nt:E08, and its finite
reduced-state stage (lines 2453–2456 and 2520–2527). The discriminant may be
any positive nonsquare integer; no squarefree normalization is imposed. -/
namespace P203Specs

/-- The strict bounds for every reduced represented state, with signed integer
parameters initially allowed. No divisibility assumption is needed here. -/
def ReducedSurdStateBounds : Prop :=
  ∀ P Q D : ℤ, 0 < D → ¬ IsSquare D → Q ≠ 0 →
    ReducedQuadratic (((P : ℝ) + Real.sqrt (D : ℝ)) / (Q : ℝ)) →
      -Real.sqrt (D : ℝ) < (P : ℝ) ∧ (P : ℝ) < Real.sqrt (D : ℝ) ∧
        0 < (Q : ℝ) ∧ (Q : ℝ) < 2 * Real.sqrt (D : ℝ)

/-- For a fixed discriminant the full set of reduced integer states is finite. -/
def ReducedSurdStatesFinite : Prop :=
  ∀ D : ℤ, 0 < D → ¬ IsSquare D →
    Set.Finite {s : ℤ × ℤ | s.2 ≠ 0 ∧
      ReducedQuadratic (((s.1 : ℝ) + Real.sqrt (D : ℝ)) / (s.2 : ℝ))}

/-- Every real quadratic irrational has an eventually periodic canonical
simple continued fraction, including arbitrary initial complete quotients. -/
def QuadraticEventuallyPeriodic : Prop :=
  ∀ x : ℝ, QuadraticIrrational x → EventuallyPeriodicCF x

/-- The full Lagrange criterion, on every irrational real input. -/
def LagrangePeriodicity : Prop :=
  ∀ x : ℝ, Irrational x → (EventuallyPeriodicCF x ↔ QuadraticIrrational x)

end P203Specs
