import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.MetricCompactness
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.UniformContinuity

/-!
Independent specification for K03.03.heine_cantor (paper.tex:592–598).
The continuity hypothesis is relative to the compact metric subset E, and
the output radius controls all pairs of points in E. No nonemptiness,
ambient completeness, interval, or Lipschitz hypothesis is imposed.

The metric-target statement specializes to the two scalar targets. The
last two statements spell out the manuscript's absolute value and complex
modulus in both the continuity hypothesis and uniform-continuity conclusion.
An intrinsic compact metric domain is covered by taking E = Set.univ.
-/
namespace Specs.SingleVariableAnalysis.Ch03.HeineCantor

open Specs.SingleVariableAnalysis.Ch03.Continuity
open Specs.SingleVariableAnalysis.Ch03.UniformContinuity
universe u v

def heineCantor : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X),
    IsCompact E → relativeContinuousValue f E →
      relativeUniformContinuousValue f E

def heineCantorReal : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X),
    IsCompact E →
    (∀ a ∈ E, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, dist x a < δ → |f x - f a| < ε) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → |f x - f y| < ε

def heineCantorComplex : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X),
    IsCompact E →
    (∀ a ∈ E, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, dist x a < δ → ‖f x - f a‖ < ε) →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → ‖f x - f y‖ < ε

end Specs.SingleVariableAnalysis.Ch03.HeineCantor
