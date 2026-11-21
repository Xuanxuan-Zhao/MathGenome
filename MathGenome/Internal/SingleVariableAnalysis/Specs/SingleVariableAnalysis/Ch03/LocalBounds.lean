import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity

/-!
Independent specification for K03.03.local_bounds (paper.tex:513–521).
The scalar targets are the canonical ℝ and ℂ. A relative neighborhood is
expressed as a positive-radius ball tested only on E, including its base point.
There is no accumulation, openness, or compactness hypothesis. Taking E = univ
also covers an intrinsic metric domain. The final two statements record the
explicit consequence for continuous nonzero denominators.
-/

namespace Specs.SingleVariableAnalysis.Ch03.LocalBounds

open Specs.SingleVariableAnalysis.Ch03.Continuity
universe u

def realLocalUpperBound : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E),
    relativeContinuousAtValue f E a →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → |f x| ≤ |f a| + 1

def complexLocalUpperBound : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (a : E),
    relativeContinuousAtValue f E a →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → ‖f x‖ ≤ ‖f a‖ + 1

def realLocalLowerBound : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E),
    relativeContinuousAtValue f E a → f a ≠ 0 →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → |f a| / 2 ≤ |f x|

def complexLocalLowerBound : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (a : E),
    relativeContinuousAtValue f E a → f a ≠ 0 →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → ‖f a‖ / 2 ≤ ‖f x‖

def realLocalPositive : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E),
    relativeContinuousAtValue f E a → 0 < f a →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ →
        f a / 2 < f x ∧ 0 < f a / 2

def realLocalNonzero : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (a : E),
    relativeContinuousAtValue f E a → f a ≠ 0 →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → f x ≠ 0

def complexLocalNonzero : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (a : E),
    relativeContinuousAtValue f E a → f a ≠ 0 →
      ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ E, dist x a < δ → f x ≠ 0

end Specs.SingleVariableAnalysis.Ch03.LocalBounds
