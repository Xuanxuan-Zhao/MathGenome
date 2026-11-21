import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.UniformContinuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch07.RealPowers
import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.Deriv.Abs

/-!
Independent specification for K03.03.lipschitz, paper.tex:600–609.
Distances raised to a real exponent use `Real.rpow`. The first obligation
identifies this with the upstream real power, including its extension at zero,
for every nonnegative distance and positive exponent. Metric targets give a
common statement that specializes explicitly to real and complex scalars.
No compactness, boundedness, completeness or nonemptiness of E is imposed.

`HolderOnWith` is Mathlib's quantitative Hölder predicate; the bridge holds
for all nonnegative parameters and hence in particular for 0 < α < 1.
At α = 1 the estimate is exactly Lipschitz continuity. The non-differentiability
claim is an ordinary derivative with real increments, at the interior point 0.
-/
namespace Specs.SingleVariableAnalysis.Ch03.Lipschitz
open scoped NNReal ENNReal
universe u v

def nonnegativePartialRealPower : Prop :=
  ∀ d α : ℝ, 0 ≤ d → 0 < α →
    Specs.SingleVariableAnalysis.Ch07.RealPowers.partialRealPowerValue d α = some (d ^ α)

def holderEstimateUniformContinuous : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (C α : ℝ),
    0 ≤ C → 0 < α → α ≤ 1 →
    (∀ x ∈ E, ∀ y ∈ E, dist (f x) (f y) ≤ C * dist x y ^ α) →
    UniformContinuity.relativeUniformContinuousValue f E

def realHolderEstimateUniformContinuous : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X) (C α : ℝ),
    0 ≤ C → 0 < α → α ≤ 1 →
    (∀ x ∈ E, ∀ y ∈ E, |f x - f y| ≤ C * dist x y ^ α) →
    UniformContinuity.relativeUniformContinuousValue f E

def complexHolderEstimateUniformContinuous : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X) (C α : ℝ),
    0 ≤ C → 0 < α → α ≤ 1 →
    (∀ x ∈ E, ∀ y ∈ E, ‖f x - f y‖ ≤ C * dist x y ^ α) →
    UniformContinuity.relativeUniformContinuousValue f E

def holderEstimateZeroIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (α : ℝ),
    (∀ x ∈ E, ∀ y ∈ E, dist (f x) (f y) ≤ 0 * dist x y ^ α) ↔
      ∀ x ∈ E, ∀ y ∈ E, f x = f y

def holderEstimateOneIffLipschitz : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (C : ℝ≥0),
    (∀ x ∈ E, ∀ y ∈ E, dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (1 : ℝ)) ↔
      LipschitzOnWith C f E

def holderEstimateIffHolder : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X) (C α : ℝ≥0),
    (∀ x ∈ E, ∀ y ∈ E,
      dist (f x) (f y) ≤ (C : ℝ) * dist x y ^ (α : ℝ)) ↔ HolderOnWith C α f E

def absOneLipschitz : Prop := LipschitzWith 1 (abs : ℝ → ℝ)

def absNotDifferentiableZero : Prop := ¬ DifferentiableAt ℝ (abs : ℝ → ℝ) 0

def absDifferenceQuotientPos : Prop :=
  ∀ h : ℝ, 0 < h → (|h| - |(0 : ℝ)|) / h = 1

def absDifferenceQuotientNeg : Prop :=
  ∀ h : ℝ, h < 0 → (|h| - |(0 : ℝ)|) / h = -1

end Specs.SingleVariableAnalysis.Ch03.Lipschitz
