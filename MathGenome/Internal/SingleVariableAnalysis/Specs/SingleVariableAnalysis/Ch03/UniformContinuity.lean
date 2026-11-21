import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.Continuity

/-!
Independent specification for K03.03.uniform_continuity (paper.tex:585–591).
The single radius controls every pair in E. Metric targets include both scalar
targets; the real and complex statements explicitly identify absolute value
and modulus. No compactness, completeness or nonemptiness is assumed.
Sequence index n represents the manuscript's positive index n+1. The two
sequences need not converge individually: only their mutual distance tends to 0.
-/
namespace Specs.SingleVariableAnalysis.Ch03.UniformContinuity

open scoped Topology
universe u v

def relativeUniformContinuousType : Type (max (u + 1) (v + 1)) :=
  {X : Type u} → {Y : Type v} → [MetricSpace X] → [MetricSpace Y] →
    (X → Y) → Set X → Prop

def relativeUniformContinuousValue : relativeUniformContinuousType.{u,v} :=
  fun f E => ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → dist (f x) (f y) < ε

def relativeUniformContinuousOnIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X),
    relativeUniformContinuousValue f E ↔ UniformContinuousOn f E

def relativeUniformContinuousSubtypeIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X),
    relativeUniformContinuousValue f E ↔ UniformContinuous (fun x : E => f x)

def relativeUniformContinuousImpliesContinuous : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X),
    relativeUniformContinuousValue f E →
      Specs.SingleVariableAnalysis.Ch03.Continuity.relativeContinuousValue f E

def relativeUniformContinuousFailureIff : Prop :=
  ∀ {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (E : Set X),
    ¬ relativeUniformContinuousValue f E ↔
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ x y : ℕ → X,
        (∀ n, x n ∈ E) ∧ (∀ n, y n ∈ E) ∧
        Filter.Tendsto (fun n => dist (x n) (y n)) Filter.atTop (𝓝 (0 : ℝ)) ∧
        ∀ n, ε₀ ≤ dist (f (x n)) (f (y n))

def realRelativeUniformContinuousIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X),
    relativeUniformContinuousValue f E ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → |f x - f y| < ε

def complexRelativeUniformContinuousIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X),
    relativeUniformContinuousValue f E ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ x ∈ E, ∀ y ∈ E, dist x y < δ → ‖f x - f y‖ < ε

def realRelativeUniformContinuousFailureIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℝ) (E : Set X),
    ¬ relativeUniformContinuousValue f E ↔
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ x y : ℕ → X,
        (∀ n, x n ∈ E) ∧ (∀ n, y n ∈ E) ∧
        Filter.Tendsto (fun n => dist (x n) (y n)) Filter.atTop (𝓝 (0 : ℝ)) ∧
        ∀ n, ε₀ ≤ |f (x n) - f (y n)|

def complexRelativeUniformContinuousFailureIff : Prop :=
  ∀ {X : Type u} [MetricSpace X] (f : X → ℂ) (E : Set X),
    ¬ relativeUniformContinuousValue f E ↔
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ x y : ℕ → X,
        (∀ n, x n ∈ E) ∧ (∀ n, y n ∈ E) ∧
        Filter.Tendsto (fun n => dist (x n) (y n)) Filter.atTop (𝓝 (0 : ℝ)) ∧
        ∀ n, ε₀ ≤ ‖f (x n) - f (y n)‖

end Specs.SingleVariableAnalysis.Ch03.UniformContinuity
