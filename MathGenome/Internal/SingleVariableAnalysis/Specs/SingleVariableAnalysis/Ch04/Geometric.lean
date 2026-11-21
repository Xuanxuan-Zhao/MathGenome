import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Peano

/-!
Independent specification of K03.04.geometric, paper.tex:783–793.
An affine function through (a, f a) is written explicitly as
x ↦ f a + (x-a) • v. Real scalar multiplication gives L*(x-a) for
real values and L*((x-a) : ℂ) for complex values. All increments and
elapsed times are real. The statements for a domain I require interiority
and test the error only at increments remaining in I; no endpoint
or nonzero derivative hypothesis is imposed.
-/

namespace Specs.SingleVariableAnalysis.Ch04.Geometric

open Filter
open scoped Topology
universe u

/-- The error characterizes exactly the derivative slope. -/
def affineTangentIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (a : ℝ),
    Derivative.hasRealIncrementDerivativeValue f L a → ∀ v : F,
      (Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
        (fun h => f (a + h) - (f a + (a + h - a) • v)) (fun h : ℝ => h) ↔ v = L)

/-- The canonical tangent is the unique affine function through f a with
little-o error, with equality as functions, not merely equality of slopes. -/
def tangentUnique : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (a : ℝ), DifferentiableAt ℝ f a →
    let l : ℝ → F := fun x => f a + (x - a) • deriv f a
    l a = f a ∧
    Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
      (fun h => f (a + h) - l (a + h)) (fun h : ℝ => h) ∧
    ∀ m : ℝ → F, (∃ v : F, ∀ x : ℝ, m x = f a + (x - a) • v) →
      Asymptotics.IsLittleO (𝓝[≠] (0 : ℝ))
        (fun h => f (a + h) - m (a + h)) (fun h : ℝ => h) → m = l

def withinAffineTangentIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    Derivative.hasRealIncrementDerivativeWithinValue f L I a → ∀ v : F,
      (Asymptotics.IsLittleO (𝓝[{h : ℝ | a + h ∈ I} \ {0}] (0 : ℝ))
        (fun h => f (a + h) - (f a + (a + h - a) • v)) (fun h : ℝ => h) ↔ v = L)

/-- Uniqueness on the original domain does not constrain ambient extensions
away from that domain. Affineness is required only on I. -/
def withinTangentUnique : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (L : F) (I : Set ℝ) (a : ℝ), a ∈ interior I →
    Derivative.hasRealIncrementDerivativeWithinValue f L I a →
    let l : ℝ → F := fun x => f a + (x - a) • L
    l a = f a ∧
    Asymptotics.IsLittleO (𝓝[{h : ℝ | a + h ∈ I} \ {0}] (0 : ℝ))
      (fun h => f (a + h) - l (a + h)) (fun h : ℝ => h) ∧
    ∀ m : ℝ → F, (∃ v : F, ∀ x ∈ I, m x = f a + (x - a) • v) →
      Asymptotics.IsLittleO (𝓝[{h : ℝ | a + h ∈ I} \ {0}] (0 : ℝ))
        (fun h => f (a + h) - m (a + h)) (fun h : ℝ => h) → Set.EqOn m l I

def realAffineTangentIff : Prop :=
  ∀ (f : ℝ → ℝ) (L a : ℝ), Derivative.hasRealIncrementDerivativeValue f L a →
    ∀ v : ℝ, (Ch02.BigO.scalarLittleOValue (𝓝[≠] (0 : ℝ))
      (fun h => f (a + h) - (f a + v * (a + h - a))) (fun h : ℝ => h) ↔ v = L)

def complexAffineTangentIff : Prop :=
  ∀ (f : ℝ → ℂ) (L : ℂ) (a : ℝ), Derivative.hasRealIncrementDerivativeValue f L a →
    ∀ v : ℂ, (Ch02.BigO.scalarLittleOValue (𝓝[≠] (0 : ℝ))
      (fun h => f (a + h) - (f a + v * ((a + h - a : ℝ) : ℂ)))
      (fun h : ℝ => (h : ℂ)) ↔ v = L)

/-- Velocity is the finite displacement/real-time limit. -/
def instantaneousVelocityIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (v : F) (t : ℝ),
    Derivative.hasRealIncrementDerivativeValue f v t ↔
      Tendsto (fun h : ℝ => h⁻¹ • (f (t + h) - f t)) (𝓝[≠] (0 : ℝ)) (𝓝 v)

def withinInstantaneousVelocityIff : Prop :=
  ∀ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (v : F) (I : Set ℝ) (t : ℝ),
    Derivative.hasRealIncrementDerivativeWithinValue f v I t ↔
      Tendsto (fun h : ℝ => h⁻¹ • (f (t + h) - f t))
        (𝓝[{h : ℝ | t + h ∈ I} \ {0}] (0 : ℝ)) (𝓝 v)

def realInstantaneousVelocity : Prop :=
  ∀ (f : ℝ → ℝ) (t : ℝ), DifferentiableAt ℝ f t →
    Tendsto (fun h : ℝ => (f (t + h) - f t) / h)
      (𝓝[≠] (0 : ℝ)) (𝓝 (deriv f t))

def complexInstantaneousVelocity : Prop :=
  ∀ (f : ℝ → ℂ) (t : ℝ), DifferentiableAt ℝ f t →
    Tendsto (fun h : ℝ => (f (t + h) - f t) / (h : ℂ))
      (𝓝[≠] (0 : ℝ)) (𝓝 (deriv f t))

end Specs.SingleVariableAnalysis.Ch04.Geometric
