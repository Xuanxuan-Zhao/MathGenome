import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Independent specification of paper.tex, d13:09:reduction.
Real intervals may have either endpoint included; classical solution intervals
are nondegenerate. Continuous first and second derivative witnesses express C²
regularity, including the corresponding one-sided derivatives at included ends.
Complex derivatives are ordinary complex derivatives on the actual open domain.
-/
noncomputable section
open Set MeasureTheory

namespace D13Unified.Ch09.ReductionOrder

/-- A C² solution, with its two continuous derivative representatives. -/
def IsSecondOrderSolutionOn {𝕂 : Type*} [NontriviallyNormedField 𝕂]
    (J : Set 𝕂) (p q y dy ddy : 𝕂 → 𝕂) : Prop :=
  ContinuousOn y J ∧ ContinuousOn dy J ∧ ContinuousOn ddy J ∧
  (∀ t ∈ J, HasDerivWithinAt y (dy t) J t) ∧
  (∀ t ∈ J, HasDerivWithinAt dy (ddy t) J t) ∧
  ∀ t ∈ J, ddy t + p t * dy t + q t * y t = 0

/-- Linear independence as functions on precisely J. -/
def IndependentOn {𝕂 : Type*} [Field 𝕂] (J : Set 𝕂) (y z : 𝕂 → 𝕂) : Prop :=
  ∀ a b : 𝕂, (∀ t ∈ J, a * y t + b * z t = 0) → a = 0 ∧ b = 0

end D13Unified.Ch09.ReductionOrder

namespace Specs.D13Unified.Ch09.ReductionOrder
open _root_.D13Unified _root_.D13Unified.Ch09.ReductionOrder

/-- The real oriented-integral formula, its C² equation, Wronskian, and
independence on a nondegenerate real interval, without restrictions on endpoints. -/
def RealReductionWithDerivatives : Prop :=
  ∀ (I : TimeInterval) (t₀ : ℝ) (p q y dy ddy : ℝ → ℝ),
    I.carrier.Nontrivial → t₀ ∈ I.carrier →
    ContinuousOn p I.carrier → ContinuousOn q I.carrier →
    IsSecondOrderSolutionOn I.carrier p q y dy ddy →
    (∀ t ∈ I.carrier, y t ≠ 0) →
    let e := fun t => Real.exp (-(∫ r in t₀..t, p r))
    let y₂ := fun t => y t * ∫ s in t₀..t, e s / y s ^ 2
    ∃ dy₂ ddy₂ : ℝ → ℝ,
      IsSecondOrderSolutionOn I.carrier p q y₂ dy₂ ddy₂ ∧
      (∀ t ∈ I.carrier, y t * dy₂ t - dy t * y₂ t = e t) ∧
      IndependentOn I.carrier y y₂

/-- C² formulation with canonical derivatives relative to the actual interval.
Nondegeneracy is automatic for the open classical domains of Chapter 1.
The extension to other endpoint types uses the corresponding within derivatives. -/
def RealReduction : Prop :=
  ∀ (I : TimeInterval) (t₀ : ℝ) (p q y : ℝ → ℝ),
    I.carrier.Nontrivial → t₀ ∈ I.carrier →
    ContinuousOn p I.carrier → ContinuousOn q I.carrier →
    ContDiffOn ℝ 2 y I.carrier →
    (∀ t ∈ I.carrier, derivWithin (derivWithin y I.carrier) I.carrier t +
      p t * derivWithin y I.carrier t + q t * y t = 0) →
    (∀ t ∈ I.carrier, y t ≠ 0) →
    let e := fun t => Real.exp (-(∫ r in t₀..t, p r))
    let y₂ := fun t => y t * ∫ s in t₀..t, e s / y s ^ 2
    ContDiffOn ℝ 2 y₂ I.carrier ∧
      (∀ t ∈ I.carrier, derivWithin (derivWithin y₂ I.carrier) I.carrier t +
        p t * derivWithin y₂ I.carrier t + q t * y₂ t = 0) ∧
      (∀ t ∈ I.carrier, y t * derivWithin y₂ I.carrier t -
        derivWithin y I.carrier t * y₂ t = e t) ∧
      IndependentOn I.carrier y y₂

/-- In the original open-interval convention for classical solutions there is
no separate nondegeneracy hypothesis, and all derivatives are ordinary ones. -/
def ClassicalRealReduction : Prop :=
  ∀ (I : OpenTimeInterval) (t₀ : ℝ) (p q y : ℝ → ℝ),
    t₀ ∈ I.carrier → ContinuousOn p I.carrier → ContinuousOn q I.carrier →
    ContDiffOn ℝ 2 y I.carrier →
    (∀ t ∈ I.carrier, deriv (deriv y) t + p t * deriv y t + q t * y t = 0) →
    (∀ t ∈ I.carrier, y t ≠ 0) →
    let e := fun t => Real.exp (-(∫ r in t₀..t, p r))
    let y₂ := fun t => y t * ∫ s in t₀..t, e s / y s ^ 2
    ContDiffOn ℝ 2 y₂ I.carrier ∧
      (∀ t ∈ I.carrier, deriv (deriv y₂) t + p t * deriv y₂ t + q t * y₂ t = 0) ∧
      (∀ t ∈ I.carrier, y t * deriv y₂ t - deriv y t * y₂ t = e t) ∧
      IndependentOn I.carrier y y₂

/-- The complex result uses normalized primitives on the given simply connected
open domain, with no convexity or globally chosen logarithm assumption. -/
def HolomorphicReduction : Prop :=
  ∀ (D : Set ℂ) (t₀ : ℂ) (p q y : ℂ → ℂ),
    IsOpen D → IsSimplyConnected D → t₀ ∈ D →
    DifferentiableOn ℂ p D → DifferentiableOn ℂ q D →
    DifferentiableOn ℂ y D → (∀ z ∈ D, y z ≠ 0) →
    (∀ z ∈ D, deriv (deriv y) z + p z * deriv y z + q z * y z = 0) →
    ∃ P V : ℂ → ℂ,
      P t₀ = 0 ∧ V t₀ = 0 ∧
      (∀ z ∈ D, HasDerivAt P (p z) z) ∧
      (∀ z ∈ D, HasDerivAt V (Complex.exp (-P z) / y z ^ 2) z) ∧
      let y₂ := fun z => y z * V z
      DifferentiableOn ℂ y₂ D ∧
      (∀ z ∈ D, deriv (deriv y₂) z + p z * deriv y₂ z + q z * y₂ z = 0) ∧
      (∀ z ∈ D, y z * deriv y₂ z - deriv y z * y₂ z = Complex.exp (-P z)) ∧
      IndependentOn D y y₂

end Specs.D13Unified.Ch09.ReductionOrder
