import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch06.LinearVolterra
import Mathlib.Analysis.Normed.Operator.Mul

/-! Whole-interval homogeneous linear IVPs (paper.tex, d13:07:fundamental,
existence stage). Time is real. `TimeInterval` retains all endpoint conventions.
The Banach-space statement permits any fixed norm, including complex spaces
regarded as real spaces. Matrix statements use actual multiplication; the
square-matrix norm is an operator norm, never the elementwise norm.
No evolution matrix is selected by an assumed existence certificate. -/
noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator

namespace D13Unified.Ch07.LinearSystemExistence
/-- The induced matrix operator in any fixed real normed realization of 𝕂ⁿ.
For complex matrices this is the actual realification, with unchanged values. -/
def matrixOperatorIn {𝕂 : Type} [RCLike 𝕂] {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (e : (Fin n → 𝕂) ≃L[ℝ] E) (A : Matrix (Fin n) (Fin n) 𝕂) : E →L[ℝ] E :=
  e.toContinuousLinearMap.comp
    ((A.mulVecLin.toContinuousLinearMap.restrictScalars ℝ).comp e.symm.toContinuousLinearMap)
end D13Unified.Ch07.LinearSystemExistence

namespace Specs.D13Unified.Ch07.LinearSystemExistence
open _root_.D13Unified
universe u

/-- Existence and uniqueness, with both the integral and classical conclusions.
Uniqueness of ambient representatives is asserted only on the actual interval. -/
def Existence : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (I : TimeInterval) (A : ℝ → E →L[ℝ] E) (s : ℝ) (ξ : E),
    s ∈ I.carrier → ContinuousOn A I.carrier →
    ∃ Y : ℝ → E, ContinuousOn Y I.carrier ∧ Y s = ξ ∧
      (∀ t ∈ I.carrier, HasDerivWithinAt Y (A t (Y t)) I.carrier t) ∧
      (∀ t ∈ I.carrier, Y t = ξ + ∫ r in s..t, A r (Y r)) ∧
      ContDiffOn ℝ 1 Y I.carrier ∧
      ∀ Z : ℝ → E, ContinuousOn Z I.carrier → Z s = ξ →
        (∀ t ∈ I.carrier, HasDerivWithinAt Z (A t (Z t)) I.carrier t) →
        EqOn Z Y I.carrier

/-- A continuous majorant, rather than a global constant, controls growth.
Taking b(t)=‖A(t)‖ gives exactly the required sharp variable bound. -/
def GrowthBound : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (I : TimeInterval) (A : ℝ → E →L[ℝ] E) (s : ℝ) (ξ : E)
    (Y : ℝ → E) (b : ℝ → ℝ),
    s ∈ I.carrier → ContinuousOn Y I.carrier → ContinuousOn b I.carrier →
    (∀ r ∈ I.carrier, 0 ≤ b r) →
    (∀ r ∈ I.carrier, ‖A r (Y r)‖ ≤ b r * ‖Y r‖) →
    (∀ t ∈ I.carrier, Y t = ξ + ∫ r in s..t, A r (Y r)) →
    ∀ t ∈ I.carrier,
      ‖Y t‖ ≤ ‖ξ‖ * Real.exp (∫ r in min s t..max s t, b r)

/-- Any real Banach algebra, in particular complex matrix algebras with real
time and every compatible submultiplicative norm. -/
def AlgebraExistence : Prop :=
  ∀ {R : Type u} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    (I : TimeInterval) (A : ℝ → R) (s : ℝ) (ξ : R),
    s ∈ I.carrier → ContinuousOn A I.carrier →
    ∃ Y : ℝ → R, ContinuousOn Y I.carrier ∧ Y s = ξ ∧
      (∀ t ∈ I.carrier, HasDerivWithinAt Y (A t * Y t) I.carrier t) ∧
      (∀ t ∈ I.carrier,
        ‖Y t‖ ≤ ‖ξ‖ * Real.exp (∫ r in min s t..max s t, ‖A r‖)) ∧
      ContDiffOn ℝ 1 Y I.carrier ∧
      ∀ Z : ℝ → R, ContinuousOn Z I.carrier → Z s = ξ →
        (∀ t ∈ I.carrier, HasDerivWithinAt Z (A t * Z t) I.carrier t) →
        EqOn Z Y I.carrier

/-- Realification of bounded 𝕂-linear operators on an arbitrary fixed normed
space; compatible real scalar structure is retained explicitly. -/
def ScalarExistence : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] {E : Type u} [NormedAddCommGroup E]
    [NormedSpace 𝕂 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕂 E] [CompleteSpace E]
    (I : TimeInterval) (A : ℝ → E →L[𝕂] E) (s : ℝ) (ξ : E),
    s ∈ I.carrier → ContinuousOn A I.carrier →
    ∃ Y : ℝ → E, ContinuousOn Y I.carrier ∧ Y s = ξ ∧
      (∀ t ∈ I.carrier, HasDerivWithinAt Y (A t (Y t)) I.carrier t) ∧
      (∀ t ∈ I.carrier,
        ‖Y t‖ ≤ ‖ξ‖ * Real.exp (∫ r in min s t..max s t, ‖A r‖)) ∧
      ContDiffOn ℝ 1 Y I.carrier ∧
      ∀ Z : ℝ → E, ContinuousOn Z I.carrier → Z s = ξ →
        (∀ t ∈ I.carrier, HasDerivWithinAt Z (A t (Z t)) I.carrier t) →
        EqOn Z Y I.carrier

/-- The evolution operator in every fixed norm, including non-Euclidean norms.
A finite-dimensional operator is precisely a matrix in a chosen basis. -/
def OperatorEvolution : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] {E : Type u} [NormedAddCommGroup E]
    [NormedSpace 𝕂 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕂 E] [CompleteSpace E]
    (I : TimeInterval) (A : ℝ → E →L[𝕂] E) (s : ℝ),
    s ∈ I.carrier → ContinuousOn A I.carrier →
    ∃ U : ℝ → E →L[𝕂] E, ContinuousOn U I.carrier ∧ U s = 1 ∧
      (∀ t ∈ I.carrier, HasDerivWithinAt U (A t * U t) I.carrier t) ∧
      (∀ t ∈ I.carrier,
        ‖U t‖ ≤ Real.exp (∫ r in min s t..max s t, ‖A r‖)) ∧
      ContDiffOn ℝ 1 U I.carrier ∧
      ∀ V : ℝ → E →L[𝕂] E, ContinuousOn V I.carrier → V s = 1 →
        (∀ t ∈ I.carrier, HasDerivWithinAt V (A t * V t) I.carrier t) →
        EqOn V U I.carrier

/-- Vector IVPs over either ℝ or ℂ, with real time and one-sided endpoints. -/
def VectorExistence : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ)
    (I : TimeInterval) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (s : ℝ) (ξ : Fin n → 𝕂), s ∈ I.carrier → ContinuousOn A I.carrier →
    ∃ Y : ℝ → Fin n → 𝕂, ContinuousOn Y I.carrier ∧ Y s = ξ ∧
      (∀ t ∈ I.carrier, HasDerivWithinAt Y (A t *ᵥ Y t) I.carrier t) ∧
      ContDiffOn ℝ 1 Y I.carrier ∧
      ∀ Z : ℝ → Fin n → 𝕂, ContinuousOn Z I.carrier → Z s = ξ →
        (∀ t ∈ I.carrier, HasDerivWithinAt Z (A t *ᵥ Z t) I.carrier t) →
        EqOn Z Y I.carrier

/-- Rectangular matrix initial data, including empty dimensions. -/
def MatrixExistence : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n r : ℕ)
    (I : TimeInterval) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂)
    (s : ℝ) (ξ : Matrix (Fin n) (Fin r) 𝕂),
    s ∈ I.carrier → ContinuousOn A I.carrier →
    ∃ Y : ℝ → Matrix (Fin n) (Fin r) 𝕂, ContinuousOn Y I.carrier ∧ Y s = ξ ∧
      (∀ t ∈ I.carrier, HasDerivWithinAt Y (A t * Y t) I.carrier t) ∧
      ContDiffOn ℝ 1 Y I.carrier ∧
      ∀ Z : ℝ → Matrix (Fin n) (Fin r) 𝕂, ContinuousOn Z I.carrier → Z s = ξ →
        (∀ t ∈ I.carrier, HasDerivWithinAt Z (A t * Z t) I.carrier t) →
        EqOn Z Y I.carrier

/-- The evolution matrix exists before any canonical choice is made.
The norm here is the induced ℓ∞ operator norm; AlgebraExistence also permits
other compatible normed realizations, and Existence allows arbitrary norms. -/
def EvolutionExistence : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ)
    (I : TimeInterval) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ),
    s ∈ I.carrier → ContinuousOn A I.carrier →
    ∃ U : ℝ → Matrix (Fin n) (Fin n) 𝕂, ContinuousOn U I.carrier ∧ U s = 1 ∧
      (∀ t ∈ I.carrier, HasDerivWithinAt U (A t * U t) I.carrier t) ∧
      (∀ t ∈ I.carrier,
        ‖U t‖ ≤ Real.exp (∫ r in min s t..max s t, ‖A r‖)) ∧
      ContDiffOn ℝ 1 U I.carrier ∧
      ∀ V : ℝ → Matrix (Fin n) (Fin n) 𝕂, ContinuousOn V I.carrier → V s = 1 →
        (∀ t ∈ I.carrier, HasDerivWithinAt V (A t * V t) I.carrier t) →
        EqOn V U I.carrier
/-- Actual evolution matrices and their induced norm bound in every compatible
fixed norm. The equivalence e may change norms and need not be an isometry. -/
def MatrixEvolutionIn : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : (Fin n → 𝕂) ≃L[ℝ] E)
    (I : TimeInterval) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ),
    s ∈ I.carrier → ContinuousOn A I.carrier →
    ∃ U : ℝ → Matrix (Fin n) (Fin n) 𝕂, ContinuousOn U I.carrier ∧ U s = 1 ∧
      (∀ t ∈ I.carrier, HasDerivWithinAt U (A t * U t) I.carrier t) ∧
      (∀ t ∈ I.carrier,
        ‖_root_.D13Unified.Ch07.LinearSystemExistence.matrixOperatorIn e (U t)‖ ≤
          Real.exp (∫ r in min s t..max s t,
            ‖_root_.D13Unified.Ch07.LinearSystemExistence.matrixOperatorIn e (A r)‖)) ∧
      ContDiffOn ℝ 1 U I.carrier ∧
      ∀ V : ℝ → Matrix (Fin n) (Fin n) 𝕂, ContinuousOn V I.carrier → V s = 1 →
        (∀ t ∈ I.carrier, HasDerivWithinAt V (A t * V t) I.carrier t) →
        EqOn V U I.carrier

end Specs.D13Unified.Ch07.LinearSystemExistence
