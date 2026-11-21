import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.LinearSystemExistence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Evolution matrices for paper.tex, d13:07:fundamental.
Time is real for both scalar fields. The actual interval is retained in every
calculus assertion. Matrices carry the induced ℓ∞ operator norm. `NormBoundIn`
also gives the estimate in any fixed real normed realization of the state space.
The choice defining U asks only for a normalized homogeneous linear solution;
its existence is established from the linear-system prerequisite in the proof
module. No composition, invertibility, or derivative-in-s certificate is assumed.
-/
noncomputable section
open Set MeasureTheory
open scoped Matrix Matrix.Norms.Operator

namespace D13Unified.Ch07.EvolutionMatrix
variable {𝕂 : Type} [RCLike 𝕂] {n : ℕ}

/-- The elementary normalized IVP used by the canonical choice. -/
def NormalizedSolution (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ)
    (Y : ℝ → Matrix (Fin n) (Fin n) 𝕂) : Prop :=
  ContinuousOn Y I.carrier ∧ Y s = 1 ∧
    ∀ t ∈ I.carrier, HasDerivWithinAt Y (A t * Y t) I.carrier t

/-- Canonical evolution matrix. Only values at times in I under continuity of
A are used. Epsilon is specified using the proved upstream existence theorem,
not by postulating an evolution matrix or its algebraic properties. -/
def U (I : TimeInterval) (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (t s : ℝ) :
    Matrix (Fin n) (Fin n) 𝕂 :=
  (Classical.epsilon (NormalizedSolution I A s)) t

/-- An invertible C¹ matrix solution on its actual interval, including its
one-sided derivatives at included endpoints. -/
def IsFundamentalMatrixOn (I : TimeInterval)
    (A X : ℝ → Matrix (Fin n) (Fin n) 𝕂) : Prop :=
  ContDiffOn ℝ 1 X I.carrier ∧
    (∀ t ∈ I.carrier, HasDerivWithinAt X (A t * X t) I.carrier t) ∧
    ∀ t ∈ I.carrier, IsUnit (X t)
end D13Unified.Ch07.EvolutionMatrix

namespace Specs.D13Unified.Ch07.EvolutionMatrix
open _root_.D13Unified _root_.D13Unified.Ch07.EvolutionMatrix
universe u

/-- Explicit expected values of the two shared canonical definitions. -/
def UType := ∀ {𝕂 : Type} [RCLike 𝕂] {n : ℕ}, TimeInterval →
  (ℝ → Matrix (Fin n) (Fin n) 𝕂) → ℝ → ℝ → Matrix (Fin n) (Fin n) 𝕂

def UValue : UType := fun I A t s =>
  (Classical.epsilon (fun Y => ContinuousOn Y I.carrier ∧ Y s = 1 ∧
    ∀ r ∈ I.carrier, HasDerivWithinAt Y (A r * Y r) I.carrier r)) t

def FundamentalType := ∀ {𝕂 : Type} [RCLike 𝕂] {n : ℕ}, TimeInterval →
  (ℝ → Matrix (Fin n) (Fin n) 𝕂) → (ℝ → Matrix (Fin n) (Fin n) 𝕂) → Prop

def FundamentalValue : FundamentalType := fun I A X =>
  ContDiffOn ℝ 1 X I.carrier ∧
    (∀ t ∈ I.carrier, HasDerivWithinAt X (A t * X t) I.carrier t) ∧
    ∀ t ∈ I.carrier, IsUnit (X t)

/-- The shared choice has precisely the normalized-IVP defining formula.
The implementation verifies this equality; the shared definition itself is
owned by this independent interface rather than submitted as a proof target. -/
def UDefinition : Prop :=
  @_root_.D13Unified.Ch07.EvolutionMatrix.U = @UValue

/-- The shared fundamental-matrix predicate has exactly its stated meaning. -/
def FundamentalDefinition : Prop :=
  @_root_.D13Unified.Ch07.EvolutionMatrix.IsFundamentalMatrixOn = @FundamentalValue

/-- Existence, normalization, regularity, sharp growth, and uniqueness on I. -/
def Evolution : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ) (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ),
    s ∈ I.carrier → ContinuousOn A I.carrier →
    ContinuousOn (fun t => U I A t s) I.carrier ∧ U I A s s = 1 ∧
    (∀ t ∈ I.carrier,
      HasDerivWithinAt (fun r => U I A r s) (A t * U I A t s) I.carrier t) ∧
    (∀ t ∈ I.carrier,
      ‖U I A t s‖ ≤ Real.exp (∫ r in min s t..max s t, ‖A r‖)) ∧
    ContDiffOn ℝ 1 (fun t => U I A t s) I.carrier ∧
    ∀ V : ℝ → Matrix (Fin n) (Fin n) 𝕂, ContinuousOn V I.carrier → V s = 1 →
      (∀ t ∈ I.carrier, HasDerivWithinAt V (A t * V t) I.carrier t) →
      EqOn V (fun t => U I A t s) I.carrier

/-- The same canonical matrices in every compatible fixed norm. -/
def NormBoundIn : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (e : (Fin n → 𝕂) ≃L[ℝ] E) (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ),
    s ∈ I.carrier → ContinuousOn A I.carrier → ∀ t ∈ I.carrier,
      ‖_root_.D13Unified.Ch07.LinearSystemExistence.matrixOperatorIn e (U I A t s)‖ ≤
        Real.exp (∫ r in min s t..max s t,
          ‖_root_.D13Unified.Ch07.LinearSystemExistence.matrixOperatorIn e (A r)‖)

def Composition : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ) (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂), ContinuousOn A I.carrier →
    ∀ r ∈ I.carrier, ∀ s ∈ I.carrier, ∀ t ∈ I.carrier,
      U I A t r * U I A r s = U I A t s

def Inverse : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ) (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂), ContinuousOn A I.carrier →
    ∀ s ∈ I.carrier, ∀ t ∈ I.carrier,
      IsUnit (U I A t s) ∧ (U I A t s)⁻¹ = U I A s t

def StartingTimeDerivative : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ) (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂), ContinuousOn A I.carrier →
    ∀ t ∈ I.carrier, ∀ s ∈ I.carrier,
      HasDerivWithinAt (fun r => U I A t r) (-U I A t s * A s) I.carrier s

/-- Explicit converse for an arbitrary invertible constant. -/
def FundamentalMultiplication : Prop :=
  ∀ {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ),
    s ∈ I.carrier → ContinuousOn A I.carrier →
    ∀ C : Matrix (Fin n) (Fin n) 𝕂, IsUnit C →
      IsFundamentalMatrixOn I A (fun t => U I A t s * C)

/-- Every constant in such a representation is X(s), with no invertibility
assumption needed for this evaluation identity. -/
def FundamentalConstant : Prop :=
  ∀ {𝕂 : Type} [RCLike 𝕂] {n : ℕ} (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂) (s : ℝ),
    s ∈ I.carrier → ContinuousOn A I.carrier →
    ∀ (X : ℝ → Matrix (Fin n) (Fin n) 𝕂) (C : Matrix (Fin n) (Fin n) 𝕂),
      EqOn X (fun t => U I A t s * C) I.carrier → C = X s

/-- The unique constant is exactly X(s); conversely every invertible constant
produces a fundamental matrix. Equality is required only on the real domain I. -/
def FundamentalCharacterization : Prop :=
  ∀ (𝕂 : Type) [RCLike 𝕂] (n : ℕ) (I : TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) 𝕂), ContinuousOn A I.carrier →
    ∀ s ∈ I.carrier, ∀ X : ℝ → Matrix (Fin n) (Fin n) 𝕂,
      IsFundamentalMatrixOn I A X ↔
        ∃! C : Matrix (Fin n) (Fin n) 𝕂,
          IsUnit C ∧ EqOn X (fun t => U I A t s * C) I.carrier

end Specs.D13Unified.Ch07.EvolutionMatrix
