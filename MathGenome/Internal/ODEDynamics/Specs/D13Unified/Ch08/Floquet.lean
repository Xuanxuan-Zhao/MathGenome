import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.Translation
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch08.MatrixLogarithm
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch07.ExponentialCalculus

/-! The complex Floquet theorem (paper.tex, d13:08:floquet).
Matrices with `IsUnit` express GL(n,ℂ). Regularity is in real time.
The solution equivalence retains the actual interval and its endpoint convention.
The real specialization uses the entrywise inclusion, with complex factors. -/
noncomputable section
open scoped Matrix Matrix.Norms.Operator

namespace D13Unified.Ch08.Floquet

/-- Classical complex linear solutions, with one-sided derivatives if an
endpoint is included. Ambient representatives are only constrained on I. -/
def IsLinearSolutionOn {n : ℕ} (I : D13Unified.TimeInterval)
    (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (y : ℝ → Fin n → ℂ) : Prop :=
  ContDiffOn ℝ 1 y I.carrier ∧
    ∀ t ∈ I.carrier, HasDerivWithinAt y (A t *ᵥ y t) I.carrier t

/-- All conclusions for the same pair of Floquet factors. -/
def Factors {n : ℕ} (A X : ℝ → Matrix (Fin n) (Fin n) ℂ) (T : ℝ)
    (B : Matrix (Fin n) (Fin n) ℂ) (P : ℝ → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ContDiff ℝ 1 P ∧ (∀ t, IsUnit (P t)) ∧ Function.Periodic P T ∧ P 0 = 1 ∧
    (∀ t, X t = P t * Specs.D13Unified.Ch07.MatrixExponential.exponentialValue B t) ∧
    (∀ t, HasDerivAt P (A t * P t - P t * B) t) ∧
    ∀ (I : D13Unified.TimeInterval) (y : ℝ → Fin n → ℂ),
      IsLinearSolutionOn I A (fun t => P t *ᵥ y t) ↔
        IsLinearSolutionOn I (fun _ => B) y

end D13Unified.Ch08.Floquet

namespace Specs.D13Unified.Ch08.Floquet
open _root_.D13Unified.Ch08.Floquet
open Specs.D13Unified.Ch08.Monodromy

/-- Arbitrary finite dimension, positive period, and only continuity of A. -/
def Representation : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℂ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    ∃ B P, Factors A (principalMatrixValue A) T B P

/-- The principal matrix for real A is actually the real principal matrix
included entrywise in ℂ, rather than an unrelated complex solution. -/
def RealRepresentation : Prop :=
  ∀ (n : ℕ) (A : ℝ → Matrix (Fin n) (Fin n) ℝ) (T : ℝ),
    Continuous A → 0 < T → Function.Periodic A T →
    ∃ B P, Factors (fun t => complexifyValue (A t))
      (fun t => complexifyValue (principalMatrixValue A t)) T B P

end Specs.D13Unified.Ch08.Floquet
