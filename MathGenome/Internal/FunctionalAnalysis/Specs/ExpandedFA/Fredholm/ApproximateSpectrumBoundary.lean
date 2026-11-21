import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachAlgebra.Conventions
import Mathlib.Topology.Sequences

/-! Independent statements for the approximate-point stage of
`fa2:p2:local-spectrum`, paper.tex 10718–10739. The approximate spectrum is the
shared unit-sphere definition; resolvents have the sign (z I - T)⁻¹.
No nonzero-space hypothesis is imposed. -/
namespace Specs.ExpandedFA.Fredholm.ApproximateSpectrumBoundary

open Filter Set
open scoped Topology
open ExpandedFA.BanachAlgebra.Conventions

universe u

def UnitSequence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : X →L[ℂ] X) (z : ℂ),
    z ∈ ApproximatePointSpectrumValue ℂ X T ↔
      ∃ x : ℕ → X, (∀ n, ‖x n‖ = 1) ∧
        Tendsto (fun n => T (x n) - z • x n) atTop (𝓝 0)

def ClosedRangeComplement : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X) (z : ℂ),
    z ∉ ApproximatePointSpectrumValue ℂ X T ↔
      Function.Injective (T - z • (1 : X →L[ℂ] X)) ∧
        IsClosed (Set.range (T - z • (1 : X →L[ℂ] X)))

/-- A quantitative resolvent blow-up bound, valid for each spectral point. -/
def ResolventLowerBound : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X) (z w : ℂ),
    z ∈ AlgebraSpectrumValue ℂ (X →L[ℂ] X) T →
    w ∈ AlgebraResolventSetValue ℂ (X →L[ℂ] X) T →
      1 ≤ ‖w - z‖ * ‖AlgebraResolventValue ℂ (X →L[ℂ] X) T w‖

def BoundaryResolventBlowup : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X) (z : ℂ),
    z ∈ frontier (AlgebraSpectrumValue ℂ (X →L[ℂ] X) T) →
    ∀ w : ℕ → ℂ, (∀ n, w n ∈ AlgebraResolventSetValue ℂ (X →L[ℂ] X) T) →
      Tendsto w atTop (𝓝 z) →
      Tendsto (fun n => ‖AlgebraResolventValue ℂ (X →L[ℂ] X) T (w n)‖) atTop atTop

def BoundaryInclusion : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : X →L[ℂ] X),
    frontier (AlgebraSpectrumValue ℂ (X →L[ℂ] X) T) ⊆
      ApproximatePointSpectrumValue ℂ X T

/-- Intrinsic real approximate spectrum on a real normed space. -/
def RealUnitSequence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X]
    (T : X →L[ℝ] X) (z : ℝ),
    z ∈ ApproximatePointSpectrumValue ℝ X T ↔
      ∃ x : ℕ → X, (∀ n, ‖x n‖ = 1) ∧
        Tendsto (fun n => T (x n) - z • x n) atTop (𝓝 0)

def RealClosedRangeComplement : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : X →L[ℝ] X) (z : ℝ),
    z ∉ ApproximatePointSpectrumValue ℝ X T ↔
      Function.Injective (T - z • (1 : X →L[ℝ] X)) ∧
        IsClosed (Set.range (T - z • (1 : X →L[ℝ] X)))

/-- Boundary is taken in ℝ and the spectrum uses the original real field. -/
def RealBoundaryInclusion : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : X →L[ℝ] X),
    frontier (AlgebraSpectrumValue ℝ (X →L[ℝ] X) T) ⊆
      ApproximatePointSpectrumValue ℝ X T


end Specs.ExpandedFA.Fredholm.ApproximateSpectrumBoundary
