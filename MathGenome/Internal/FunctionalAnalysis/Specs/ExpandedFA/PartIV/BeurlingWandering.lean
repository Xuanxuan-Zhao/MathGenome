import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyDisk
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.Dimension.Finite

/-! The geometric stage of Beurling's theorem, paper.tex:18813–18825.
All objects use the canonical disk Hardy space and its normalized Haar boundary
map from the upstream Specs. No analytic or geometric conclusion is assumed. -/
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
namespace ExpandedFA.PartIV.BeurlingWanderingSpec
open HardyDiskSpec

/-- Invariance under the actual coefficient shift (multiplication by z). -/
def ShiftInvariant (M : Submodule ℂ H2) : Prop := ∀ f ∈ M, shift f ∈ M

def shiftRange (M : Submodule ℂ H2) : Submodule ℂ H2 := M.map shift.toLinearMap

def wandering (M : Submodule ℂ H2) : Submodule ℂ H2 := M ⊓ (shiftRange M)ᗮ

def ShiftClosed : Prop := ∀ M : Submodule ℂ H2,
  IsClosed (M : Set H2) → IsClosed (shiftRange M : Set H2)

def ShiftProper : Prop := ∀ M : Submodule ℂ H2,
  M ≠ ⊥ → ShiftInvariant M → shiftRange M < M

def WanderingUnit : Prop := ∀ M : Submodule ℂ H2,
  IsClosed (M : Set H2) → M ≠ ⊥ → ShiftInvariant M →
  ∃ θ : H2, θ ∈ wandering M ∧ ‖θ‖ = 1

def WanderingDimension : Prop := ∀ M : Submodule ℂ H2,
  IsClosed (M : Set H2) → M ≠ ⊥ → ShiftInvariant M →
  Module.rank ℂ (wandering M) = 1

def WanderingBoundaryUnit : Prop := ∀ (M : Submodule ℂ H2),
  IsClosed (M : Set H2) → M ≠ ⊥ → ShiftInvariant M →
  ∀ θ ∈ wandering M, ‖θ‖ = 1 →
    ∀ᵐ t ∂AddCircle.haarAddCircle, ‖boundary θ t‖ = 1

def WanderingInner : Prop := ∀ (M : Submodule ℂ H2),
  IsClosed (M : Set H2) → M ≠ ⊥ → ShiftInvariant M →
  ∀ θ ∈ wandering M, ‖θ‖ = 1 → IsInner θ

def WanderingDiskBound : Prop := ∀ (M : Submodule ℂ H2),
  IsClosed (M : Set H2) → M ≠ ⊥ → ShiftInvariant M →
  ∀ θ ∈ wandering M, ‖θ‖ = 1 → ∀ z ∈ disk, ‖eval θ z‖ ≤ 1

end ExpandedFA.PartIV.BeurlingWanderingSpec
