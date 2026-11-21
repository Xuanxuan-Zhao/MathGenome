import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Adjoint
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
Independent statements for the complex eigenspace stage of
`paper.tex:11267–11313`, `fa2:p2:compact-spectral`.

The Hilbert space is arbitrary: no countability or separability assumption is
made on it or on its kernel. Normality is the native equality N*N = NN*;
compactness is the shared compact-closure condition in the original space.
The kernel identity, orthogonality, and reduction include the zero eigenvalue.
Only the finite-dimensionality assertion excludes zero.
-/

namespace ExpandedFA.CompactSpectral.NormalEigenspaces.Spec

universe u
open scoped InnerProductSpace

/-- Equality of the scalar-shift kernels, with the conjugated adjoint shift. -/
def ShiftKernels : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N → ∀ α : ℂ,
    (N - α • 1).ker = (N.adjoint - star α • 1).ker

/-- The same statement on vectors, in both directions. -/
def AdjointEigenvectors : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N → ∀ (α : ℂ) (x : H),
    N x = α • x ↔ N.adjoint x = star α • x

/-- Orthogonality of all distinct eigenspaces, including the kernel. -/
def OrthogonalEigenspaces : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N →
    OrthogonalFamily ℂ (fun α : ℂ => Module.End.eigenspace N.toLinearMap α)
      (fun α => (Module.End.eigenspace N.toLinearMap α).subtypeₗᵢ)

/-- Each eigenspace and its orthogonal complement are invariant under N. -/
def ReducingEigenspaces : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H), IsStarNormal N → ∀ α : ℂ,
    Hilbert.Adjoint.Spec.ReducingSubspaceValue ℂ H
      (Module.End.eigenspace N.toLinearMap α) N

/-- The geometric eigenspace is finite-dimensional for every nonzero scalar.
This stronger compact-map statement does not require normality. -/
def FiniteDimensionalEigenspaces : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap →
    ∀ α : ℂ, α ≠ 0 → FiniteDimensional ℂ (Module.End.eigenspace N.toLinearMap α)

/-- There are finitely many eigenvalues outside every disk about zero. -/
def FiniteAwayFromZero : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap →
    ∀ ε : ℝ, 0 < ε →
    {α : ℂ | (∃ x : H, x ≠ 0 ∧ N x = α • x) ∧ ε ≤ ‖α‖}.Finite

/-- Only the nonzero eigenvalues are asserted countable, not the ambient
Hilbert dimension or the dimension of the kernel. -/
def CountableNonzeroEigenvalues : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap →
    {α : ℂ | α ≠ 0 ∧ ∃ x : H, x ≠ 0 ∧ N x = α • x}.Countable

end ExpandedFA.CompactSpectral.NormalEigenspaces.Spec
