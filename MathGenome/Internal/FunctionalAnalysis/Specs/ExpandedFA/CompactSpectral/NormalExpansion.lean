import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.CompactSpectral.NormalEigenspaces
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-! Independent statements for the complex expansion stage of
`fa2:p2:compact-spectral`, paper.tex, chapter Compact Hilbert operators.
No separability, positive dimension, or infinite-spectrum assumption is made.
Finite sets may contain scalars that are not eigenvalues: their projections
are zero. The real supremum of an empty tail is zero.
-/
noncomputable section
namespace ExpandedFA.CompactSpectral.NormalExpansion.Spec
universe u
open Filter
open scoped Topology InnerProductSpace
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Ambient orthogonal projection onto the closed eigenspace. -/
def eigenProjection (N : H →L[ℂ] H) (α : ℂ) : H →L[ℂ] H :=
  letI : CompleteSpace (Module.End.eigenspace N.toLinearMap α) :=
    (ContinuousLinearMap.isClosed_eigenspace N α).completeSpace_coe
  (Module.End.eigenspace N.toLinearMap α).starProjection

def spectralSum (N : H →L[ℂ] H) (s : Finset ℂ) : H →L[ℂ] H :=
  ∑ α ∈ s, α • eigenProjection N α

def nonzeroEigenvalues (N : H →L[ℂ] H) : Set ℂ :=
  {α | α ≠ 0 ∧ ∃ x : H, x ≠ 0 ∧ N x = α • x}

def tailModuli (N : H →L[ℂ] H) (s : Finset ℂ) : Set ℝ :=
  (fun α : ℂ => ‖α‖) '' (nonzeroEigenvalues N \ (s : Set ℂ))

def nonzeroSpan (N : H →L[ℂ] H) : Submodule ℂ H :=
  (⨆ α : {α : ℂ // α ≠ 0}, Module.End.eigenspace N.toLinearMap α.val).topologicalClosure

/-- The kernel and closed nonzero spectral span are complementary and orthogonal. -/
def Decomposition : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap → IsStarNormal N →
    nonzeroSpan N = N.ker.orthogonal ∧ IsCompl N.ker (nonzeroSpan N)

/-- Exact error of every finite spectral truncation, including the empty tail. -/
def TailNorm : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap → IsStarNormal N →
    ∀ s : Finset ℂ, ‖N - spectralSum N s‖ = sSup (tailModuli N s)

/-- Unconditional convergence of finite spectral sums in operator norm. -/
def OperatorExpansion : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap → IsStarNormal N →
    HasSum (fun α : ℂ => α • eigenProjection N α) N

/-- The vector expansion, with the zero scalar explicitly omitted. -/
def VectorExpansion : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap → IsStarNormal N →
    ∀ x : H, HasSum (fun α : {α : ℂ // α ≠ 0} => α.val • eigenProjection N α.val x) (N x)

/-- Finite truncations can be taken in decreasing order of modulus (ties may
be taken together). They exhaust the nonzero spectrum and converge in norm. -/
def OrderedExpansion : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (N : H →L[ℂ] H),
    Compactness.DefinitionsSpec.IsCompactLinearMapValue N.toLinearMap → IsStarNormal N →
    ∃ s : ℕ → Finset ℂ, Monotone s ∧
      (∀ n, (s n : Set ℂ) ⊆ nonzeroEigenvalues N) ∧
      (∀ α ∈ nonzeroEigenvalues N, ∃ n, α ∈ s n) ∧
      (∀ n α, α ∈ s n → ∀ β ∈ nonzeroEigenvalues N, β ∉ s n → ‖β‖ ≤ ‖α‖) ∧
      Tendsto (fun n => spectralSum N (s n)) atTop (𝓝 N)
end ExpandedFA.CompactSpectral.NormalExpansion.Spec
