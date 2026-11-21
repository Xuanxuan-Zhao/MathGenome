import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.Plancherel
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-! The complex L² Fourier transform with phase exp(-2πixξ), on the
one-dimensional real Euclidean space. The diagonal ℓᵖ clause of the source
proposition belongs to the separate DiagonalLpSpectrum goal. -/
noncomputable section
open MeasureTheory
open scoped ComplexInnerProductSpace
namespace ExpandedFA.Models.FourierFourPointSpectrum
open ExpandedFA.Fourier

abbrev H := L2 1

def fourier : H →L[ℂ] H := (l2Fourier 1).toContinuousLinearEquiv.toContinuousLinearMap

def root (j : Fin 4) : ℂ := ![1, -1, Complex.I, -Complex.I] j

def projection (j : Fin 4) : H →L[ℂ] H :=
  (1 / 4 : ℂ) • ∑ k ∈ Finset.range 4, ((root j)⁻¹ ^ k) • fourier ^ k

def eigenspace (j : Fin 4) : Submodule ℂ H :=
  Module.End.eigenspace fourier.toLinearMap (root j)

namespace Spec

/-- The canonical one-coordinate model is unitarily intertwined with the
Fourier transform on functions of an actual real variable. -/
def RealCoordinateBridge : Prop :=
  ∃ (e : ℝ ≃ₗᵢ[ℝ] Euclidean 1)
    (U : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] H),
    (∀ f, (U f : Euclidean 1 → ℂ) =ᵐ[volume] (f : ℝ → ℂ) ∘ e.symm) ∧
    ∀ f, U (Lp.fourierTransformₗᵢ ℝ ℂ f) = fourier (U f)

def FourthPower : Prop := fourier ^ 4 = 1

def ProjectionIdentities : Prop :=
  (∑ j : Fin 4, projection j) = 1 ∧
  (∀ j, fourier * projection j = root j • projection j) ∧
  (∀ j, projection j * projection j = projection j) ∧
  (∀ j k, j ≠ k → projection j * projection k = 0) ∧
  (∀ j, IsSelfAdjoint (projection j)) ∧
  (∀ j, LinearMap.range (projection j).toLinearMap = eigenspace j)

/-- Every vector has a unique sum of components in the four eigenspaces;
these subspaces are pairwise orthogonal and the displayed polynomials give
the components. This also includes closedness of all four subspaces. -/
def OrthogonalDecomposition : Prop :=
  (∀ j, IsClosed (eigenspace j : Set H)) ∧
  (∀ j k, j ≠ k → ∀ x ∈ eigenspace j, ∀ y ∈ eigenspace k, inner ℂ x y = 0) ∧
  ∀ f : H, (∀ j, projection j f ∈ eigenspace j) ∧
    (∑ j : Fin 4, projection j f) = f ∧
    ∀ v : Fin 4 → H, (∀ j, v j ∈ eigenspace j) → (∑ j, v j) = f →
      ∀ j, v j = projection j f

/-- All four roots actually occur; there are no conditional eigenvectors. -/
def NonzeroEigenspaces : Prop :=
  ∀ j : Fin 4, ∃ f : H, f ≠ 0 ∧ fourier f = root j • f

def ExactSpectrum : Prop := spectrum ℂ fourier = {1, -1, Complex.I, -Complex.I}

end Spec
end ExpandedFA.Models.FourierFourPointSpectrum
