import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.ExponentialTypePolynomialDivision
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionCalculus

/-! Compact-support solvability, `fa2:p4:compact-pde-solvability`.
The operator acts on the actual complex scalar-linear LF distributions.
All dimensions, constant nonzero polynomials, and the zero right hand side
are included. The Fourier normalization is D_j = (2πi)⁻¹ ∂_j. -/
noncomputable section
namespace ExpandedFA.Fourier.CompactSupportPDE
open ExpandedFA.Distributions ExpandedFA.Fourier.PaleyWiener
open ExpandedFA.Fourier.DistributionPaleyWiener
open TopologicalSpace

/-- Normalized coordinate differentiation, with the transpose minus sign. -/
def normalizedPartial {d : ℕ} (i : Fin d) (u : Distribution d) : Distribution d :=
  (-(2 * (Real.pi : ℂ) * Complex.I)⁻¹) • u.comp (testPartialCLM [i])

/-- Transposed ordered coordinate derivatives; the empty word is the identity. -/
def normalizedWord {d : ℕ} : List (Fin d) → Distribution d → Distribution d
  | [], u => u
  | i :: w, u => normalizedWord w (normalizedPartial i u)

/-- The genuine finite sum of normalized distributional multi-index derivatives. -/
def polynomialOperator {d : ℕ} (P : MvPolynomial (Fin d) ℂ)
    (u : Distribution d) : Distribution d :=
  P.support.sum fun α => P.coeff α • normalizedWord (multiIndexWord (fun j => α j)) u

end ExpandedFA.Fourier.CompactSupportPDE

namespace Specs.ExpandedFA.Fourier.CompactSupportPDESolvability
open Set _root_.ExpandedFA.Fourier.PaleyWiener
open _root_.ExpandedFA.Fourier.DistributionPaleyWiener
open _root_.ExpandedFA.Fourier.CompactSupportPDE

/-- Entire divisibility is equality at every complex frequency. -/
def solvabilityType : Prop := ∀ (d : ℕ) (P : MvPolynomial (Fin d) ℂ), P ≠ 0 →
  ∀ v : Distribution d, IsCompact (euclideanSupport v) →
  ((∃ u : Distribution d, IsCompact (euclideanSupport u) ∧ polynomialOperator P u = v) ↔
    ∃ G : ComplexEuclidean d → ℂ, Differentiable ℂ G ∧
      ∀ z, fourierLaplace v z = MvPolynomial.eval (fun j => z j) P * G z)

/-- Uniqueness among all compactly supported solutions, without a prescribed
common support and including a zero right hand side. -/
def uniquenessType : Prop := ∀ (d : ℕ) (P : MvPolynomial (Fin d) ℂ), P ≠ 0 →
  ∀ u w : Distribution d, IsCompact (euclideanSupport u) →
    IsCompact (euclideanSupport w) → polynomialOperator P u = polynomialOperator P w → u = w

/-- Every compact solution has the sharp convex hull support inclusion. -/
def supportType : Prop := ∀ (d : ℕ) (P : MvPolynomial (Fin d) ℂ), P ≠ 0 →
  ∀ u v : Distribution d, IsCompact (euclideanSupport u) →
    IsCompact (euclideanSupport v) → polynomialOperator P u = v →
      euclideanSupport u ⊆ convexHull ℝ (euclideanSupport v)

/-- The zero case is stated without a support function of the empty set. -/
def zeroType : Prop := ∀ (d : ℕ) (P : MvPolynomial (Fin d) ℂ), P ≠ 0 →
  polynomialOperator P (0 : Distribution d) = 0 ∧
    euclideanSupport (0 : Distribution d) = ∅ ∧
    ∀ u : Distribution d, IsCompact (euclideanSupport u) → polynomialOperator P u = 0 → u = 0

end Specs.ExpandedFA.Fourier.CompactSupportPDESolvability
