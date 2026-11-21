import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.DistributionPaleyWiener
import Mathlib.Algebra.MvPolynomial.Basic

/-! Independent statement of `fa2:p4:polynomial-division`, paper.tex:17516–17543.
The polynomial is a genuine multivariate complex polynomial, evaluated on the
same Euclidean complex frequency space as the Paley--Wiener estimates.
No positive degree, positive dimension, or nonempty interior is assumed. -/
namespace Specs.ExpandedFA.Fourier.ExponentialTypePolynomialDivision
open Set
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.Fourier.PaleyWiener
open _root_.ExpandedFA.Fourier.DistributionPaleyWiener

/-- Dividing an entire function by a nonzero polynomial preserves the exact
compact convex exponential type. The constant and polynomial power may change. -/
def polynomialDivisionType : Prop :=
  ∀ (d : ℕ) (K : Set (Euclidean d)),
    K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ (P : MvPolynomial (Fin d) ℂ), P ≠ 0 →
    ∀ (G : ComplexEuclidean d → ℂ), Differentiable ℂ G →
      PolynomialExponentialType K (fun z => MvPolynomial.eval (fun j => z j) P * G z) →
      PolynomialExponentialType K G

end Specs.ExpandedFA.Fourier.ExponentialTypePolynomialDivision
