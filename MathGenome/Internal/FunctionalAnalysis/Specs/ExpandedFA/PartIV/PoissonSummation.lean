import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.SchwartzFourierConvention
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Independent statements for paper.tex:18697–18722, fa2:p4:poisson-summation.
The integer lattice is embedded coordinatewise in the established Euclidean space.
No positive-dimensional premise is imposed. Invertibility is exactly nonzero determinant.
The Fourier transform is the shared transform with exponent -2πi〈x,ξ〉. -/

namespace ExpandedFA.PartIV.PoissonSummation
open ExpandedFA.Fourier

/-- The usual inclusion ℤ^d → ℝ^d. -/
def integerPoint {d : ℕ} (n : Fin d → ℤ) : Euclidean d :=
  WithLp.toLp 2 (fun i => (n i : ℝ))

/-- Matrix multiplication on Euclidean space with its standard coordinate basis. -/
noncomputable def matrixAction {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (x : Euclidean d) : Euclidean d := A.toEuclideanLin x

end ExpandedFA.PartIV.PoissonSummation

namespace Specs.ExpandedFA.PartIV.PoissonSummation
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.PartIV.PoissonSummation

/-- Absolute convergence of both series and the standard Poisson formula. -/
def StandardFormula : Prop := ∀ (d : ℕ) (f : Schwartz ℂ d),
  Summable (fun n : Fin d → ℤ => ‖f (integerPoint n)‖) ∧
  Summable (fun n : Fin d → ℤ => ‖schwartzFourier f (integerPoint n)‖) ∧
  (∑' n : Fin d → ℤ, f (integerPoint n)) =
    ∑' n : Fin d → ℤ, schwartzFourier f (integerPoint n)

/-- The full matrix formula, including absolute convergence on the lattice and its dual. -/
def LatticeFormula : Prop := ∀ (d : ℕ) (f : Schwartz ℂ d)
    (A : Matrix (Fin d) (Fin d) ℝ), A.det ≠ 0 →
  Summable (fun n : Fin d → ℤ => ‖f (matrixAction A (integerPoint n))‖) ∧
  Summable (fun n : Fin d → ℤ =>
    ‖schwartzFourier f (matrixAction A⁻¹.transpose (integerPoint n))‖) ∧
  (∑' n : Fin d → ℤ, f (matrixAction A (integerPoint n))) =
    |A.det|⁻¹ • (∑' n : Fin d → ℤ,
      schwartzFourier f (matrixAction A⁻¹.transpose (integerPoint n)))

end Specs.ExpandedFA.PartIV.PoissonSummation
