import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.InverseStability
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Matrix.Normed

/-! Independent statements of `d04:04:matrix-inversion`.
The domain is the open set of invertible real matrices in the shared column
representation. Smoothness is the paper's recursive C^r condition for every
finite r. The derivative is on the entire ambient matrix space, not just on
invertible increments. Matrices carry the Euclidean Frobenius norm, as in the
shared bilinear rules. All dimensions, including zero, are quantified. -/
noncomputable section
open Set
open scoped Matrix.Norms.Frobenius
namespace Specs.D04.C04.MatrixInversion
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

def matrix_inversion_mapsToType : Prop :=
  ∀ n : ℕ, MapsTo (fun A : Matrix (Fin n) (Fin n) ℝ => A⁻¹)
    {A | IsUnit A} {A | IsUnit A}

def matrix_inversion_smoothType : Prop :=
  ∀ n : ℕ, SmoothOn {A : Matrix (Fin n) (Fin n) ℝ | IsUnit A}
    (fun A => A⁻¹)

def matrix_inversion_hasTotalDerivativeType : Prop :=
  ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ), IsUnit A →
    ∃ L : Matrix (Fin n) (Fin n) ℝ →L[ℝ] Matrix (Fin n) (Fin n) ℝ,
      HasTotalDerivative {B | IsUnit B} (fun B => B⁻¹) L A ∧
      ∀ H, L H = -(A⁻¹ * H * A⁻¹)

/-- The same differential in standard column linear maps, explicitly retaining
the order of both inverse factors and the increment. -/
def matrix_inversion_column_derivativeType : Prop :=
  ∀ {n : ℕ} (A H : Matrix (Fin n) (Fin n) ℝ), IsUnit A →
    matrixLinearEquiv n n (totalDerivative (fun B : Matrix (Fin n) (Fin n) ℝ => B⁻¹) A H) =
      -((matrixLinearEquiv n n A⁻¹).comp (matrixLinearEquiv n n H)).comp
        (matrixLinearEquiv n n A⁻¹)

end Specs.D04.C04.MatrixInversion
