import Mathlib.Data.Rat.Defs
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.Decomposition

namespace Specs.Alg01SymmetricWitt.Witt.RationalIndex

def binaryPlaneType := QuadraticForm ℚ (ℚ × ℚ)

def binaryPlane : QuadraticForm ℚ (ℚ × ℚ) :=
  (QuadraticMap.sq (R := ℚ)).prod ((-2 : ℚ) • QuadraticMap.sq (R := ℚ))

def rationalFormType := QuadraticForm ℚ ((ℚ × ℚ) × (ℚ × ℚ))

/-- The coordinates are grouped as `((x, y), (u, v))`. -/
def rationalForm : QuadraticForm ℚ ((ℚ × ℚ) × (ℚ × ℚ)) :=
  (Coordinates.hyperbolicPlane ℚ).prod binaryPlane

def binaryPlane_apply : Prop :=
  ∀ u v : ℚ, binaryPlane (u, v) = u ^ 2 - 2 * v ^ 2

def rationalForm_apply : Prop :=
  ∀ x y u v : ℚ, rationalForm ((x, y), (u, v)) = x * y + u ^ 2 - 2 * v ^ 2

def two_not_isSquare : Prop :=
  ¬ IsSquare (2 : ℚ)

def binaryPlane_anisotropic : Prop :=
  binaryPlane.Anisotropic

def binaryPlane_nondegenerate : Prop :=
  binaryPlane.Nondegenerate

def rationalForm_eq_hyperbolic_prod : Prop :=
  rationalForm = (Coordinates.hyperbolicPlane ℚ).prod binaryPlane

def rationalForm_nondegenerate : Prop :=
  rationalForm.Nondegenerate

def rationalForm_wittIndex : Prop :=
  Decomposition.IsWittIndex rationalForm 1

end Specs.Alg01SymmetricWitt.Witt.RationalIndex
