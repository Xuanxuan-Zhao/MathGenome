import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.CharP.Invertible
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.LinearAlgebra.QuadraticForm.TensorProduct
import MathGenome.Internal.LinearAlgebraSupplement.Specs.Alg01SymmetricWitt.Witt.RationalIndex

namespace Specs.Alg01SymmetricWitt.Witt.WittBaseChange

open scoped TensorProduct

noncomputable section

/-- The subfield of the reals generated over the rationals by the positive square root of two. -/
def sqrtTwoExtension : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ {Real.sqrt 2}

local notation "K" => (sqrtTwoExtension : Type)

def sqrtTwoExtensionType := IntermediateField ℚ ℝ

def sqrtTwoType := K

def sqrtTwo : K :=
  ⟨Real.sqrt 2, IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)⟩

def sqrtTwo_sq : Prop :=
  sqrtTwo ^ 2 = 2

/-- The binary summand in extension-field coordinates. -/
def coordinateBinaryForm : QuadraticForm K (K × K) :=
  (QuadraticMap.sq (R := K)).prod ((-2 : K) • QuadraticMap.sq (R := K))

def coordinateBinaryFormType := QuadraticForm K (K × K)

def coordinateForm : QuadraticForm K ((K × K) × (K × K)) :=
  (Coordinates.hyperbolicPlane K).prod coordinateBinaryForm

def coordinateFormType := QuadraticForm K ((K × K) × (K × K))

def coordinateForm_apply : Prop :=
  ∀ x y u v : K, coordinateForm ((x, y), (u, v)) = x * y + u ^ 2 - 2 * v ^ 2

/-- The scalar-extended form is the coordinate polynomial under the canonical
extension of the rational coordinates. -/
def baseChangeCoordinates : Prop :=
  ∃ e : (RationalIndex.rationalForm.baseChange K).IsometryEquiv coordinateForm,
    ∀ (a : K) (x y u v : ℚ),
      e (a ⊗ₜ[ℚ] ((x, y), (u, v))) =
        ((a * algebraMap ℚ K x, a * algebraMap ℚ K y),
          (a * algebraMap ℚ K u, a * algebraMap ℚ K v))

def binaryPlaneSplits : Prop :=
  ∃ e : coordinateBinaryForm.IsometryEquiv (Coordinates.hyperbolicPlane K),
    ∀ u v : K, e (u, v) = (u + sqrtTwo * v, u - sqrtTwo * v)

def baseChangeHyperbolic : Prop :=
  (RationalIndex.rationalForm.baseChange K).Equivalent (Coordinates.hyperbolicSum K 2)

def wittIndexComparison : Prop :=
  Decomposition.IsWittIndex RationalIndex.rationalForm 1 ∧
    Decomposition.IsWittIndex (RationalIndex.rationalForm.baseChange K) 2

end

end Specs.Alg01SymmetricWitt.Witt.WittBaseChange
