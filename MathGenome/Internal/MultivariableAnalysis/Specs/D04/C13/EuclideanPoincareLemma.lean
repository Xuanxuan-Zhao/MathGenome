import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.HomotopyOperatorRegularity
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.ClosedAndExactForms
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.PullbackCalculus

/-! Independent statement of d04:13:poincare and d04:13:homotopy-example.
All equalities are restricted to the original open domain. The primitive is
exactly the shared radial proper-integral operator. No Stokes theorem is used. -/
noncomputable section
open Set
namespace Specs.D04.C13.EuclideanPoincareLemma
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C13.ClosedAndExactForms.Model
open Specs.D04.C13.HomotopyOperatorRegularity.Model
open Specs.D04.C13.PullbackCalculus.Model

/-- The C¹ part of the main theorem, recorded separately for incremental work. -/
def homotopy_C1Type : Prop :=
  ∀ {n k : ℕ} {U : Set (E n)} {a : E n} (ω : FormField n (k+1)),
    IsOpen U → a ∈ U → StarConvex ℝ a U → IsCrForm (some 1) U ω →
      IsCrForm (some 1) U (homotopyOperator a ω)

/-- Regularity of the specified operator, including order zero and smoothness. -/
def homotopy_regularityType : Prop :=
  ∀ {n k : ℕ} {U : Set (E n)} {a : E n} (ω : FormField n (k+1)) (r : Option ℕ),
    IsOpen U → a ∈ U → StarConvex ℝ a U → IsCrForm r U ω →
      IsCrForm r U (homotopyOperator a ω)

/-- Positive degree is indexed by k+1; no negative-degree forms occur. -/
def homotopy_identityType : Prop :=
  ∀ {n k : ℕ} {U : Set (E n)} {a : E n} (ω : FormField n (k+1)),
    IsOpen U → a ∈ U → StarConvex ℝ a U → IsCrForm (some 1) U ω →
    IsCrForm (some 1) U (homotopyOperator a ω) ∧
    ∀ x ∈ U, exteriorDerivative (homotopyOperator a ω) x +
      homotopyOperator a (exteriorDerivative ω) x = ω x

def poincare_primitiveType : Prop :=
  ∀ {n k : ℕ} {U : Set (E n)} {a : E n} (ω : FormField n (k+1)),
    IsOpen U → a ∈ U → StarConvex ℝ a U → IsClosedForm U ω →
    IsCrForm (some 1) U (homotopyOperator a ω) ∧
      EqOn (exteriorDerivative (homotopyOperator a ω)) ω U ∧ IsExactForm U ω

/-- Includes all finite r ≥ 1 and infinite regularity (represented by none). -/
def poincare_primitive_isCrType : Prop :=
  ∀ {n k : ℕ} {U : Set (E n)} {a : E n} (ω : FormField n (k+1)) (r : Option ℕ),
    (∀ s, r = some s → 1 ≤ s) → IsOpen U → a ∈ U → StarConvex ℝ a U →
    IsClosedForm U ω → IsCrForm r U ω →
    IsCrForm r U (homotopyOperator a ω) ∧
      EqOn (exteriorDerivative (homotopyOperator a ω)) ω U

/-- The degree-zero identity is equality of scalar covectors. -/
def homotopy_functionType : Prop :=
  ∀ {n : ℕ} {U : Set (E n)} {a : E n} (f : E n → ℝ),
    IsOpen U → a ∈ U → StarConvex ℝ a U → CrOn 1 U f →
    ∀ x ∈ U, homotopyOperator a
      (exteriorDerivative (fun y => scalarCovector (V := E n) (f y))) x =
      scalarCovector (f x - f a)

namespace Model
/-- z dx ∧ dz, with zero-based coordinate indices 0 and 2. -/
def exampleForm : FormField 3 2 :=
  fun x => x 2 • wedge (coordinateOneForm 3 0) (coordinateOneForm 3 2)

/-- (-z² dx + xz dz)/3. -/
def examplePrimitive : FormField 3 1 := fun x =>
  (-(x 2)^2 / 3) • coordinateOneForm 3 0 +
    (x 0 * x 2 / 3) • coordinateOneForm 3 2
end Model
open Model
abbrev exampleFormType := FormField 3 2
def exampleFormValue : exampleFormType := exampleForm
abbrev examplePrimitiveType := FormField 3 1
def examplePrimitiveValue : examplePrimitiveType := examplePrimitive

def homotopy_exampleType : Prop :=
  IsCrForm none univ exampleForm ∧ IsCrForm none univ examplePrimitive ∧
    homotopyOperator (0 : E 3) exampleForm = examplePrimitive ∧
    exteriorDerivative exampleForm = 0 ∧ exteriorDerivative examplePrimitive = exampleForm

end Specs.D04.C13.EuclideanPoincareLemma
