import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.ClosedAndExactForms

/-! Independent finite-regularity statements for d04:15:exact-closed-c1.
The predecessor degree is arbitrary, so degree k+1 ranges over all positive
integers. The ambient dimension includes zero and there is no degree bound.
Both fields are C¹ only on U; no second derivatives of the primitive are assumed. -/
noncomputable section
namespace Specs.D04.C15.ExactC1FormsAreClosed
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C13.ClosedAndExactForms.Model

def exteriorDerivative_eq_zero_of_C1_primitiveType : Prop :=
  ∀ {n k : ℕ} (U : Set (E n)) (ω : FormField n (k+1)) (η : FormField n k),
    IsCrForm (some 1) U ω → IsCrForm (some 1) U η →
    Set.EqOn ω (exteriorDerivative η) U →
    ∀ x ∈ U, exteriorDerivative ω x = 0

def isClosedForm_of_isExactFormType : Prop :=
  ∀ {n k : ℕ} (U : Set (E n)) (ω : FormField n (k+1)),
    IsCrForm (some 1) U ω → IsExactForm U ω → IsClosedForm U ω

end Specs.D04.C15.ExactC1FormsAreClosed
