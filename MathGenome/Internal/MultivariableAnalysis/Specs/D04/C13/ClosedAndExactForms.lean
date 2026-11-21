import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.ExteriorDerivative
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C01.Components

/-! Independent interfaces for chapters/13.tex, d04:13:closed-exact.
Ambient representatives are compared only on U. Exactness is defined only in
positive degree, with a C¹ primitive; it imposes no C² requirement. The later
theorem that a C¹ exact form is closed is not assumed here. -/
noncomputable section
namespace Specs.D04.C13.ClosedAndExactForms
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C01.Components.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model

namespace Model

/-- A C¹ form on the open domain U whose exterior derivative vanishes there. -/
def IsClosedForm {n k : ℕ} (U : Set (E n)) (ω : FormField n k) : Prop :=
  IsCrForm (some 1) U ω ∧ ∀ x ∈ U, exteriorDerivative ω x = 0

/-- A positive-degree form is exact when it has a C¹ primitive on U.
The derivative is continuous, but need not itself be C¹. -/
def IsExactForm {n k : ℕ} (U : Set (E n)) (ω : FormField n (k + 1)) : Prop :=
  ∃ η : FormField n k, IsCrForm (some 1) U η ∧ Set.EqOn ω (exteriorDerivative η) U

end Model
open Model

abbrev IsClosedFormType := {n k : ℕ} → Set (E n) → FormField n k → Prop
def IsClosedFormValue : IsClosedFormType := @Model.IsClosedForm

abbrev IsExactFormType := {n k : ℕ} → Set (E n) → FormField n (k + 1) → Prop
def IsExactFormValue : IsExactFormType := @Model.IsExactForm

def isClosedForm_iffType : Prop :=
  ∀ {n k : ℕ} (U : Set (E n)) (ω : FormField n k),
    IsCrForm (some 1) U ω →
      (IsClosedForm U ω ↔ ∀ x ∈ U, exteriorDerivative ω x = 0)

def isExactForm_iffType : Prop :=
  ∀ {n k : ℕ} (U : Set (E n)) (ω : FormField n (k + 1)),
    IsExactForm U ω ↔
      ∃ η : FormField n k, IsCrForm (some 1) U η ∧
        ∀ x ∈ U, ω x = exteriorDerivative η x

/-- Local constancy is stated on actual ambient balls contained in U. -/
def isClosedForm_zero_iff_locally_constantType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (ω : FormField n 0),
    IsCrForm (some 1) U ω →
      (IsClosedForm U ω ↔ ∀ x ∈ U, ∃ r > 0,
        Metric.ball x r ⊆ U ∧ ∀ y ∈ Metric.ball x r, ω y = ω x)

/-- Constancy on every component means pairwise equality, so it also covers
the empty domain without choosing a basepoint or a constant value. -/
def isClosedForm_zero_iff_constant_on_componentsType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (ω : FormField n 0),
    IsCrForm (some 1) U ω →
      (IsClosedForm U ω ↔ ∀ a ∈ U,
        ∀ x ∈ componentWithin U a, ∀ y ∈ componentWithin U a, ω x = ω y)

end Specs.D04.C13.ClosedAndExactForms
