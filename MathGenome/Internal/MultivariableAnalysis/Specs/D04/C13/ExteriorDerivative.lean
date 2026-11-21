import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.NormalizedFormsAndWedge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge

/-! The coordinate exterior derivative, with the normalization and coefficient
regularity of Chapter 13. Ambient representatives are restricted to the open
set in all analytic assertions. No regularity is required outside that set. -/
noncomputable section
open scoped BigOperators Classical
namespace Specs.D04.C13.ExteriorDerivative
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
namespace Model

/-- The constant covector dx_j ∧ dx_I, with its degree transported to k+1.
The first factor is the j-th coordinate functional, hence has value v_j on v. -/
def coordinateExteriorTerm {n k : ℕ} (j : Fin n) (I : MultiIndex n k) :
    Covector (E n) (k + 1) :=
  castCovector (Nat.add_comm 1 k)
    (wedge (linearCovector ((standardBasis n).coord j)) (dx (standardBasis n) I))

/-- dω = ∑_(I,j) (∂_j a_I) dx_j ∧ dx_I. The partial-derivative
selector is asserted to represent a genuine derivative under the C¹ hypotheses. -/
def exteriorDerivative {n k : ℕ} (ω : FormField n k) : FormField n (k + 1) :=
  fun x => ∑ I : MultiIndex n k, ∑ j : Fin n,
    scalarPartialDerivative (fun y => coefficient (standardBasis n) (ω y) I) x j •
      coordinateExteriorTerm j I

end Model
open Model

abbrev exteriorDerivativeType := {n k : ℕ} → FormField n k → FormField n (k + 1)
def exteriorDerivativeValue : exteriorDerivativeType := @Model.exteriorDerivative

def exteriorDerivative_formulaType : Prop :=
  ∀ {n k : ℕ} (ω : FormField n k) (x : E n),
    exteriorDerivative ω x = ∑ I : MultiIndex n k, ∑ j : Fin n,
      scalarPartialDerivative (fun y => coefficient (standardBasis n) (ω y) I) x j •
        castCovector (Nat.add_comm 1 k)
          (wedge (linearCovector ((standardBasis n).coord j)) (dx (standardBasis n) I))

def exteriorDerivative_isCrType : Prop :=
  ∀ {n k : ℕ} (r : ℕ) (hr : 1 ≤ r) (U : Set (E n)) (ω : FormField n k),
    IsCrForm (some r) U ω → IsCrForm (some (r - 1)) U (exteriorDerivative ω)

def exteriorDerivative_continuousType : Prop :=
  ∀ {n k : ℕ} (U : Set (E n)) (ω : FormField n k),
    IsCrForm (some 1) U ω → IsCrForm (some 0) U (exteriorDerivative ω)

def exteriorDerivative_smoothType : Prop :=
  ∀ {n k : ℕ} (U : Set (E n)) (ω : FormField n k),
    IsCrForm none U ω → IsCrForm none U (exteriorDerivative ω)

def exteriorDerivative_topType : Prop :=
  ∀ {n : ℕ} (ω : FormField n n), exteriorDerivative ω = 0

def exteriorDerivative_aboveType : Prop :=
  ∀ {n k : ℕ} (hk : n < k) (ω : FormField n k), exteriorDerivative ω = 0

/-- Agreement with a specified genuine total derivative, at any point where it
exists. This in particular identifies d on all C¹ functions. -/
def exteriorDerivative_scalarType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (x : E n)
    (A : E n →L[ℝ] ℝ), HasTotalDerivative U f A x →
    exteriorDerivative (fun y => scalarCovector (V := E n) (f y)) x =
      linearCovector A.toLinearMap

def exteriorDerivative_functionType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (hU : IsOpen U),
    CrOn 1 U f → ∀ x ∈ U,
      exteriorDerivative (fun y => scalarCovector (V := E n) (f y)) x =
        linearCovector (totalDerivative f x).toLinearMap

end Specs.D04.C13.ExteriorDerivative
