import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C13.ExteriorDerivative
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.EuclideanVectorOperators
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C09.GradientIntegral
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.OrientationsAndChartSigns
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.CrossProduct

/-! The metric dictionary uses the same alternating maps, derivative selectors,
work integral and orientation ray as the earlier chapters. Indices are zero based. -/
noncomputable section
open scoped BigOperators Classical
namespace Specs.D04.C13.OrientedEuclideanDictionary
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C13.NormalizedFormsAndWedge.Model
open Specs.D04.C13.ExteriorDerivative.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C09.PathsLength.Model
open Specs.D04.C09.LineIntegrals.Model
open Specs.D04.C14.OrientationsAndChartSigns.Model
namespace Model

/-- The work one-form, in every dimension, including zero. -/
def alpha {n : ℕ} (F : E n → E n) : FormField n 1 :=
  fun x => linearCovector (workCovector F x).toLinearMap

/-- A one-form is integrated by its evaluation on the path velocity. -/
def OneFormIntegrable {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (ω : FormField n 1) : Prop :=
  PieceIntegrable d (fun x v => ω x (fun _ => v))

def oneFormIntegral {n a b} {γ : IntervalPath n a b}
    (d : PiecewiseC1Data γ) (ω : FormField n 1) (h : OneFormIntegrable d ω) : ℝ :=
  pieceIntegral d (fun x v => ω x (fun _ => v)) h

def coordinateOne {n : ℕ} (i : Fin n) : Covector (E n) 1 :=
  linearCovector ((standardBasis n).coord i)

def omega (n : ℕ) : Covector (E n) n := (standardBasis n).det

/-- Increasing coordinate wedge with the i-th coordinate omitted. -/
def coordinateWithout {n : ℕ} (i : Fin (n+1)) : Covector (E (n+1)) n :=
  wedgeList n (fun j => (standardBasis (n+1)).coord (i.succAbove j))

/-- The n-form corresponding to flux in dimension n+1. This parametrization
includes dimension one without introducing negative-degree forms. -/
def fluxForm {n : ℕ} (F : E (n+1) → E (n+1)) : FormField (n+1) n :=
  fun x => ∑ i : Fin (n+1), ((-1 : ℝ) ^ i.val * F x i) • coordinateWithout i

/-- The cyclic order dz∧dx fixes the middle sign. -/
def beta (F : E 3 → E 3) : FormField 3 2 := fun x =>
  F x 0 • wedge (coordinateOne 1) (coordinateOne 2) +
  F x 1 • wedge (coordinateOne 2) (coordinateOne 0) +
  F x 2 • wedge (coordinateOne 0) (coordinateOne 1)

def euclideanCross (v w : E 3) : E 3 :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp v) (WithLp.ofLp w))

/-- This is the canonical Chapter 14 orientation, with no additional sign data. -/
def metricTopForm {k : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fact (Module.finrank ℝ V = k)] (o : SpaceOrientation k V) : Covector V k :=
  o.volumeForm

def gramDensity {k : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : Fin k → V) : ℝ := Real.sqrt (Matrix.det (fun i j => inner ℝ (v i) (v j)))
end Model
open Model

-- Definitions and their expected values.
abbrev alphaType := {n : ℕ} → (E n → E n) → FormField n 1
def alphaValue : alphaType := @Model.alpha
abbrev coordinateOneType := {n : ℕ} → Fin n → Covector (E n) 1
def coordinateOneValue : coordinateOneType := @Model.coordinateOne
abbrev omegaType := (n : ℕ) → Covector (E n) n
def omegaValue : omegaType := Model.omega
abbrev coordinateWithoutType := {n : ℕ} → Fin (n+1) → Covector (E (n+1)) n
def coordinateWithoutValue : coordinateWithoutType := @Model.coordinateWithout
abbrev fluxFormType := {n : ℕ} → (E (n+1) → E (n+1)) → FormField (n+1) n
def fluxFormValue : fluxFormType := @Model.fluxForm
abbrev betaType := (E 3 → E 3) → FormField 3 2
def betaValue : betaType := Model.beta
abbrev euclideanCrossType := E 3 → E 3 → E 3
def euclideanCrossValue : euclideanCrossType := Model.euclideanCross
universe u
abbrev metricTopFormType := {k : ℕ} → {V : Type u} → [NormedAddCommGroup V] →
  [InnerProductSpace ℝ V] → [Fact (Module.finrank ℝ V = k)] → SpaceOrientation k V → Covector V k
def metricTopFormValue : metricTopFormType := @Model.metricTopForm
abbrev gramDensityType := {k : ℕ} → {V : Type u} → [NormedAddCommGroup V] →
  [InnerProductSpace ℝ V] → (Fin k → V) → ℝ
def gramDensityValue : gramDensityType := @Model.gramDensity
abbrev OneFormIntegrableType := {n : ℕ} → {a b : ℝ} → {γ : IntervalPath n a b} →
  PiecewiseC1Data γ → FormField n 1 → Prop
def OneFormIntegrableValue : OneFormIntegrableType := @Model.OneFormIntegrable
abbrev oneFormIntegralType := {n : ℕ} → {a b : ℝ} → {γ : IntervalPath n a b} →
  (d : PiecewiseC1Data γ) → (ω : FormField n 1) → OneFormIntegrable d ω → ℝ
def oneFormIntegralValue : oneFormIntegralType := @Model.oneFormIntegral

def alpha_applyType : Prop := ∀ {n} (F : E n → E n) (x : E n) (v : Fin 1 → E n),
  alpha F x v = inner ℝ (F x) (v 0)

def alpha_coordinatesType : Prop := ∀ {n} (F : E n → E n) (x : E n),
  alpha F x = ∑ i : Fin n, F x i • coordinateOne i

def alpha_workCovectorType : Prop := ∀ {n} (F : E n → E n) (x : E n) (v : E n),
  alpha F x (fun _ => v) = workCovector F x v

def differential_alpha_gradientType : Prop := ∀ {n} (U : Set (E n)) (f : E n → ℝ),
  IsOpen U → CrOn 1 U f → ∀ x ∈ U,
    exteriorDerivative (fun y => scalarCovector (V := E n) (f y)) x = alpha (scalarGradient f) x

def alpha_integrable_iffType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (F : E n → E n), OneFormIntegrable d (alpha F) ↔ WorkIntegrable d F

def alpha_integral_workType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (F : E n → E n) (ha : OneFormIntegrable d (alpha F))
  (hw : WorkIntegrable d F), oneFormIntegral d (alpha F) ha = workLineIntegral d F hw

def alpha_gradient_endpointType : Prop := ∀ {n a b} {γ : IntervalPath n a b}
  (d : PiecewiseC1Data γ) (U : Set (E n)) (f : E n → ℝ), IsOpen U → CrOn 1 U f →
  trace γ ⊆ U → ∃ h : OneFormIntegrable d (alpha (scalarGradient f)),
    oneFormIntegral d (alpha (scalarGradient f)) h = f (γ b) - f (γ a)

/-- The general coordinate formula is valid even without regularity because
all coefficients here are literally the components of F. -/
def exterior_alpha_formulaType : Prop := ∀ {n} (F : E n → E n) (x : E n),
  exteriorDerivative (alpha F) x = ∑ i : Fin n, ∑ j : Fin n,
    if i < j then
      (scalarPartialDerivative (fun y => F y j) x i -
       scalarPartialDerivative (fun y => F y i) x j) • wedge (coordinateOne i) (coordinateOne j)
    else 0

def exterior_alpha_closed_iffType : Prop := ∀ {n} (U : Set (E n)) (F : E n → E n),
  IsOpen U → CrOn 1 U F →
  ((∀ x ∈ U, exteriorDerivative (alpha F) x = 0) ↔
    ∀ x ∈ U, (jacobian F x).IsSymm)

def planar_derivativeType : Prop := ∀ (U : Set (E 2)) (P Q : E 2 → ℝ),
  IsOpen U → CrOn 1 U P → CrOn 1 U Q → ∀ x ∈ U,
  exteriorDerivative (fun y => P y • coordinateOne 0 + Q y • coordinateOne 1) x =
    (scalarPartialDerivative Q x 0 - scalarPartialDerivative P x 1) • omega 2

def beta_crossType : Prop := ∀ (F : E 3 → E 3) (x v w : E 3),
  beta F x ![v,w] = inner ℝ (F x) (euclideanCross v w)

def exterior_alpha_curlType : Prop := ∀ (U : Set (E 3)) (F : E 3 → E 3),
  IsOpen U → CrOn 1 U F → ∀ x ∈ U,
    exteriorDerivative (alpha F) x = beta (curl F) x

def exterior_beta_divergenceType : Prop := ∀ (U : Set (E 3)) (F : E 3 → E 3),
  IsOpen U → CrOn 1 U F → ∀ x ∈ U,
    exteriorDerivative (beta F) x = divergence F x • omega 3

def fluxForm_threeType : Prop := ∀ (F : E 3 → E 3), fluxForm F = beta F

def exterior_flux_divergenceType : Prop := ∀ {n} (U : Set (E (n+1)))
  (F : E (n+1) → E (n+1)), IsOpen U → CrOn 1 U F → ∀ x ∈ U,
  exteriorDerivative (fluxForm F) x = divergence F x • omega (n+1)

def exterior_flux_coefficientType : Prop := ∀ {n} (U : Set (E (n+1)))
  (F : E (n+1) → E (n+1)), IsOpen U → CrOn 1 U F → ∀ x ∈ U,
  exteriorDerivative (fluxForm F) x =
    (∑ i, scalarPartialDerivative (fun y => F y i) x i) • omega (n+1)

def omega_wedgeType : Prop := ∀ n, omega n = wedgeList n (fun i => (standardBasis n).coord i)

def metricTopForm_normalizedType : Prop := ∀ {k : ℕ} {V : Type u}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = k)]
  (o : SpaceOrientation k V) (b : OrthonormalBasis (Fin k) ℝ V),
  b.toBasis.orientation = o → metricTopForm o b = 1

def metricTopForm_exists_uniqueType : Prop := ∀ {k : ℕ} {V : Type u}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = k)]
  (hk : 0 < k) (o : SpaceOrientation k V),
  ∃! ω : Covector V k, ∀ b : OrthonormalBasis (Fin k) ℝ V, b.toBasis.orientation = o → ω b = 1

def metricTopForm_gramType : Prop := ∀ {k : ℕ} {V : Type u}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = k)]
  (o : SpaceOrientation k V) (v : Fin k → V), |metricTopForm o v| = gramDensity v

def metricTopForm_reverseType : Prop := ∀ {k : ℕ} {V : Type u}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = k)]
  (o : SpaceOrientation k V), metricTopForm (-o) = -metricTopForm o

def metricTopForm_reverse_densityType : Prop := ∀ {k : ℕ} {V : Type u}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = k)]
  (o : SpaceOrientation k V) (v : Fin k → V),
  |metricTopForm (-o) v| = |metricTopForm o v|

/-- Curl is the unique vector representing this two-covector. -/
def curl_identification_uniqueType : Prop := ∀ (U : Set (E 3)) (F : E 3 → E 3),
  IsOpen U → CrOn 1 U F → ∀ x ∈ U, ∀ c : E 3,
    (∀ v w, exteriorDerivative (alpha F) x ![v,w] = inner ℝ c (euclideanCross v w)) → c = curl F x

/-- Reversing orientation negates both the flux-vector identification and curl. -/
def curl_orientation_reverseType : Prop := ∀ (U : Set (E 3)) (F : E 3 → E 3),
  IsOpen U → CrOn 1 U F → ∀ x ∈ U,
    exteriorDerivative (alpha F) x = -beta (fun y => -curl F y) x

/-- The standard coordinate volume uses the positive standard-basis orientation. -/
def omega_metricTopFormType : Prop := ∀ n : ℕ,
  letI : Fact (Module.finrank ℝ (E n) = n) := ⟨by simp [E]⟩
  omega n = metricTopForm (standardBasis n).orientation

def fluxForm_volumeType : Prop := ∀ {n} (F : E (n+1) → E (n+1)) (x : E (n+1)) (v : Fin n → E (n+1)),
  fluxForm F x v = omega (n+1) (Fin.cons (F x) v)

def beta_volumeType : Prop := ∀ (F : E 3 → E 3) (x v w : E 3),
  beta F x ![v,w] = omega 3 ![F x,v,w]

def alpha_isCrType : Prop := ∀ {n} (r : ℕ) (U : Set (E n)) (F : E n → E n),
  IsOpen U → CrOn r U F → IsCrForm (some r) U (alpha F)

def fluxForm_isCrType : Prop := ∀ {n} (r : ℕ) (U : Set (E (n+1))) (F : E (n+1) → E (n+1)),
  IsOpen U → CrOn r U F → IsCrForm (some r) U (fluxForm F)

def beta_isCrType : Prop := ∀ (r : ℕ) (U : Set (E 3)) (F : E 3 → E 3),
  IsOpen U → CrOn r U F → IsCrForm (some r) U (beta F)

end Specs.D04.C13.OrientedEuclideanDictionary
