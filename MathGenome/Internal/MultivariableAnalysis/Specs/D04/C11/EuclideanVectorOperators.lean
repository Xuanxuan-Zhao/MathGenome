import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge
import Mathlib.LinearAlgebra.Trace

/-! Independent specification for d04:11:operators. Functions on an open set
are ambient extensions, evaluated only in that set, as in Chapter 2.
All scalar gradients below are the canonical Chapter 2 object.
The curl uses the ordered standard basis (x,y,z). Its exterior-form
identification and its reversal under ambient orientation reversal belong to
`d04:13:dictionary`; the present coordinate convention fixes that sign.
Dimensions are arbitrary natural numbers, including zero. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C11.EuclideanVectorOperators
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
namespace Model

/-- The invariant trace of the total derivative, also used for moving domains. -/
def divergence {n : ℕ} (F : E n → E n) (x : E n) : ℝ :=
  LinearMap.trace ℝ (E n) (totalDerivative F x).toLinearMap

/-- Standard right-handed curl, with the coordinate order x,y,z. -/
def curl (F : E 3 → E 3) (x : E 3) : E 3 :=
  WithLp.toLp 2 ![jacobian F x 2 1 - jacobian F x 1 2,
    jacobian F x 0 2 - jacobian F x 2 0,
    jacobian F x 1 0 - jacobian F x 0 1]

/-- Scalar Laplacian of the existing gradient. -/
def laplacian {n : ℕ} (f : E n → ℝ) : E n → ℝ :=
  divergence (scalarGradient f)

/-- Apply the scalar Laplacian to each column component. -/
def vectorLaplacian {n m : ℕ} (F : E n → E m) (x : E n) : E m :=
  WithLp.toLp 2 (fun i => laplacian (fun y => F y i) x)

end Model
open Model

def divergenceType := {n : ℕ} → (E n → E n) → E n → ℝ
def divergenceValue : divergenceType := @Model.divergence

def curlType := (E 3 → E 3) → E 3 → E 3
def curlValue : curlType := Model.curl

def laplacianType := {n : ℕ} → (E n → ℝ) → E n → ℝ
def laplacianValue : laplacianType := @Model.laplacian

def vectorLaplacianType := {n m : ℕ} → (E n → E m) → E n → E m
def vectorLaplacianValue : vectorLaplacianType := @Model.vectorLaplacian

def gradient_characterizationType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (x : E n)
    (hU : IsOpen U) (hf : CrOn 1 U f) (hx : x ∈ U),
    (∀ v, totalDerivative f x v = inner ℝ (scalarGradient f x) v) ∧
    (∀ g : E n, (∀ v, totalDerivative f x v = inner ℝ g v) → g = scalarGradient f x)

def gradient_coordinatesType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (x : E n)
    (hU : IsOpen U) (hf : CrOn 1 U f) (hx : x ∈ U) (i : Fin n),
    scalarGradient f x i = scalarPartialDerivative f x i

def divergence_eq_traceType : Prop :=
  ∀ {n : ℕ} (F : E n → E n) (x : E n),
    divergence F x = LinearMap.trace ℝ (E n) (totalDerivative F x).toLinearMap

def divergence_eq_jacobian_traceType : Prop :=
  ∀ {n : ℕ} (F : E n → E n) (x : E n),
    divergence F x = Matrix.trace (jacobian F x)

def divergence_coordinatesType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (F : E n → E n) (x : E n)
    (hU : IsOpen U) (hF : CrOn 1 U F) (hx : x ∈ U),
    divergence F x = ∑ i, scalarPartialDerivative (fun y => F y i) x i

def curl_coordinatesType : Prop :=
  ∀ (U : Set (E 3)) (F : E 3 → E 3) (x : E 3)
    (hU : IsOpen U) (hF : CrOn 1 U F) (hx : x ∈ U),
    curl F x = WithLp.toLp 2
      ![scalarPartialDerivative (fun y => F y 2) x 1 - scalarPartialDerivative (fun y => F y 1) x 2,
        scalarPartialDerivative (fun y => F y 0) x 2 - scalarPartialDerivative (fun y => F y 2) x 0,
        scalarPartialDerivative (fun y => F y 1) x 0 - scalarPartialDerivative (fun y => F y 0) x 1]

def laplacian_eq_divergence_gradientType : Prop :=
  ∀ {n : ℕ} (f : E n → ℝ) (x : E n),
    laplacian f x = divergence (scalarGradient f) x

def gradient_crOnType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ)
    (hU : IsOpen U) (hf : CrOn 2 U f), CrOn 1 U (scalarGradient f)

def laplacian_coordinatesType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (x : E n)
    (hU : IsOpen U) (hf : CrOn 2 U f) (hx : x ∈ U),
    laplacian f x = ∑ i, scalarPartialDerivative (fun y => scalarPartialDerivative f y i) x i

def vectorLaplacian_applyType : Prop :=
  ∀ {n m : ℕ} (F : E n → E m) (x : E n) (i : Fin m),
    vectorLaplacian F x i = laplacian (fun y => F y i) x

def vectorLaplacian_coordinatesType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (F : E n → E m) (x : E n)
    (hU : IsOpen U) (hF : CrOn 2 U F) (hx : x ∈ U) (j : Fin m),
    vectorLaplacian F x j =
      ∑ i, scalarPartialDerivative (fun y => scalarPartialDerivative (fun z => F z j) y i) x i

def gradient_dimension_zeroType : Prop :=
  ∀ (f : E 0 → ℝ) (x : E 0), scalarGradient f x = 0

def divergence_dimension_zeroType : Prop :=
  ∀ (F : E 0 → E 0) (x : E 0), divergence F x = 0

def laplacian_dimension_zeroType : Prop :=
  ∀ (f : E 0 → ℝ) (x : E 0), laplacian f x = 0

def vectorLaplacian_dimension_zeroType : Prop :=
  ∀ {m : ℕ} (F : E 0 → E m) (x : E 0), vectorLaplacian F x = 0

end Specs.D04.C11.EuclideanVectorOperators
