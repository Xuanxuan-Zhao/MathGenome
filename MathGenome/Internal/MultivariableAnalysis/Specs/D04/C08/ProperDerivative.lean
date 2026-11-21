import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.ProperContinuity
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces

/-! The proper parameter theorem, paper.tex `d04:08:proper-derivative`.
Operator integrability is coordinatewise Riemann integrability of the columns.
The operator integral integrates exactly these columns, in the fixed Euclidean
bases. Parameters are ambient functions restricted to an open set; no condition
is placed on their values outside that set. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Specs.D04.C08.ProperDerivative
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C02.DerivativeInterfaces.Model
namespace Model

def OperatorRegionIntegrable {n m k : ℕ} {S : Set (E n)}
    (A : S → E m →L[ℝ] E k) : Prop :=
  Bornology.IsBounded S ∧ ∀ j : Fin m,
    VectorRegionIntegrable (fun x => A x (standardBasis m j))

def operatorRegionIntegral {n m k : ℕ} {S : Set (E n)}
    (A : S → E m →L[ℝ] E k) : E m →L[ℝ] E k :=
  LinearMap.toContinuousLinearMap (matrixLinearEquiv k m
    (fun i j => regionIntegral (fun x => A x (standardBasis m j) i)))
end Model
open Model
abbrev OperatorRegionIntegrableType := {n m k : ℕ} → {S : Set (E n)} →
  (S → E m →L[ℝ] E k) → Prop
def OperatorRegionIntegrableValue : OperatorRegionIntegrableType := @OperatorRegionIntegrable
abbrev operatorRegionIntegralType := {n m k : ℕ} → {S : Set (E n)} →
  (S → E m →L[ℝ] E k) → (E m →L[ℝ] E k)
def operatorRegionIntegralValue : operatorRegionIntegralType := @operatorRegionIntegral

/-- Evaluation commutes with the actual Riemann operator integral. This also
identifies column integrability with integrability in every fixed direction. -/
def integral_applyType : Prop := ∀ {n m k : ℕ} {S : Set (E n)}
  (A : S → E m →L[ℝ] E k), OperatorRegionIntegrable A → ∀ h : E m,
  VectorRegionIntegrable (fun x => A x h) ∧
  operatorRegionIntegral A h = vectorRegionIntegral (fun x => A x h)

def proper_derivativeType : Prop := ∀ {n m k : ℕ} {S : Set (E n)} {P : Set (E m)},
  Jordan S → IsOpen P → ∀ (f : S → E m → E k)
  (A : S → E m → E m →L[ℝ] E k),
  (∀ p ∈ P, VectorRegionIntegrable (fun x => f x p)) →
  (∀ x p, p ∈ P → HasFDerivAt (f x) (A x p) p) →
  (∀ p ∈ P, OperatorRegionIntegrable (fun x => A x p)) →
  ∀ (p₀ : E m) (hp₀ : p₀ ∈ P),
  Tendsto (fun p : P => sSup (range (fun x => ‖A x p - A x p₀‖)))
    (𝓝 (⟨p₀, hp₀⟩ : P)) (𝓝 0) →
  HasFDerivAt (fun p => vectorRegionIntegral (fun x => f x p))
    (operatorRegionIntegral (fun x => A x p₀)) p₀ ∧
  ∀ h, fderiv ℝ (fun p => vectorRegionIntegral (fun x => f x p)) p₀ h =
    vectorRegionIntegral (fun x => A x p₀ h)

def continuous_parameter_derivativeType : Prop :=
  ∀ {n m k : ℕ} {S : Set (E n)} {P : Set (E m)}, Jordan S → IsOpen P →
  ∀ (f : closure S → E m → E k) (A : closure S → E m → E m →L[ℝ] E k),
  Continuous (fun z : closure S × P => f z.1 z.2) →
  Continuous (fun z : closure S × P => A z.1 z.2) →
  (∀ x : S, ∀ p ∈ P, HasFDerivAt (f ⟨x, subset_closure x.property⟩)
    (A ⟨x, subset_closure x.property⟩ p) p) →
  let F := fun p => vectorRegionIntegral (fun x : S => f ⟨x, subset_closure x.property⟩ p)
  let G := fun p => operatorRegionIntegral (fun x : S => A ⟨x, subset_closure x.property⟩ p)
  (∀ p ∈ P, VectorRegionIntegrable (fun x : S => f ⟨x, subset_closure x.property⟩ p)) ∧
  CrOn 1 P F ∧ ContinuousOn G P ∧
  ∀ p ∈ P, HasFDerivAt F (G p) p ∧ ∀ h,
    fderiv ℝ F p h = vectorRegionIntegral (fun x : S => A ⟨x, subset_closure x.property⟩ p h)
end Specs.D04.C08.ProperDerivative
