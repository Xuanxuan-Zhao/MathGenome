import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.ProperDerivative
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C08.PositiveJacobian
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.RegionSubstitution
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.LinearVolume
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.EuclideanVectorOperators
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Pow

/-! Independent statements for `d04:08:moving-domain` and `d04:08:expansion`.
All regions and integrals are the canonical bounded Jordan/Riemann objects.
The family is represented by partial homeomorphisms with common open source W.
Its forward map is jointly C¹; its inverse is C¹ separately for each parameter.
The parameter derivative of the spatial matrix is only assumed to exist and
be continuous. No joint C² or regularity of the region's boundary is assumed.
All dimensions range over ℕ, including zero. -/
noncomputable section
open Set
open scoped Matrix.Norms.Elementwise
namespace Specs.D04.C08.MovingDomains
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
namespace Model

abbrev Family (m n : ℕ) := E m → OpenPartialHomeomorph (E n) (E n)

def spatialMatrix {m n : ℕ} (e : Family m n) (p : E m) (x : E n) :=
  matrixOfLinearMap (fderiv ℝ (e p) x).toLinearMap

def parameterJacobian {m n : ℕ} (e : Family m n) (p : E m) (x : E n) :=
  fderiv ℝ (fun q => spatialMatrix e q x) p

def RegularFamily {m n : ℕ} (P : Set (E m)) (W : Set (E n))
    (e : Family m n) : Prop :=
  (∀ p ∈ P, (e p).source = W) ∧
  ContDiffOn ℝ 1 (fun z : E m × E n => e z.1 z.2) (P ×ˢ W) ∧
  (∀ p ∈ P, ContDiffOn ℝ 1 (e p).symm (e p).target) ∧
  (∀ p ∈ P, ∀ x ∈ W, DifferentiableAt ℝ (fun q => spatialMatrix e q x) p) ∧
  ContinuousOn (fun z : E m × E n => parameterJacobian e z.1 z.2) (P ×ˢ W)

def movingIntegral {m n : ℕ} (S : Set (E n)) (e : Family m n)
    (f : E m × E n → ℝ) (p : E m) : ℝ :=
  regionIntegral (fun y : (e p) '' S => f (p, y))

def referenceIntegrand {m n : ℕ} (e : Family m n)
    (f : E m × E n → ℝ) (p h : E m) (x : E n) : ℝ :=
  |(spatialMatrix e p x).det| *
    (fderiv ℝ (fun q => f (q, e p x)) p h +
      fderiv ℝ (fun y => f (p, y)) (e p x)
        (fderiv ℝ (fun q => e q x) p h) +
      f (p, e p x) * ((spatialMatrix e p x)⁻¹ * parameterJacobian e p x h).trace)

def velocity {m n : ℕ} (e : Family m n) (p h : E m) (y : E n) : E n :=
  fderiv ℝ (fun q => e q ((e p).symm y)) p h

/-- This is D_x D_p Φ[h] = (D_p D_x Φ[h]), evaluated on each fixed h.
In finite-dimensional parameter spaces the directional evaluations are equivalent
to differentiability of the operator-valued map with this mixed derivative. -/
def MixedCommutes {m n : ℕ} (P : Set (E m)) (W : Set (E n))
    (e : Family m n) : Prop :=
  ∀ p ∈ P, ∀ x ∈ W, ∀ h : E m,
    HasFDerivAt (fun z => fderiv ℝ (fun q => e q z) p h)
      (LinearMap.toContinuousLinearMap
        (matrixLinearEquiv n n (parameterJacobian e p x h))) x

def spatialIntegrand {m n : ℕ} (e : Family m n)
    (f : E m × E n → ℝ) (p h : E m) (y : E n) : ℝ :=
  fderiv ℝ (fun q => f (q, y)) p h +
    fderiv ℝ (fun z => f (p, z)) y (velocity e p h y) +
      f (p, y) * divergence (velocity e p h) y

end Model
open Model

/-- Applicability bridge from the source's operator-valued D_x D_p Φ.
The matrix equality evaluates the two different slot orders explicitly. -/
def mixed_commutes_of_operator_derivativeType : Prop := ∀ {m n : ℕ}
  (P : Set (E m)) (W : Set (E n)) (e : Family m n),
  (∀ p ∈ P, ∀ x ∈ W, ∃ C : E n →L[ℝ] (E m →L[ℝ] E n),
    HasFDerivAt (fun z => fderiv ℝ (fun q => e q z) p) C x ∧
      ∀ h k, C k h = matrixLinearEquiv n n (parameterJacobian e p x h) k) →
  MixedCommutes P W e

/-- Joint C² suffices for both finite-regularity assumptions. -/
def c2_sufficientType : Prop := ∀ {m n : ℕ} (P : Set (E m)) (W : Set (E n)) (e : Family m n),
  IsOpen P → IsOpen W → (∀ p ∈ P, (e p).source = W) →
  ContDiffOn ℝ 2 (fun z : E m × E n => e z.1 z.2) (P ×ˢ W) →
  (∀ p ∈ P, ContDiffOn ℝ 1 (e p).symm (e p).target) →
  RegularFamily P W e ∧ MixedCommutes P W e

/-- The geometric conclusion does not need the mixed parameter derivative. -/
def jordan_imageType : Prop := ∀ {m n : ℕ} (S : Set (E n))
  (P : Set (E m)) (W : Set (E n)) (e : Family m n),
  Jordan S → IsOpen P → IsOpen W → closure S ⊆ W → RegularFamily P W e →
  ∀ p ∈ P, Jordan ((e p) '' S)

def pullbackType : Prop := ∀ {m n : ℕ} (S : Set (E n))
  (P : Set (E m)) (W : Set (E n)) (e : Family m n)
  (O : Set (E m × E n)) (f : E m × E n → ℝ),
  Jordan S → IsOpen P → IsOpen W → closure S ⊆ W → RegularFamily P W e →
  IsOpen O → ContDiffOn ℝ 1 f O →
  (∀ p ∈ P, ∀ x ∈ closure S, (p, e p x) ∈ O) →
  ∀ p ∈ P,
    RegionIntegrable (fun y : (e p) '' S => f (p, y)) ∧
    RegionIntegrable (fun x : S => f (p, e p x) * |(spatialMatrix e p x).det|) ∧
    movingIntegral S e f p =
      regionIntegral (fun x : S => f (p, e p x) * |(spatialMatrix e p x).det|)

def moving_domainType : Prop := ∀ {m n : ℕ} (S : Set (E n))
  (P : Set (E m)) (W : Set (E n)) (e : Family m n)
  (O : Set (E m × E n)) (f : E m × E n → ℝ),
  Jordan S → IsOpen P → IsOpen W → closure S ⊆ W → RegularFamily P W e →
  IsOpen O → ContDiffOn ℝ 1 f O →
  (∀ p ∈ P, ∀ x ∈ closure S, (p, e p x) ∈ O) →
  CrOn 1 P (movingIntegral S e f) ∧ ∀ p ∈ P, ∀ h : E m,
    RegionIntegrable (fun x : S => referenceIntegrand e f p h x) ∧
    fderiv ℝ (movingIntegral S e f) p h =
      regionIntegral (fun x : S => referenceIntegrand e f p h x)

def velocity_formulaType : Prop := ∀ {m n : ℕ} (S : Set (E n))
  (P : Set (E m)) (W : Set (E n)) (e : Family m n)
  (O : Set (E m × E n)) (f : E m × E n → ℝ),
  Jordan S → IsOpen P → IsOpen W → closure S ⊆ W → RegularFamily P W e →
  IsOpen O → ContDiffOn ℝ 1 f O →
  (∀ p ∈ P, ∀ x ∈ closure S, (p, e p x) ∈ O) → MixedCommutes P W e →
  ∀ p ∈ P, ∀ h : E m,
    (∀ x ∈ W, DifferentiableAt ℝ (velocity e p h) (e p x) ∧
      divergence (velocity e p h) (e p x) =
        ((spatialMatrix e p x)⁻¹ * parameterJacobian e p x h).trace) ∧
    RegionIntegrable (fun y : (e p) '' S => spatialIntegrand e f p h y) ∧
    fderiv ℝ (movingIntegral S e f) p h =
      regionIntegral (fun y : (e p) '' S => spatialIntegrand e f p h y)

/-- The source's fixed C¹ density on dilations; an arbitrary open positive
parameter set permits a neighborhood of exactly the relevant closures. -/
def dilationType : Prop := ∀ {n : ℕ} (S : Set (E n)) (T : Set ℝ)
  (O : Set (E n)) (f : E n → ℝ),
  Jordan S → IsOpen T → T ⊆ Ioi 0 → IsOpen O → ContDiffOn ℝ 1 f O →
  (∀ t ∈ T, ∀ x ∈ closure S, t • x ∈ O) →
  ∀ t ∈ T,
    Jordan ((fun x : E n => t • x) '' S) ∧
    (∀ y : E n, fderiv ℝ (fun z : E n => t⁻¹ • z) y =
      t⁻¹ • ContinuousLinearMap.id ℝ (E n) ∧
      divergence (fun z : E n => t⁻¹ • z) y = (n : ℝ) / t) ∧
    RegionIntegrable (fun y : ((fun x : E n => t • x) '' S) =>
      fderiv ℝ f y y + (n : ℝ) * f y) ∧
    HasDerivAt (fun u : ℝ => regionIntegral
      (fun y : ((fun x : E n => u • x) '' S) => f y))
      (t⁻¹ * regionIntegral
        (fun y : ((fun x : E n => t • x) '' S) => fderiv ℝ f y y + (n : ℝ) * f y)) t

def dilation_volumeType : Prop := ∀ {n : ℕ} (S : Set (E n)), Jordan S →
  ∀ t : ℝ, 0 < t →
    Jordan ((fun x : E n => t • x) '' S) ∧
    volume ((fun x : E n => t • x) '' S) = t ^ n * volume S ∧
    HasDerivAt (fun u : ℝ => volume ((fun x : E n => u • x) '' S))
      ((n : ℝ) * t ^ (n - 1) * volume S) t

end Specs.D04.C08.MovingDomains
