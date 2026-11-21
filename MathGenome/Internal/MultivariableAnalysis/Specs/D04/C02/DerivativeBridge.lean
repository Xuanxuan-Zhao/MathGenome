import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import Mathlib.Analysis.Calculus.Gradient.Basic

/-! Independent specification of d04:02:derivative-bridge. The ambient extensions
are used only at points of the specified open domain. All dimensions may be zero.
Scalar functions have target ℝ; vector components are the actual column coordinates. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C02.DerivativeBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
namespace Model

def TotalDifferentiableAt {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (a : X) : Prop :=
  ∃ A, HasTotalDerivative U f A a

def jacobian {n m : ℕ} (f : E n → E m) (a : E n) : Matrix (Fin m) (Fin n) ℝ :=
  matrixOfLinearMap (totalDerivative f a).toLinearMap

def scalarPartialDerivative {n : ℕ} (f : E n → ℝ) (a : E n) (j : Fin n) : ℝ :=
  directionalDerivative f a (standardBasis n j)

def scalarGradient {n : ℕ} (f : E n → ℝ) (a : E n) : E n :=
  _root_.gradient f a

end Model
open Model

def TotalDifferentiableAtType := {X Y : Type} → [NormedAddCommGroup X] → [NormedSpace ℝ X] →
  [NormedAddCommGroup Y] → [NormedSpace ℝ Y] → Set X → (X → Y) → X → Prop
def TotalDifferentiableAtValue : TotalDifferentiableAtType := @Model.TotalDifferentiableAt

def jacobianType := {n m : ℕ} → (E n → E m) → E n → Matrix (Fin m) (Fin n) ℝ
def jacobianValue : jacobianType := @Model.jacobian

def scalarPartialDerivativeType := {n : ℕ} → (E n → ℝ) → E n → Fin n → ℝ
def scalarPartialDerivativeValue : scalarPartialDerivativeType := @Model.scalarPartialDerivative

def scalarGradientType := {n : ℕ} → (E n → ℝ) → E n → E n
def scalarGradientValue : scalarGradientType := @Model.scalarGradient

-- Proposition specifications

def totalDifferentiableAt_iff_differentiableAtType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (a : X)
    (hU : IsOpen U) (ha : a ∈ U),
    TotalDifferentiableAt U f a ↔ DifferentiableAt ℝ f a

def totalDerivative_uniqueType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (a : X)
    (A B : X →L[ℝ] Y) (hA : HasTotalDerivative U f A a)
    (hB : HasTotalDerivative U f B a),
    A = B

def totalDerivative_continuousAtType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (a : X)
    (A : X →L[ℝ] Y) (hA : HasTotalDerivative U f A a),
    ContinuousAt f a

def totalDerivative_hasDirectionalDerivativeType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (a v : X)
    (A : X →L[ℝ] Y) (hA : HasTotalDerivative U f A a),
    HasDirectionalDerivative f a v (A v)

def totalDerivative_directionalDerivativeType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (U : Set X) (f : X → Y) (a v : X)
    (A : X →L[ℝ] Y) (hA : HasTotalDerivative U f A a),
    directionalDerivative f a v = A v

def hasDirectionalDerivative_zeroType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (a : X),
    HasDirectionalDerivative f a 0 0

def totalDifferentiableAt_iff_componentsType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n))
    (f : E n → E m) (a : E n) (hU : IsOpen U) (ha : a ∈ U),
    TotalDifferentiableAt U f a ↔
      ∀ i : Fin m, TotalDifferentiableAt U (fun x => f x i) a

def component_hasTotalDerivativeType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n))
    (f : E n → E m) (a : E n) (A : E n →L[ℝ] E m)
    (hA : HasTotalDerivative U f A a) (i : Fin m),
    HasTotalDerivative U (fun x => f x i) ((PiLp.proj 2 (fun _ : Fin m => ℝ) i).comp A) a

def totalDerivative_hasPartialDerivativeType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n))
    (f : E n → E m) (a : E n) (A : E n →L[ℝ] E m)
    (hA : HasTotalDerivative U f A a) (j : Fin n),
    HasPartialDerivative f a j (A (standardBasis n j))

def totalDerivative_partialDerivativeType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n))
    (f : E n → E m) (a : E n) (A : E n →L[ℝ] E m)
    (hA : HasTotalDerivative U f A a) (j : Fin n),
    partialDerivative f a j = A (standardBasis n j)

def scalarPartialDerivative_eqType : Prop :=
  ∀ {n : ℕ} (U : Set (E n))
    (f : E n → ℝ) (a : E n) (A : E n →L[ℝ] ℝ)
    (hA : HasTotalDerivative U f A a) (j : Fin n),
    scalarPartialDerivative f a j = A (standardBasis n j)

def jacobian_applyType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (a : E n)
    (hf : TotalDifferentiableAt U f a) (i : Fin m) (j : Fin n),
    jacobian f a i j = scalarPartialDerivative (fun x => f x i) a j

def jacobian_characterizationType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m)
    (a : E n) (J : Matrix (Fin m) (Fin n) ℝ) (hU : IsOpen U) (ha : a ∈ U),
    HasTotalDerivative U f (LinearMap.toContinuousLinearMap (matrixLinearEquiv m n J)) a ↔
      TotalDifferentiableAt U f a ∧ jacobian f a = J

def jacobian_iff_remainderType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m)
    (a : E n) (J : Matrix (Fin m) (Fin n) ℝ) (hU : IsOpen U) (ha : a ∈ U),
    (TotalDifferentiableAt U f a ∧ jacobian f a = J) ↔
      ∃ r : E n → E m, r 0 = 0 ∧
        (∀ h, a + h ∈ U → f (a + h) = f a + matrixLinearEquiv m n J h + r h) ∧
        Tendsto (fun h => ‖r h‖ / ‖h‖) (𝓝[{h | a + h ∈ U} \ {0}] 0) (𝓝 0)

def scalarGradient_representsType : Prop :=
  ∀ {n : ℕ} (f : E n → ℝ) (a h : E n),
    totalDerivative f a h = inner ℝ (scalarGradient f a) h

def scalarGradient_uniqueType : Prop :=
  ∀ {n : ℕ} (f : E n → ℝ) (a : E n),
    ∃! g : E n, ∀ h : E n, totalDerivative f a h = inner ℝ g h

def scalarGradient_applyType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n)
    (hf : TotalDifferentiableAt U f a) (j : Fin n),
    scalarGradient f a j = scalarPartialDerivative f a j

def hasTotalDerivative_from_zeroType : Prop :=
  ∀ {m : ℕ} (U : Set (E 0)) (f : E 0 → E m)
    (a : E 0) (hU : IsOpen U) (ha : a ∈ U),
    HasTotalDerivative U f 0 a

def hasTotalDerivative_to_zeroType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → E 0)
    (a : E n) (hU : IsOpen U) (ha : a ∈ U),
    HasTotalDerivative U f 0 a

end Specs.D04.C02.DerivativeBridge
