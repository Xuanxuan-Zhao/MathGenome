import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.Matrix.Normed

/-! Independent statements for chapters/02.tex, d04:02:bilinear-rule.
All derivatives use the open-domain remainder predicate from the shared interface.
The general bilinear rule assumes algebraic bilinearity, with no extra continuity
hypothesis. Matrix spaces use their Euclidean Frobenius norm. Rectangular
matrix sizes and Euclidean dimensions may be zero. -/
noncomputable section
open Set
open scoped BigOperators Matrix.Norms.Frobenius
namespace Specs.D04.C02.BilinearRules
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model

namespace Model
/-- Ordered cross product in the standard oriented Euclidean three-space. -/
def cross (u v : E 3) : E 3 :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (WithLp.ofLp v))
end Model

def crossType := E 3 → E 3 → E 3
def crossValue : crossType := Model.cross

def linear_hasTotalDerivativeType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ [FiniteDimensional ℝ X] (U : Set X) (A : X →ₗ[ℝ] Y) (a : X),
    IsOpen U → a ∈ U →
    HasTotalDerivative U A A.toContinuousLinearMap a ∧
      totalDerivative A a = A.toContinuousLinearMap

def sum_hasTotalDerivativeType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ {ι : Type} (s : Finset ι) (U : Set X) (f : ι → X → Y)
    (A : ι → X →L[ℝ] Y) (a : X), IsOpen U → a ∈ U →
    (∀ i ∈ s, HasTotalDerivative U (f i) (A i) a) →
    HasTotalDerivative U (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, A i) a

def sum_totalDerivativeType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ {ι : Type} (s : Finset ι) (U : Set X) (f : ι → X → Y) (a : X),
    IsOpen U → a ∈ U → (∀ i ∈ s, TotalDifferentiableAt U (f i) a) →
    TotalDifferentiableAt U (fun x => ∑ i ∈ s, f i x) a ∧
      totalDerivative (fun x => ∑ i ∈ s, f i x) a = ∑ i ∈ s, totalDerivative (f i) a

def const_smul_hasTotalDerivativeType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (U : Set X) (f : X → Y) (A : X →L[ℝ] Y) (a : X) (c : ℝ),
    HasTotalDerivative U f A a → HasTotalDerivative U (fun x => c • f x) (c • A) a

def const_smul_totalDerivativeType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (U : Set X) (f : X → Y) (a : X) (c : ℝ), TotalDifferentiableAt U f a →
    TotalDifferentiableAt U (fun x => c • f x) a ∧
      totalDerivative (fun x => c • f x) a = c • totalDerivative f a

def bilinear_hasTotalDerivativeType : Prop :=
  ∀ {X Y Z W : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W],
  ∀ [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]
    (B : Y →ₗ[ℝ] Z →ₗ[ℝ] W) (U : Set X) (u : X → Y) (v : X → Z)
    (A : X →L[ℝ] Y) (C : X →L[ℝ] Z) (a : X),
    HasTotalDerivative U u A a → HasTotalDerivative U v C a →
    ∃ L : X →L[ℝ] W, HasTotalDerivative U (fun x => B (u x) (v x)) L a ∧
      ∀ h, L h = B (A h) (v a) + B (u a) (C h)

def bilinear_totalDerivativeType : Prop :=
  ∀ {X Y Z W : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [NormedAddCommGroup Z] [NormedSpace ℝ Z] [NormedAddCommGroup W] [NormedSpace ℝ W],
  ∀ [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]
    (B : Y →ₗ[ℝ] Z →ₗ[ℝ] W) (U : Set X) (u : X → Y) (v : X → Z) (a : X),
    TotalDifferentiableAt U u a → TotalDifferentiableAt U v a →
    TotalDifferentiableAt U (fun x => B (u x) (v x)) a ∧
      ∀ h, totalDerivative (fun x => B (u x) (v x)) a h =
        B (totalDerivative u a h) (v a) + B (u a) (totalDerivative v a h)

-- Actual specializations: the operations in the conclusions are their ordinary ones.
def scalar_mul_totalDerivativeType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X],
  ∀ (U : Set X) (u v : X → ℝ) (a : X),
    TotalDifferentiableAt U u a → TotalDifferentiableAt U v a →
    TotalDifferentiableAt U (fun x => u x * v x) a ∧
      ∀ h, totalDerivative (fun x => u x * v x) a h =
        totalDerivative u a h * v a + u a * totalDerivative v a h

def smul_totalDerivativeType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ [FiniteDimensional ℝ Y] (U : Set X) (u : X → ℝ) (v : X → Y) (a : X),
    TotalDifferentiableAt U u a → TotalDifferentiableAt U v a →
    TotalDifferentiableAt U (fun x => u x • v x) a ∧
      ∀ h, totalDerivative (fun x => u x • v x) a h =
        totalDerivative u a h • v a + u a • totalDerivative v a h

def matrix_mul_totalDerivativeType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X],
  ∀ {r s t : ℕ} (U : Set X) (u : X → Matrix (Fin r) (Fin s) ℝ)
    (v : X → Matrix (Fin s) (Fin t) ℝ) (a : X),
    TotalDifferentiableAt U u a → TotalDifferentiableAt U v a →
    TotalDifferentiableAt U (fun x => u x * v x) a ∧
      ∀ h, totalDerivative (fun x => u x * v x) a h =
        totalDerivative u a h * v a + u a * totalDerivative v a h

def inner_totalDerivativeType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X],
  ∀ {n : ℕ} (U : Set X) (u v : X → E n) (a : X),
    TotalDifferentiableAt U u a → TotalDifferentiableAt U v a →
    TotalDifferentiableAt U (fun x => inner ℝ (u x) (v x)) a ∧
      ∀ h, totalDerivative (fun x => inner ℝ (u x) (v x)) a h =
        inner ℝ (totalDerivative u a h) (v a) + inner ℝ (u a) (totalDerivative v a h)

def cross_totalDerivativeType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X],
  ∀ (U : Set X) (u v : X → E 3) (a : X),
    TotalDifferentiableAt U u a → TotalDifferentiableAt U v a →
    TotalDifferentiableAt U (fun x => Model.cross (u x) (v x)) a ∧
      ∀ h, totalDerivative (fun x => Model.cross (u x) (v x)) a h =
        Model.cross (totalDerivative u a h) (v a) + Model.cross (u a) (totalDerivative v a h)

end Specs.D04.C02.BilinearRules
