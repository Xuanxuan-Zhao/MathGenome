import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! Independent specification of d04:03:symmetry. The hypotheses use the
pointwise existence predicate, not continuous differentiability. All arities
and Euclidean dimensions are unrestricted natural numbers. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace Specs.D04.C03.Symmetry
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
namespace Model
/-- Row i, column j is the ordered partial ∂ᵢ∂ⱼ f. -/
def hessian {n : ℕ} (f : E n → ℝ) (a : E n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => orderedPartial [i,j] f a
end Model

def hessianType := {n : ℕ} → (E n → ℝ) → E n → Matrix (Fin n) (Fin n) ℝ
def hessianValue : hessianType := @Model.hessian

section Generic
def higherDifferential_symmetricType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (k : ℕ) (U : Set X) (f : X → Y) (a : X), TimesDifferentiableAt k U f a →
    ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → X),
      higherDifferential k f a (v ∘ σ) = higherDifferential k f a v

def crOn_timesDifferentiableAtType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (k : ℕ) (U : Set X) (f : X → Y), IsOpen U → CrOn k U f →
    ∀ a ∈ U, TimesDifferentiableAt k U f a
end Generic

section Coordinates
def orderedPartial_eq_higherDifferentialType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (is : List (Fin n)) (U : Set (E n)) (f : E n → Y) (a : E n),
    TimesDifferentiableAt is.length U f a →
      orderedPartial is f a = higherDifferential is.length f a
        (fun r => standardBasis n (is.get r))

def orderedPartial_hasDerivativeType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (is : List (Fin n)) (U : Set (E n)) (f : E n → Y) (a : E n),
    TimesDifferentiableAt (is.length+1) U f a → ∀ i : Fin n,
      HasDirectionalDerivative (orderedPartial is f) a (standardBasis n i)
        (orderedPartial (i :: is) f a)

def higherDifferential_basisType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (k : ℕ) (U : Set (E n)) (f : E n → Y) (a : E n),
    TimesDifferentiableAt k U f a → ∀ j : Fin k → Fin n,
      higherDifferential k f a (fun r => standardBasis n (j r)) =
        orderedPartial (List.ofFn j) f a

def orderedPartial_permutationType : Prop :=
  ∀ {n : ℕ} {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y],
  ∀ (k : ℕ) (U : Set (E n)) (f : E n → Y) (a : E n),
    TimesDifferentiableAt k U f a → ∀ (j : Fin k → Fin n) (σ : Equiv.Perm (Fin k)),
      orderedPartial (List.ofFn (j ∘ σ)) f a = orderedPartial (List.ofFn j) f a
end Coordinates

def crOn_orderedPartial_permutationType : Prop :=
  ∀ {n m : ℕ} (k : ℕ) (U : Set (E n)) (f : E n → E m),
    IsOpen U → CrOn k U f → ∀ a ∈ U,
      ∀ (j : Fin k → Fin n) (σ : Equiv.Perm (Fin k)),
        orderedPartial (List.ofFn (j ∘ σ)) f a = orderedPartial (List.ofFn j) f a

def hessian_applyType : Prop :=
  ∀ {n : ℕ} (f : E n → ℝ) (a : E n) (i j : Fin n),
    Model.hessian f a i j =
      directionalDerivative (fun x => directionalDerivative f x (standardBasis n j))
        a (standardBasis n i)

def hessian_symmetricType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TimesDifferentiableAt 2 U f a → (Model.hessian f a).IsSymm

def higherDifferential_two_hessianType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TimesDifferentiableAt 2 U f a → ∀ u v : E n,
      higherDifferential 2 f a ![u,v] =
        dotProduct (coordinates n u) ((Model.hessian f a).mulVec (coordinates n v))

def higherDifferential_diagonal_hessianType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TimesDifferentiableAt 2 U f a → ∀ h : E n,
      differentialDiagonal (higherDifferential 2 f a) h =
        dotProduct (coordinates n h) ((Model.hessian f a).mulVec (coordinates n h))

def quadraticTaylorTerm_hessianType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TimesDifferentiableAt 2 U f a → ∀ h : E n,
      ((Nat.factorial 2 : ℝ)⁻¹) • differentialDiagonal (higherDifferential 2 f a) h =
        (1/2 : ℝ) * dotProduct (coordinates n h) ((Model.hessian f a).mulVec (coordinates n h))

def taylorPolynomial_two_hessianType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TimesDifferentiableAt 2 U f a → ∀ h : E n,
      taylorPolynomial 2 f a h = f a + totalDerivative f a h +
        (1/2 : ℝ) * dotProduct (coordinates n h) ((Model.hessian f a).mulVec (coordinates n h))
end Specs.D04.C03.Symmetry
