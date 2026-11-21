import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ExtremaInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.Symmetry
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Convex.Function

/-! Independent statements for d04:05:convexity. Domain convexity and openness
are explicit hypotheses. Functions are ambient representatives restricted to U.
The Hessian is the shared second differential, evaluated twice on a direction. -/
noncomputable section
open Set
namespace Specs.D04.C05.Convexity
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
open Specs.D04.C05.ExtremaInterfaces.Model
namespace Model

def ScalarConvexOn {n : ℕ} (U : Set (E n)) (f : E n → ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, ∀ t ∈ Icc (0 : ℝ) 1,
    f ((1-t) • x + t • y) ≤ (1-t) * f x + t * f y

def ScalarStrictConvexOn {n : ℕ} (U : Set (E n)) (f : E n → ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U, x ≠ y → ∀ t ∈ Ioo (0 : ℝ) 1,
    f ((1-t) • x + t • y) < (1-t) * f x + t * f y
end Model
open Model

abbrev ScalarConvexOnType := {n : ℕ} → Set (E n) → (E n → ℝ) → Prop
def ScalarConvexOnValue : ScalarConvexOnType := @ScalarConvexOn
abbrev ScalarStrictConvexOnType := {n : ℕ} → Set (E n) → (E n → ℝ) → Prop
def ScalarStrictConvexOnValue : ScalarStrictConvexOnType := @ScalarStrictConvexOn

def scalarConvexOn_iff_supportingType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ), IsOpen U → Convex ℝ U →
    TotalDifferentiableOn U f →
    (ScalarConvexOn U f ↔ ∀ x ∈ U, ∀ y ∈ U,
      f x + totalDerivative f x (y-x) ≤ f y)

def scalarConvexOn_iff_hessian_nonnegType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ), IsOpen U → Convex ℝ U →
    CrOn 2 U f → (ScalarConvexOn U f ↔
      ∀ x ∈ U, ∀ v : E n, 0 ≤ differentialDiagonal (higherDifferential 2 f x) v)

def scalarStrictConvexOn_of_hessian_posType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ), IsOpen U → Convex ℝ U →
    CrOn 2 U f →
    (∀ x ∈ U, ∀ v : E n, v ≠ 0 → 0 < differentialDiagonal (higherDifferential 2 f x) v) →
    ScalarStrictConvexOn U f

def convex_stationary_globalMinimumType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    IsOpen U → Convex ℝ U → TotalDifferentiableOn U f → ScalarConvexOn U f →
    StationaryPoint U f a → GlobalMinimumOn U f a

def strictConvex_minimum_uniqueType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a b : E n),
    Convex ℝ U → ScalarStrictConvexOn U f →
    GlobalMinimumOn U f a → GlobalMinimumOn U f b → a = b

def strictConvex_stationary_uniqueMinimumType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    IsOpen U → Convex ℝ U → TotalDifferentiableOn U f → ScalarStrictConvexOn U f →
    StationaryPoint U f a →
    GlobalMinimumOn U f a ∧ ∀ b : E n, GlobalMinimumOn U f b → b = a

def convex_feasible_minimum_iffType : Prop :=
  ∀ {n : ℕ} (U S : Set (E n)) (f : E n → ℝ) (a : E n),
    IsOpen U → Convex ℝ U → S ⊆ U → Convex ℝ S → a ∈ S →
    TotalDifferentiableOn U f → ScalarConvexOn U f →
    (GlobalMinimumOn S f a ↔ ∀ x ∈ S, 0 ≤ totalDerivative f a (x-a))

/-- The same test for the coordinate Hessian matrix, including its symmetry. -/
def scalarConvexOn_iff_hessian_posSemidefType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ), IsOpen U → Convex ℝ U →
    CrOn 2 U f → (ScalarConvexOn U f ↔
      ∀ x ∈ U, (Specs.D04.C03.Symmetry.Model.hessian f x).PosSemidef)

def scalarStrictConvexOn_of_hessian_posDefType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ), IsOpen U → Convex ℝ U →
    CrOn 2 U f → (∀ x ∈ U, (Specs.D04.C03.Symmetry.Model.hessian f x).PosDef) →
    ScalarStrictConvexOn U f

end Specs.D04.C05.Convexity
