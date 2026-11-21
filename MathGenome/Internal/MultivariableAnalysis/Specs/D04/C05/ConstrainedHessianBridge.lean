import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.RegularLevel
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.Symmetry

/-! Independent statements for the fixed-multiplier chart calculation in
chapters/05.tex, constrained-second-variation and fixed-multiplier.
All dimensions, including zero constraints and zero tangent dimension, are allowed. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C05.ConstrainedHessianBridge
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
open Specs.D04.C03.Symmetry.Model
open Specs.D04.C04.RegularLevel.Model
namespace Model
/-- The covector lam is a constant parameter, not a function of x. -/
def lagrangian {n q : ℕ} (f : E n → ℝ) (g : E n → E q)
    (lam : E q →L[ℝ] ℝ) : E n → ℝ := fun x => f x - lam (g x)
end Model
open Model

def lagrangianType := {n q : ℕ} → (E n → ℝ) → (E n → E q) →
  (E q →L[ℝ] ℝ) → E n → ℝ
def lagrangianValue : lagrangianType := @lagrangian

/-- The linear-covector definition is the source's finite-coordinate Lagrangian. -/
def lagrangian_coordinatesType : Prop :=
  ∀ {n q : ℕ} (f : E n → ℝ) (g : E n → E q)
    (lam : E q →L[ℝ] ℝ) (x : E n),
    lagrangian f g lam x = f x - ∑ i : Fin q, lam (standardBasis q i) * g x i

/-- A graph chart identifies its coordinate space with the tangent kernel.
The displayed equality specifies the isomorphism, not just its existence. -/
def chart_tangent_isomorphismType : Prop :=
  ∀ {n q : ℕ} {U : Set (E n)} {g : E n → E q} {c : E q},
    IsOpen U → ContDiffOn ℝ 2 g U →
    ∀ (d : LevelGraph 2 U g c) (u : E (n-q)), u ∈ d.A →
      ∃ e : E (n-q) ≃L[ℝ] LinearMap.ker (fderiv ℝ g (d.θ u)).toLinearMap,
        ∀ w, (e w : E n) = fderiv ℝ d.θ u w

/-- Stationarity alone gives zero chart derivative and the tangent second variation.
The base point a is θ(u); the level and ambient-domain memberships are supplied
by the regular-level graph data. There is no extremum or definiteness premise. -/
def chart_second_variationType : Prop :=
  ∀ {n q : ℕ} {U : Set (E n)} {f : E n → ℝ} {g : E n → E q} {c : E q},
    IsOpen U → ContDiffOn ℝ 2 f U → ContDiffOn ℝ 2 g U →
    ∀ (lam : E q →L[ℝ] ℝ) (d : LevelGraph 2 U g c)
      (u : E (n-q)) (a : E n), u ∈ d.A → d.θ u = a →
      Function.Surjective (fderiv ℝ g a) →
      fderiv ℝ f a = lam.comp (fderiv ℝ g a) →
      fderiv ℝ (lagrangian f g lam) a = 0 ∧
      fderiv ℝ (f ∘ d.θ) u = 0 ∧
      ∀ w : E (n-q),
        higherDifferential 2 (f ∘ d.θ) u ![w,w] =
          higherDifferential 2 (lagrangian f g lam) a
            ![fderiv ℝ d.θ u w, fderiv ℝ d.θ u w]

/-- Entrywise identity for the actual ordered-partial Hessians from chapter 3.
The coefficients of the covector are its values on the standard basis. -/
def fixed_multiplier_hessianType : Prop :=
  ∀ {n q : ℕ} {U : Set (E n)} {f : E n → ℝ} {g : E n → E q},
    IsOpen U → ContDiffOn ℝ 2 f U → ContDiffOn ℝ 2 g U →
    ∀ (lam : E q →L[ℝ] ℝ) (a : E n), a ∈ U →
      hessian (lagrangian f g lam) a = hessian f a -
        ∑ i : Fin q, lam (standardBasis q i) • hessian (fun x => g x i) a

end Specs.D04.C05.ConstrainedHessianBridge
