import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ConstrainedHessianBridge
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ExtremaInterfaces

/-! Tangent second variation on a regular equality level (chapter 5).
The covector is fixed; the level includes the open ambient domain.
All dimensions, including a zero tangent kernel, are permitted. -/
noncomputable section
open Set
namespace Specs.D04.C05.ConstrainedSecondVariation
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
open Specs.D04.C04.RegularLevel.Model
open Specs.D04.C05.ExtremaInterfaces.Model
open Specs.D04.C05.ConstrainedHessianBridge.Model

def constrained_minimumType : Prop :=
  ∀ {n q : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (c : E q) (a : E n) (lam : E q →L[ℝ] ℝ),
    IsOpen U → ContDiffOn ℝ 2 f U → ContDiffOn ℝ 2 g U →
    a ∈ level U g c → Function.Surjective (fderiv ℝ g a) →
    fderiv ℝ f a = lam.comp (fderiv ℝ g a) →
    LocalMinimumOn (level U g c) f a →
    ∀ v, fderiv ℝ g a v = 0 → 0 ≤ higherDifferential 2 (lagrangian f g lam) a ![v,v]

def constrained_maximumType : Prop :=
  ∀ {n q : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (c : E q) (a : E n) (lam : E q →L[ℝ] ℝ),
    IsOpen U → ContDiffOn ℝ 2 f U → ContDiffOn ℝ 2 g U →
    a ∈ level U g c → Function.Surjective (fderiv ℝ g a) →
    fderiv ℝ f a = lam.comp (fderiv ℝ g a) →
    LocalMaximumOn (level U g c) f a →
    ∀ v, fderiv ℝ g a v = 0 → higherDifferential 2 (lagrangian f g lam) a ![v,v] ≤ 0

def constrained_positiveType : Prop :=
  ∀ {n q : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (c : E q) (a : E n) (lam : E q →L[ℝ] ℝ),
    IsOpen U → ContDiffOn ℝ 2 f U → ContDiffOn ℝ 2 g U →
    a ∈ level U g c → Function.Surjective (fderiv ℝ g a) →
    fderiv ℝ f a = lam.comp (fderiv ℝ g a) →
    (∀ v, fderiv ℝ g a v = 0 → v ≠ 0 → 0 < higherDifferential 2 (lagrangian f g lam) a ![v,v]) →
    StrictLocalMinimumOn (level U g c) f a ∧
    ∃ c₀ > 0, ∃ ρ > 0, ∀ x ∈ level U g c, ‖x-a‖ < ρ →
      f a + c₀ * ‖x-a‖^2 ≤ f x

def constrained_negativeType : Prop :=
  ∀ {n q : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (c : E q) (a : E n) (lam : E q →L[ℝ] ℝ),
    IsOpen U → ContDiffOn ℝ 2 f U → ContDiffOn ℝ 2 g U →
    a ∈ level U g c → Function.Surjective (fderiv ℝ g a) →
    fderiv ℝ f a = lam.comp (fderiv ℝ g a) →
    (∀ v, fderiv ℝ g a v = 0 → v ≠ 0 → higherDifferential 2 (lagrangian f g lam) a ![v,v] < 0) →
    StrictLocalMaximumOn (level U g c) f a ∧
    ∃ c₀ > 0, ∃ ρ > 0, ∀ x ∈ level U g c, ‖x-a‖ < ρ →
      f x ≤ f a - c₀ * ‖x-a‖^2

def constrained_indefiniteType : Prop :=
  ∀ {n q : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (c : E q) (a : E n) (lam : E q →L[ℝ] ℝ),
    IsOpen U → ContDiffOn ℝ 2 f U → ContDiffOn ℝ 2 g U →
    a ∈ level U g c → Function.Surjective (fderiv ℝ g a) →
    fderiv ℝ f a = lam.comp (fderiv ℝ g a) →
    (∃ v, fderiv ℝ g a v = 0 ∧ 0 < higherDifferential 2 (lagrangian f g lam) a ![v,v]) →
    (∃ v, fderiv ℝ g a v = 0 ∧ higherDifferential 2 (lagrangian f g lam) a ![v,v] < 0) →
    SaddlePoint (level U g c) f a

/-- Vanishing tangent space makes the entire feasible level locally a singleton.
No regularity of the objective is needed for the vacuous strict extrema. -/
def constrained_zero_kernelType : Prop :=
  ∀ {n q : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (c : E q) (a : E n),
    IsOpen U → ContDiffOn ℝ 2 g U → a ∈ level U g c →
    Function.Surjective (fderiv ℝ g a) →
    LinearMap.ker (fderiv ℝ g a).toLinearMap = ⊥ →
    (∃ ρ > 0, ∀ x ∈ level U g c, ‖x-a‖ < ρ → x = a) ∧
    StrictLocalMinimumOn (level U g c) f a ∧
    StrictLocalMaximumOn (level U g c) f a

end Specs.D04.C05.ConstrainedSecondVariation
