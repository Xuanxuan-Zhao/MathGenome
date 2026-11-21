import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ExtremaInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge

/-! Independent propositions for d04:05:existence-fermat.
The ambient representation uses arbitrary extensions off the feasible set.
Curve feasibility is local at zero, so curves on any neighborhood (or right
neighborhood) are admitted. No regularity of the feasible set is imposed.
Pointwise total differentiability suffices for all first-order conclusions. -/
noncomputable section
open Set Filter Topology
namespace Specs.D04.C05.ExistenceFermat
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C05.ExtremaInterfaces.Model

def compact_global_extremaType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : E n → ℝ),
    Compact S → S.Nonempty → ContinuousOn f S →
      ∃ a b : E n, GlobalMinimumOn S f a ∧ GlobalMaximumOn S f b

/-- Literal functions on the feasible-set subtype are also covered. -/
def compact_global_extrema_subtypeType : Prop :=
  ∀ {n : ℕ} (S : Set (E n)) (f : S → ℝ),
    Compact S → S.Nonempty → Continuous f →
      ∃ a b : S, ∀ x : S, f a ≤ f x ∧ f x ≤ f b

def fermat_minimumType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TotalDifferentiableAt U f a → LocalMinimumOn U f a → totalDerivative f a = 0

def fermat_maximumType : Prop :=
  ∀ {n : ℕ} (U : Set (E n)) (f : E n → ℝ) (a : E n),
    TotalDifferentiableAt U f a → LocalMaximumOn U f a → totalDerivative f a = 0

def feasible_curve_minimumType : Prop :=
  ∀ {n : ℕ} (U S : Set (E n)) (f : E n → ℝ) (a : E n)
    (γ : ℝ → E n) (v : E n),
    TotalDifferentiableAt U f a → LocalMinimumOn S f a → γ 0 = a →
    HasDerivAt γ v 0 → (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ S) → totalDerivative f a v = 0

def feasible_curve_maximumType : Prop :=
  ∀ {n : ℕ} (U S : Set (E n)) (f : E n → ℝ) (a : E n)
    (γ : ℝ → E n) (v : E n),
    TotalDifferentiableAt U f a → LocalMaximumOn S f a → γ 0 = a →
    HasDerivAt γ v 0 → (∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ S) → totalDerivative f a v = 0

/-- Only the right derivative and right-local feasibility are assumed.
The ambient values of γ for negative times are immaterial. -/
def feasible_right_curve_minimumType : Prop :=
  ∀ {n : ℕ} (U S : Set (E n)) (f : E n → ℝ) (a : E n)
    (γ : ℝ → E n) (v : E n),
    TotalDifferentiableAt U f a → LocalMinimumOn S f a → γ 0 = a →
    HasDerivWithinAt γ v (Ici 0) 0 →
    (∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, γ t ∈ S) → 0 ≤ totalDerivative f a v

def feasible_right_curve_maximumType : Prop :=
  ∀ {n : ℕ} (U S : Set (E n)) (f : E n → ℝ) (a : E n)
    (γ : ℝ → E n) (v : E n),
    TotalDifferentiableAt U f a → LocalMaximumOn S f a → γ 0 = a →
    HasDerivWithinAt γ v (Ici 0) 0 →
    (∀ᶠ t in 𝓝[Ici (0 : ℝ)] 0, γ t ∈ S) → totalDerivative f a v ≤ 0

end Specs.D04.C05.ExistenceFermat
