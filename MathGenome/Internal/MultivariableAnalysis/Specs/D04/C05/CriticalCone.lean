import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.CriticalConeNecessity

/-! Independent statements of the full critical-cone test, with h ≥ 0.
The multipliers are held fixed in the Lagrangian. No nonzero direction,
nonempty sphere section, or strict complementarity is assumed. -/
noncomputable section
open Set
namespace Specs.D04.C05.CriticalCone
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
open Specs.D04.C05.ExtremaInterfaces.Model
open Specs.D04.C05.ActiveConstraintCoordinates
open Specs.D04.C05.ActiveConstraints
open Specs.D04.C05.CriticalConeNecessity

def critical_cone_necessaryType : Prop := critical_cone_necessityType

def critical_cone_sufficientType : Prop :=
  ∀ {n q s : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (h : E n → E s) (c : E q) (a : E n) (lam : Fin q → ℝ) (μ : Fin s → ℝ),
    IsOpen U → CrOn 2 U f → CrOn 2 U g → CrOn 2 U h →
    a ∈ Feasible U g h c → LinearIndependent ℝ (constraintRows g h a) →
    (∀ i, 0 ≤ μ i) → (∀ i, h a i ≠ 0 → μ i = 0) →
    (∀ v : E n, totalDerivative f a v =
      (∑ j, lam j * totalDerivative (fun x => g x j) a v) +
      ∑ i, μ i * totalDerivative (fun x => h x i) a v) →
    (∀ v ∈ criticalCone f g h a, v ≠ 0 →
      0 < higherDifferential 2 (lagrangian f g h lam μ) a (fun _ => v)) →
    StrictLocalMinimumOn (Feasible U g h c) f a ∧
      ∃ c₀ > 0, ∃ ρ > 0, ∀ x ∈ Feasible U g h c,
        ‖x - a‖ < ρ → f a + c₀ * ‖x - a‖ ^ 2 ≤ f x

end Specs.D04.C05.CriticalCone
