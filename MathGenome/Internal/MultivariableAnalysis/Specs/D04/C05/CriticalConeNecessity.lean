import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C05.ActiveConstraints
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C03.HigherInterfaces
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

noncomputable section
open Set Filter Topology
namespace Specs.D04.C05.CriticalConeNecessity
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C03.HigherInterfaces.Model
open Specs.D04.C05.ExtremaInterfaces.Model
open Specs.D04.C05.ActiveConstraintCoordinates
open Specs.D04.C05.ActiveConstraints

/-- The critical cone for the convention h ≥ 0. -/
def criticalCone {n q s : ℕ} (f : E n → ℝ) (g : E n → E q)
    (h : E n → E s) (a : E n) : Set (E n) :=
  {v | totalDerivative g a v = 0 ∧
    (∀ i : Active h a, 0 ≤ totalDerivative (fun x => h x i.val) a v) ∧
    totalDerivative f a v = 0}

abbrev criticalConeType := {n q s : ℕ} → (E n → ℝ) → (E n → E q) →
  (E n → E s) → E n → Set (E n)
def criticalConeValue : criticalConeType := @criticalCone

/-- A local C² curve, feasible to the right, with affine constraint coordinates.
The identities hold on a two-sided neighborhood, so the displayed constraint
accelerations are genuine ordinary second derivatives. -/
def critical_direction_curveType : Prop :=
  ∀ {n q s : ℕ} (U : Set (E n)) (g : E n → E q) (h : E n → E s)
    (c : E q) (a v : E n),
    IsOpen U → CrOn 2 U g → CrOn 2 U h → a ∈ Feasible U g h c →
    LinearIndependent ℝ (constraintRows g h a) →
    totalDerivative g a v = 0 →
    (∀ i : Active h a, 0 ≤ totalDerivative (fun x => h x i.val) a v) →
    ∃ γ : ℝ → E n, γ 0 = a ∧ ContDiffAt ℝ 2 γ 0 ∧ HasDerivAt γ v 0 ∧
      (∀ᶠ t in 𝓝[≥] (0 : ℝ), γ t ∈ Feasible U g h c) ∧
      (∀ᶠ t in 𝓝 (0 : ℝ), g (γ t) = c ∧ ∀ i : Active h a,
        h (γ t) i.val = t * totalDerivative (fun x => h x i.val) a v) ∧
      iteratedDeriv 2 (g ∘ γ) 0 = 0 ∧
      ∀ i : Active h a, iteratedDeriv 2 (fun t => h (γ t) i.val) 0 = 0

/-- The fixed Lagrangian has nonnegative Hessian on every critical direction.
Multipliers are arbitrary supplied first-order multipliers, including zero and
inactive multipliers; neither strict complementarity nor positivity is required. -/
def critical_cone_necessityType : Prop :=
  ∀ {n q s : ℕ} (U : Set (E n)) (f : E n → ℝ) (g : E n → E q)
    (h : E n → E s) (c : E q) (a : E n) (lam : Fin q → ℝ) (μ : Fin s → ℝ),
    IsOpen U → CrOn 2 U f → CrOn 2 U g → CrOn 2 U h →
    LinearIndependent ℝ (constraintRows g h a) →
    (∀ i, 0 ≤ μ i) → (∀ i, h a i ≠ 0 → μ i = 0) →
    (∀ v : E n, totalDerivative f a v =
      (∑ j, lam j * totalDerivative (fun x => g x j) a v) +
      ∑ i, μ i * totalDerivative (fun x => h x i) a v) →
    LocalMinimumOn (Feasible U g h c) f a →
    ∀ v ∈ criticalCone f g h a,
      0 ≤ higherDifferential 2 (lagrangian f g h lam μ) a (fun _ => v)

end Specs.D04.C05.CriticalConeNecessity
