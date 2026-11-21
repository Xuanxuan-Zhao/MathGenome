import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces

/-! Independent propositions for chapters/02.tex, d04:02:zero-derivative.
The norm inequalities are the definition of Lipschitz continuity on the
specified set. All dimensions range over ℕ, including zero. Constancy is
expressed by universal pairs, including when the domain is empty. -/
noncomputable section
open Set
namespace Specs.D04.C02.LipschitzConstancy
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model

def lipschitz_of_totalDerivative_boundType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m) (M : ℝ),
    IsOpen U → ConvexSet U → TotalDifferentiableOn U f →
    0 ≤ M → (∀ x ∈ U, ‖totalDerivative f x‖ ≤ M) →
    ∀ x ∈ U, ∀ y ∈ U, ‖f y - f x‖ ≤ M * ‖y - x‖

def constant_of_totalDerivative_zeroType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m),
    IsOpen U → Connected U → TotalDifferentiableOn U f →
    (∀ x ∈ U, totalDerivative f x = 0) →
    ∀ x ∈ U, ∀ y ∈ U, f x = f y

def locally_lipschitz_of_crOn_oneType : Prop :=
  ∀ {n m : ℕ} (U : Set (E n)) (f : E n → E m),
    IsOpen U → CrOn 1 U f → ∀ a ∈ U,
    ∃ r > 0, Metric.ball a r ⊆ U ∧
      ∃ M : ℝ, 0 ≤ M ∧
        ∀ x ∈ Metric.ball a r, ∀ y ∈ Metric.ball a r,
          ‖f y - f x‖ ≤ M * ‖y - x‖

end Specs.D04.C02.LipschitzConstancy
