import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeBridge

/-! Independent statements for chapters/02.tex, `d04:02:quotient-rule`.
The scalar denominator has target ℝ. Vector division by it means inverse
scalar multiplication. The generic statements include all Euclidean source
and target dimensions, including zero. Differentiability is required only
at the basepoint, on the shared open domain; no continuity of derivatives
or nonvanishing throughout that domain is assumed. Ambient inverses are
used as extensions of the reciprocal on the nonzero neighborhood. -/
noncomputable section
open Set
namespace Specs.D04.C02.QuotientRule
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model

def denominator_nonzero_neighborhoodType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : Set X) (q : X → ℝ) (a : X),
    TotalDifferentiableAt U q a → q a ≠ 0 →
      ∃ r : ℝ, 0 < r ∧ Metric.ball a r ⊆ U ∧
        ∀ x ∈ Metric.ball a r, q x ≠ 0

def reciprocal_hasTotalDerivativeType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : Set X) (q : X → ℝ) (A : X →L[ℝ] ℝ) (a : X),
    HasTotalDerivative U q A a → q a ≠ 0 →
      HasTotalDerivative U (fun x => (q x)⁻¹) (-(q a ^ 2)⁻¹ • A) a

def reciprocal_ruleType : Prop :=
  ∀ {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (U : Set X) (q : X → ℝ) (a : X),
    TotalDifferentiableAt U q a → q a ≠ 0 →
      TotalDifferentiableAt U (fun x => (q x)⁻¹) a ∧
        ∀ h, totalDerivative (fun x => (q x)⁻¹) a h =
          -(totalDerivative q a h) / q a ^ 2

def quotient_ruleType : Prop :=
  ∀ {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : Set X) (u : X → Y) (q : X → ℝ) (a : X),
    TotalDifferentiableAt U u a → TotalDifferentiableAt U q a → q a ≠ 0 →
      TotalDifferentiableAt U (fun x => (q x)⁻¹ • u x) a ∧
        ∀ h, totalDerivative (fun x => (q x)⁻¹ • u x) a h =
          (q a)⁻¹ • totalDerivative u a h -
            (totalDerivative q a h / q a ^ 2) • u a

end Specs.D04.C02.QuotientRule
