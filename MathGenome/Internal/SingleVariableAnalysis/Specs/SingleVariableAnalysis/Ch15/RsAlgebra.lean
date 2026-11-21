import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsSums
import Mathlib.Analysis.RCLike.Basic

/-! Independent propositions for K03.15.rs_algebra, paper.tex:3707–3720.
`RCLike` includes both canonical scalar fields ℝ and ℂ. No regularity,
monotonicity or variation bound on the integrator is imposed. The interval
statement includes reversed and degenerate intervals via the upstream convention.
In particular all restrictions use the original functions and endpoint values. -/
namespace Specs.SingleVariableAnalysis.Ch15.RsAlgebra
open RsSums

/-- Scalar linearity, including complex coefficients for complex integrands. -/
def integrandLinearity : Prop :=
  ∀ {K : Type} [RCLike K] (a b : ℝ) (f g : ℝ → K) (α : ℝ → ℝ)
    (I J r s : K),
    integralValue a b f α I → integralValue a b g α J →
    integralValue a b (fun x => r * f x + s * g x) α (r * I + s * J)

/-- Real linearity in the real integrator. -/
def integratorLinearity : Prop :=
  ∀ {K : Type} [RCLike K] (a b : ℝ) (f : ℝ → K) (α β : ℝ → ℝ)
    (I J : K) (r s : ℝ),
    integralValue a b f α I → integralValue a b f β J →
    integralValue a b f (fun x => r * α x + s * β x) (r • I + s • J)

/-- Both directions of integrability and the identity of values, for every
intermediate point, including the endpoints and either orientation. -/
def intervalAdditivity : Prop :=
  ∀ {K : Type} [RCLike K] (a b c : ℝ) (_hc : c ∈ Set.uIcc a b)
    (f : ℝ → K) (α : ℝ → ℝ) (L : K),
    integralValue a b f α L ↔
      ∃ I J : K, integralValue a c f α I ∧ integralValue c b f α J ∧ L = I + J

end Specs.SingleVariableAnalysis.Ch15.RsAlgebra
