import MathGenome.Internal.RealAnalysis.Specs.D11.Ch15.RNPositiveSigmaFinite

/-! Independent statements for the chain and reciprocal rules of
`paper.tex:4965–4982`. Set integrals use the shared source integral on the
original measurable space. ENNReal multiplication includes `∞ * 0 = 0`.
The universal identities cover all measurable density representatives;
the existence statements additionally select representatives finite everywhere.
-/
open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch15.RNChainRule
open Ch05.NonnegativeIntegral

/-- The product of any two successive measurable densities represents the
composite measure and agrees a.e. with every measurable composite density. -/
def chain_rule : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (ρ μ ν : Measure X)
    [SigmaFinite ρ] [SigmaFinite μ] [SigmaFinite ν],
    ν ≪ μ → μ ≪ ρ → ∀ h k l : X → ℝ≥0∞,
    Measurable h → Measurable k → Measurable l →
    (∀ E, MeasurableSet E → ν E = nonnegativeIntegral_value (μ.restrict E) h) →
    (∀ E, MeasurableSet E → μ E = nonnegativeIntegral_value (ρ.restrict E) k) →
    (∀ E, MeasurableSet E → ν E = nonnegativeIntegral_value (ρ.restrict E) l) →
    (∀ E, MeasurableSet E →
      ν E = nonnegativeIntegral_value (ρ.restrict E) (fun x => h x * k x)) ∧
    l =ᵐ[ρ] (fun x => h x * k x)

/-- All three densities can be selected finite and measurable, with a measurable
finite product which is zero wherever the reference density is zero. -/
def chain_rule_finite_representatives : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (ρ μ ν : Measure X)
    [SigmaFinite ρ] [SigmaFinite μ] [SigmaFinite ν], ν ≪ μ → μ ≪ ρ →
    ∃ h k l : X → ℝ≥0∞,
    Measurable h ∧ Measurable k ∧ Measurable l ∧
    (∀ x, h x < ∞) ∧ (∀ x, k x < ∞) ∧ (∀ x, l x < ∞) ∧
    (∀ E, MeasurableSet E → ν E = nonnegativeIntegral_value (μ.restrict E) h) ∧
    (∀ E, MeasurableSet E → μ E = nonnegativeIntegral_value (ρ.restrict E) k) ∧
    (∀ E, MeasurableSet E → ν E = nonnegativeIntegral_value (ρ.restrict E) l) ∧
    Measurable (fun x => h x * k x) ∧ (∀ x, h x * k x < ∞) ∧
    (∀ x, k x = 0 → h x * k x = 0) ∧
    l =ᵐ[ρ] (fun x => h x * k x)

/-- Here h is dρ/dμ and k is dμ/dρ. Both almost-everywhere conclusions
refer to this same product, on the two original measures. -/
def reciprocal_rule : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (ρ μ : Measure X)
    [SigmaFinite ρ] [SigmaFinite μ], μ ≪ ρ → ρ ≪ μ →
    ∀ h k : X → ℝ≥0∞, Measurable h → Measurable k →
    (∀ E, MeasurableSet E → ρ E = nonnegativeIntegral_value (μ.restrict E) h) →
    (∀ E, MeasurableSet E → μ E = nonnegativeIntegral_value (ρ.restrict E) k) →
    (∀ᵐ x ∂ρ, h x * k x = 1) ∧ (∀ᵐ x ∂μ, h x * k x = 1)

/-- Existence of finite measurable reciprocal representatives, without an
assumption of nonzero measures or nonempty underlying space. -/
def reciprocal_finite_representatives : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (ρ μ : Measure X)
    [SigmaFinite ρ] [SigmaFinite μ], μ ≪ ρ → ρ ≪ μ →
    ∃ h k : X → ℝ≥0∞, Measurable h ∧ Measurable k ∧
    (∀ x, h x < ∞) ∧ (∀ x, k x < ∞) ∧
    (∀ E, MeasurableSet E → ρ E = nonnegativeIntegral_value (μ.restrict E) h) ∧
    (∀ E, MeasurableSet E → μ E = nonnegativeIntegral_value (ρ.restrict E) k) ∧
    (∀ᵐ x ∂ρ, h x * k x = 1) ∧ (∀ᵐ x ∂μ, h x * k x = 1)

end Specs.D11.Ch15.RNChainRule
