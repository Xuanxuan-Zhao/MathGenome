import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.FiniteContinuationChains

/-! Independent statements for paper.tex:3210–3228, d12:19-04.
The supremum is taken over the compact parameter interval. Endpoint germ
identifications use transport (initial point) and heterogeneous equality
(terminal point), solely to identify the equal basepoint fibres.
The same representatives on the same closed parameter pieces are retained. -/

open Set
noncomputable section
namespace Specs.D12Complex.Ch19.ChainStability
open _root_.D12Complex _root_.D12Complex.FiniteContinuationChains

/-- Every given finite continuation chain works uniformly for nearby paths. -/
def chain_stability_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0))
    (ψ : HolomorphicGerm (γ 1)) (c : Chain Ω γ φ ψ),
    IsDomain Ω → Continuous γ → ∃ δ : ℝ, 0 < δ ∧
      ∀ (η : unitInterval → ℂ), Continuous η → (∀ t, η t ∈ Ω) →
      ∀ h0 : η 0 = γ 0, (⨆ t, ‖η t - γ t‖) < δ →
      ∃ Ψ : GermFamily η,
        IsContinuation Ω η (h0.symm ▸ φ) Ψ ∧
        (∀ i, RepresentsOn η Ψ (c.element i).domain (c.element i).toFun
          (Icc (c.time i.castSucc) (c.time i.succ))) ∧
        (∃ hm : η 1 ∈ (c.element (Fin.last c.n)).domain,
          Ψ 1 = (c.element (Fin.last c.n)).germAt (η 1) hm) ∧
        (η 1 = γ 1 → HEq (Ψ 1) ψ)

/-- A continuation supplies one fixed chain and one bound, valid also for a
varying terminal point as long as the initial point stays fixed. -/
def continuation_chain_stability_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0))
    (Φ : GermFamily γ), IsContinuation Ω γ φ Φ →
    ∃ c : Chain Ω γ φ (Φ 1), ∃ δ : ℝ, 0 < δ ∧
      ∀ (η : unitInterval → ℂ), Continuous η → (∀ t, η t ∈ Ω) →
      ∀ h0 : η 0 = γ 0, (⨆ t, ‖η t - γ t‖) < δ →
      ∃ Ψ : GermFamily η,
        IsContinuation Ω η (h0.symm ▸ φ) Ψ ∧
        (∀ i, RepresentsOn η Ψ (c.element i).domain (c.element i).toFun
          (Icc (c.time i.castSucc) (c.time i.succ))) ∧
        (∃ hm : η 1 ∈ (c.element (Fin.last c.n)).domain,
          Ψ 1 = (c.element (Fin.last c.n)).germAt (η 1) hm) ∧
        (η 1 = γ 1 → HEq (Ψ 1) (Φ 1))

/-- The fixed-endpoint formulation of the source lemma. -/
def continuation_stability_fixed_endpoints_type : Prop :=
  ∀ (Ω : Set ℂ) (γ : unitInterval → ℂ) (φ : HolomorphicGerm (γ 0))
    (Φ : GermFamily γ), IsContinuation Ω γ φ Φ →
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (η : unitInterval → ℂ), Continuous η → (∀ t, η t ∈ Ω) →
      ∀ h0 : η 0 = γ 0, η 1 = γ 1 → (⨆ t, ‖η t - γ t‖) < δ →
      ∃ Ψ : GermFamily η,
        IsContinuation Ω η (h0.symm ▸ φ) Ψ ∧ HEq (Ψ 1) (Φ 1)

end Specs.D12Complex.Ch19.ChainStability
