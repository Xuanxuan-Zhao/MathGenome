import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.GermsContinuation
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-! Monodromy, paper.tex:3244–3262. Paths are arbitrary continuous paths
on the unit interval. `IsSimplyConnected` is the usual topological predicate;
its fixed-endpoint path-homotopy characterization is used in the proof.
Total functions represent functions on Ω, so uniqueness is equality on Ω.
Germs and holomorphy are the canonical upstream objects. -/
noncomputable section
namespace Specs.D12Complex.Ch19.Monodromy
open _root_.D12Complex

/-- Existence, uniqueness on the domain, and the terminal germ for every path
and every continuation of the prescribed germ. -/
def monodromy_type : Prop :=
  ∀ (Ω : Set ℂ) (a : ℂ) (_hΩ : IsDomain Ω) (ha : a ∈ Ω),
    IsSimplyConnected Ω → ∀ φ : HolomorphicGerm a,
    (∀ (b : ℂ) (γ : Path a b), (∀ t, γ t ∈ Ω) →
      ∃ Φ : GermFamily γ,
        IsContinuation Ω γ (γ.source.symm ▸ φ) Φ) →
    ∃ (f : ℂ → ℂ) (hf : HolomorphicOn Ω f),
      HolomorphicGerm.ofFunction f hf ha = φ ∧
      (∀ (b : ℂ) (hb : b ∈ Ω) (γ : Path a b) (_hγ : ∀ t, γ t ∈ Ω)
        (Φ : GermFamily γ),
        IsContinuation Ω γ (γ.source.symm ▸ φ) Φ →
        Eq.mp (congrArg HolomorphicGerm γ.target) (Φ 1) =
          HolomorphicGerm.ofFunction f hf hb) ∧
      ∀ (g : ℂ → ℂ) (hg : HolomorphicOn Ω g),
        HolomorphicGerm.ofFunction g hg ha = φ → Set.EqOn g f Ω

end Specs.D12Complex.Ch19.Monodromy
