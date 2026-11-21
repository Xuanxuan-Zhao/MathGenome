import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.HolomorphicCompactness
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.IdentityTheorem

/-! Independent statement of Vitali convergence, paper.tex:2430–2435.
The pointwise limits are finite complex numbers and are required only on E.
The accumulation point lies in Ω but need not lie in E. -/

open Set Filter
open scoped Topology

namespace Specs.D12Complex.Ch11.Vitali
open _root_.D12Complex

/-- Local boundedness and convergence on an accumulating subset of a domain
give convergence of the whole sequence uniformly on every compact subset. -/
def vitali_convergence_type : Prop :=
  ∀ (Ω E : Set ℂ) (F : ℕ → ℂ → ℂ) (a : ℂ),
    IsDomain Ω → (∀ n, HolomorphicOn Ω (F n)) →
    HolomorphicCompactness.LocallyBounded_value Ω (range F) →
    E ⊆ Ω → a ∈ Ω → AccPt a (𝓟 E) →
    (∀ z ∈ E, ∃ L : ℂ, Tendsto (fun n => F n z) atTop (𝓝 L)) →
    ∃ f : ℂ → ℂ, HolomorphicOn Ω f ∧
      ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
        TendstoUniformlyOn F f atTop K

end Specs.D12Complex.Ch11.Vitali
