import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.ClusterPt

/-!
Independent statements for paper.tex:1307–1321, D12.05.04.
`AccPt a (𝓟 S)` means every neighborhood of `a` meets `S` away from
`a` itself. In particular, a single zero is insufficient. The accumulation
point must belong to the domain, but need not belong to the equality set.
-/

open Filter Set
open scoped Topology

namespace Specs.D12Complex.Ch05.IdentityTheorem
open _root_.D12Complex

/-- Accumulating distinct zeros imply vanishing throughout the domain. -/
def identity_zero_of_accPt_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ) (a : ℂ),
    IsDomain Ω → HolomorphicOn Ω f → a ∈ Ω →
    AccPt a (𝓟 {z | z ∈ Ω ∧ f z = 0}) →
    EqOn f (fun _ => 0) Ω

/-- Equality on any subset with an interior accumulation point extends
throughout the domain. No openness of the equality set is required. -/
def identity_of_accPt_type : Prop :=
  ∀ (Ω S : Set ℂ) (f g : ℂ → ℂ) (a : ℂ),
    IsDomain Ω → HolomorphicOn Ω f → HolomorphicOn Ω g →
    S ⊆ Ω → a ∈ Ω → AccPt a (𝓟 S) → EqOn f g S → EqOn f g Ω

end Specs.D12Complex.Ch05.IdentityTheorem
