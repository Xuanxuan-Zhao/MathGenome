import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic

/-!
Independent statement of paper.tex:490–500 and 1341–1353.
The premise is holomorphy on an open neighborhood, without any assumed
continuity of the derivative. The witnesses use the project's canonical
`BiholomorphicPair`, which includes openness, both mapping conditions and
both inverse identities. Total functions are constrained only on their sets.
-/

namespace Specs.D12Complex.Ch05.LocalHolomorphicInverse

open _root_.D12Complex

/-- A noncritical point has a holomorphic inverse on open neighborhoods.
The source is contained in the original set and can be chosen to have no
critical points. The inverse derivative formula holds on the entire target. -/
def local_holomorphic_inverse_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ) (a : ℂ),
    HolomorphicOn Ω f → a ∈ Ω → deriv f a ≠ 0 →
    ∃ (U V : Set ℂ) (h : ℂ → ℂ),
      a ∈ U ∧ f a ∈ V ∧ U ⊆ Ω ∧
      BiholomorphicPair U V f h ∧
      (∀ z ∈ U, deriv f z ≠ 0) ∧
      ∀ w ∈ V, HasDerivAt h (1 / deriv f (h w)) w ∧
        deriv h w = 1 / deriv f (h w)

end Specs.D12Complex.Ch05.LocalHolomorphicInverse
