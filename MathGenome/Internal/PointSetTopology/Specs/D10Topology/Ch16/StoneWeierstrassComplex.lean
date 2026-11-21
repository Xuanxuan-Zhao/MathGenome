import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.SupNormAlgebras

/-! Independent statements for `paper.tex`, `d10:16:stone-weierstrass-complex`.
The algebra and uniform topology are the canonical chapter 16 objects.
In particular the complex norm is the supremum norm, conjugation invariance
is an explicit hypothesis, and the domain need not be nonempty. -/

noncomputable section
open Set
universe u

namespace Specs.D10Topology.Ch16.StoneWeierstrassComplex
open SupNormAlgebras

/-- Approximation in the complex uniform norm by the original algebra. -/
def stone_weierstrass_complex : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : ComplexFunctionAlgebra X), SupNormAlgebras.IsUnital A →
    SeparatesPoints (A : Set C(X, ℂ)) →
    ConjugationInvariant (A : Set C(X, ℂ)) →
    ∀ (f : C(X, ℂ)) (ε : ℝ), 0 < ε →
      ∃ a ∈ A, supNorm (f - a) < ε

/-- Density in chapter 13's uniform topology. -/
def stone_weierstrass_complex_closure : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : ComplexFunctionAlgebra X), SupNormAlgebras.IsUnital A →
    SeparatesPoints (A : Set C(X, ℂ)) →
    ConjugationInvariant (A : Set C(X, ℂ)) →
    uniformClosure (A : Set C(X, ℂ)) = Set.univ

end Specs.D10Topology.Ch16.StoneWeierstrassComplex
