import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch16.SupNormAlgebras

/-! Independent statements for paper.tex, `d10:16:stone-weierstrass-real`.
The algebra, point separation, norm, and uniform topology are the canonical
chapter 16 objects. In particular no nonemptiness of the domain is assumed.
These statements contain no assumed approximation or lattice certificate. -/

noncomputable section
open Set
universe u

namespace Specs.D10Topology.Ch16.StoneWeierstrassReal
open SupNormAlgebras

/-- Strict uniform approximation by members of the original algebra. -/
def stone_weierstrass_real : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : RealFunctionAlgebra X), SupNormAlgebras.IsUnital A →
    SeparatesPoints (A : Set C(X, ℝ)) →
    ∀ (f : C(X, ℝ)) (ε : ℝ), 0 < ε →
      ∃ a ∈ A, supNorm (f - a) < ε

/-- The equivalent uniform-closure formulation in the chapter 13 topology. -/
def stone_weierstrass_real_closure : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : RealFunctionAlgebra X), SupNormAlgebras.IsUnital A →
    SeparatesPoints (A : Set C(X, ℝ)) →
    uniformClosure (A : Set C(X, ℝ)) = Set.univ

end Specs.D10Topology.Ch16.StoneWeierstrassReal
