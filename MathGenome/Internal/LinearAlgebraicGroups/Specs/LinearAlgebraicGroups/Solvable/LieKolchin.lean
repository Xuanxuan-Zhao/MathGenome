import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.Triangularization

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.LieKolchin

/-- Every nonzero finite-dimensional rational representation of a smooth connected
solvable affine algebraic group over an algebraically closed field has an invariant line.
The coordinate Hopf algebra presents the given group with its group law. -/
def InvariantLine : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (A : HopfAlgebraCategory k), (((affineHopfSpec k).obj (op A)).val ≅ G.val) →
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left → SchemeDerivedGroup.IsSolvable G.val →
    ∀ (V : Type u) [AddCommGroup V] [Module k V] [FiniteDimensional k V] [Nontrivial V]
      (ρ : RightComodule k A V),
      ∃ L : Submodule k V, Module.finrank k L = 1 ∧ ρ.IsSubcomodule L

/-- Every finite-dimensional rational representation of such a group has a full invariant flag. -/
def InvariantFullFlag : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (G : AffineAlgebraicGroup k)
    (A : HopfAlgebraCategory k), (((affineHopfSpec k).obj (op A)).val ≅ G.val) →
    Smooth G.val.X.hom → ConnectedSpace G.val.X.left → SchemeDerivedGroup.IsSolvable G.val →
    Triangularization.HasInvariantFullFlags A

end LinearAlgebraicGroups.Specs.LieKolchin
