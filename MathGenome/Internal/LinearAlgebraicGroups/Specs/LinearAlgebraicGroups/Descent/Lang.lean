import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.SmoothLang
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FppfTorsors

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups
noncomputable section

/-- A left action by a group scheme, with the action identities on all test schemes. -/
structure SchemeLeftAction {k : Type u} [Field k] (G : Specs.GroupScheme k) (X : SchemeOver k) where
  action : G.X ⨯ X ⟶ X
  one : ∀ {T : SchemeOver k} (x : T ⟶ X), prod.lift (1 : T ⟶ G.X) x ≫ action = x
  mul : ∀ {T : SchemeOver k} (g h : T ⟶ G.X) (x : T ⟶ X),
    prod.lift (g * h) x ≫ action = prod.lift g (prod.lift h x ≫ action) ≫ action

abbrev SchemeLeftAction.act {k : Type u} [Field k] {G : Specs.GroupScheme k} {X T : SchemeOver k}
    (a : SchemeLeftAction G X) (g : T ⟶ G.X) (x : T ⟶ X) : T ⟶ X :=
  prod.lift g x ≫ a.action

namespace Specs

/-- Lang's rational-point theorem for a geometrically transitive action. -/
def LangRationalPoint : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (G : GroupScheme k)
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (X : SchemeOver k) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [Nonempty X.left]
    (a : SchemeLeftAction G X),
    (∀ x y : Points X (CommAlgCat.of k (AlgebraicClosure k)),
      ∃ g : Points G.X (CommAlgCat.of k (AlgebraicClosure k)), a.act g x = y) →
    Nonempty (Points X (CommAlgCat.of k k))

/-- Every right fppf torsor under a connected finite-type group scheme over a finite field
has the neutral class, whether or not its sheaf is represented by a scheme. -/
def LangFppfTorsor : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (G : GroupScheme k)
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    (hG : Presieve.IsSheaf (Fppf.torsorTopology (Fppf.fieldBase k))
      (Fppf.groupSections (Fppf.fieldBase k) G ⋙ forget GrpCat))
    (P : Fppf.FppfTorsor (Fppf.fieldBase k) G),
    (Quotient.mk _ P : Fppf.H1fppf k G) = Fppf.neutralClass hG

/-- A represented right fppf torsor under the same hypotheses has a rational point. -/
def LangRepresentedTorsor : Prop :=
  ∀ (k : Type u) [Field k] [Fintype k] (G : GroupScheme k)
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom] [ConnectedSpace G.X.left]
    {X : Over (Fppf.fieldBase k)} (a : Fppf.SchemeRightAction X G)
    (_ : Fppf.IsTorsor (Fppf.representedAction a)),
    Nonempty (Fppf.fieldBase k ⟶ X.left)

end Specs
end
end LinearAlgebraicGroups
