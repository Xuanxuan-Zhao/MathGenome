import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.NormalizerLatticeAction
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.TorusCentralizer
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FppfTorsors

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.WeylScheme

open GeometricRadicals (IsMaximalTorus IsReductive IsSplitTorus IsTorus baseChangedSubgroup)
open NormalizerLatticeAction (SplitImage)
open Unipotent (IsFppfGroupQuotient closedSubgroupAlgebraicGroup)

variable {k : Type u} [Field k]
set_option backward.isDefEq.respectTransparency false

/-- A scheme fibre of the quotient at a rational point, with right translation
by the torus through its inclusion in the normalizer. -/
def FibreTorsor {T N W : GroupScheme k} (j : T ⟶ N) (q : N ⟶ W)
    (w : 𝟙_ (SchemeOver k) ⟶ W.X) : Prop :=
  ∃ (P : Over (Fppf.fieldBase k)) (p : P.left ⟶ N.X)
    (a : Fppf.SchemeRightAction P T),
    IsPullback p (toUnit P.left) q.hom.hom w ∧
    Fppf.IsTorsor (Fppf.representedAction a) ∧
    ∀ (Y : Over (Fppf.fieldBase k)) (x : Y ⟶ P) (t : Y.left ⟶ T.X),
      (Fppf.actionPair x t ≫ a.action).left ≫ p =
        (x.left ≫ p) * (show Y.left ⟶ N.X from t ≫ j.hom.hom)

/-- For a geometrically maximal torus in a connected reductive group, the
right fppf quotient of its scheme normalizer by the torus is finite étale.
Over any splitting field it is the constant finite subgroup of character
lattice automorphisms induced by conjugation. For a split torus over the
ground field the fibres are right torus torsors and every rational Weyl
element lifts to a rational point of the scheme normalizer. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsTorus T.group →
      (∃ h : IsClosedImmersion
          ((groupBaseChange k (AlgebraicClosure k)).map T.inclusion).hom.hom.left,
        IsMaximalTorus (baseChangedSubgroup (AlgebraicClosure k) T h)) →
      ∃ (N : ClosedSubgroup G.val) (j : T.group ⟶ N.group)
        (hj : IsClosedImmersion j.hom.hom.left)
        (W : AffineAlgebraicGroup k) (q : N.group ⟶ W.val),
        RepresentsSubgroup N (fun _ g ↦ Normalizes T.inclusion g) ∧
        j ≫ N.inclusion = T.inclusion ∧
        IsFppfGroupQuotient (G := closedSubgroupAlgebraicGroup N) ⟨_, j, hj⟩ q ∧
        IsFinite W.val.X.hom ∧ Etale W.val.X.hom ∧
        (∀ (K : Type u) [Field K] [Algebra k K],
          let F := groupBaseChange k K
          IsSplitTorus (F.obj T.group) →
            Nonempty (SplitImage (F.map T.inclusion) (F.map N.inclusion) (F.map q))) ∧
        (IsSplitTorus T.group →
          Nonempty (SplitImage T.inclusion N.inclusion q) ∧
          ∀ w : 𝟙_ (SchemeOver k) ⟶ W.val.X,
            FibreTorsor j q w ∧ ∃ n : 𝟙_ (SchemeOver k) ⟶ N.group.X, n ≫ q.hom.hom = w)

end LinearAlgebraicGroups.Specs.WeylScheme
