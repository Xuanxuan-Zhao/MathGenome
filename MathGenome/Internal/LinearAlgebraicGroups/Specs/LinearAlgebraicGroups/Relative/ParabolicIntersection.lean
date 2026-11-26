import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Relative.RationalCocharacter
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.UnipotentRadicalIntersection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.ParabolicIntersection

open BorelProper (IsParabolic)
open CharacterDescent (Cocharacter)
open GeometricRadicals (GeometricGroup IsMaximalTorus IsReductive baseChangedSubgroup)
open SchemeDerivedGroup (IsSubgroupOf)
open StandardParabolicLevi (IsContractingRadical)
open Unipotent (closedSubgroupAlgebraicGroup)
open UnipotentRadicalIntersection (IsSchemeIntersection)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition multiplyFactors)

variable {k : Type u} [Field k]

/-- A maximal torus of the geometric ambient group lies in both geometric
parabolics. In particular their scheme intersection has full geometric rank. -/
def CommonGeometricMaximalTorus {G : AffineAlgebraicGroup k}
    (P Q : ClosedSubgroup G.val) : Prop :=
  ∃ (hp : IsClosedImmersion
        ((groupBaseChange k (AlgebraicClosure k)).map P.inclusion).hom.hom.left)
    (hq : IsClosedImmersion
        ((groupBaseChange k (AlgebraicClosure k)).map Q.inclusion).hom.hom.left)
    (T : ClosedSubgroup (GeometricGroup G).val),
    IsMaximalTorus T ∧
      IsSubgroupOf T (baseChangedSubgroup (AlgebraicClosure k) P hp) ∧
      IsSubgroupOf T (baseChangedSubgroup (AlgebraicClosure k) Q hq)

/-- The geometric maximal torus and the smooth geometrically connected
scheme-theoretic intersection of two parabolics over any field. -/
def IntersectionGeometry : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P Q : ClosedSubgroup G.val),
    IsParabolic G P → IsParabolic G Q →
    CommonGeometricMaximalTorus P Q ∧
      ∃ H : ClosedSubgroup G.val,
        IsSchemeIntersection {P, Q} H ∧
          Smooth H.group.X.hom ∧ GeometricallyConnected H.group.X.hom ∧
          ∃ (hh : IsClosedImmersion
                ((groupBaseChange k (AlgebraicClosure k)).map H.inclusion).hom.hom.left)
            (T : ClosedSubgroup (GeometricGroup G).val),
            IsMaximalTorus T ∧
              IsSubgroupOf T (baseChangedSubgroup (AlgebraicClosure k) H hh)

/-- The projection is the limit map of a cocharacter defining P. Its kernel is
the geometric unipotent radical and its section identifies the reductive
quotient with a Levi. The inverse image is the fppf product of the
intersection and that radical. -/
def IntersectionProjection : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P Q : ClosedSubgroup G.val),
    IsParabolic G P → IsParabolic G Q →
    ∃ (H : ClosedSubgroup G.val) (a : H.group ⟶ P.group)
      (c : Cocharacter G.val) (D : LimitDecomposition c) (e : P.group ≅ D.parabolic.group),
      IsSchemeIntersection {P, Q} H ∧
      a ≫ P.inclusion = H.inclusion ∧
      e.hom ≫ D.parabolic.inclusion = P.inclusion ∧
      IsContractingRadical D ∧
      let L := closedSubgroupAlgebraicGroup D.centralizer
      ∃ (I : ClosedSubgroup L.val) (p : H.group ⟶ I.group)
        (J : ClosedSubgroup P.group) (q : J.group ⟶ I.group),
        IsParabolic L I ∧
        IsImageFactorization (a ≫ e.hom ≫ D.limit) p I.inclusion ∧
        IsCanonicalImage (a ≫ e.hom ≫ D.limit) p I.inclusion ∧
        IsPullback J.inclusion.hom.hom q.hom.hom
          (e.hom ≫ D.limit).hom.hom I.inclusion.hom.hom ∧
        IsParabolic G (GeometricBorelConjugacy.subgroupOfSubgroup P J) ∧
        ∃ (U : ClosedSubgroup P.group) (m : H.group.X ⊗ U.group.X ⟶ J.group.X),
          IsSchemeKernel (e.hom ≫ D.limit) U ∧
            m ≫ J.inclusion.hom.hom = multiplyFactors a U.inclusion ∧
            Flat m.left ∧ Surjective m.left ∧ LocallyOfFinitePresentation m.left ∧
            IsAffineHom m.left

end LinearAlgebraicGroups.Specs.ParabolicIntersection
