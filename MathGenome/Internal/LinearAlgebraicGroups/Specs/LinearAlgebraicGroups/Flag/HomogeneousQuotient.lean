import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.QuotientEmbedding
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FppfTorsors
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.NormalAffineQuotient

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.HomogeneousQuotient

noncomputable section

open QuotientEmbedding (Presentation)

variable {k : Type u} [Field k] {G : GroupScheme k}

/-- Right multiplication on the ambient group by the given subgroup. -/
def rightMultiplication (H : ClosedSubgroup G) :
    G.X ⨯ H.group.X ⟶ G.X :=
  prod.fst * (prod.snd ≫ H.inclusion.hom.hom)

/-- The kernel pair of the quotient projection has the specified right-multiplication map. -/
def QuotientPullback : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} {H : ClosedSubgroup G}
    (Q : Presentation H), IsPullback prod.fst (rightMultiplication H) Q.projection Q.projection

/-- The action on a quotient presentation is the original right multiplication.
Its comparison map is the isomorphism sending `(g,h)` to `(g,gh)`. -/
def IsQuotientTorsor {H : ClosedSubgroup G} (Q : Presentation H) : Prop :=
  ∃ a : Fppf.SchemeRightAction (Over.mk Q.projection) H.group,
    a.action.left = rightMultiplication H ∧
    IsIso (Fppf.comparison a) ∧ Fppf.IsTorsor (Fppf.representedAction a)

/-- Every quasi-projective representative carries the quotient torsor, and one exists
for each finite-type affine group and closed subgroup. -/
def RepresentabilityAndTorsor : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val),
    Nonempty (Presentation H) ∧
    ∀ Q : Presentation H, IsQuotientTorsor Q ∧
      (Smooth H.group.X.hom → Smooth Q.projection.left)

/-- Any two representatives are uniquely isomorphic over the quotient projection. -/
def QuotientUniqueness : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} {H : ClosedSubgroup G}
    (Q Q' : Presentation H), ∃! e : Q.scheme ≅ Q'.scheme,
      Q.projection ≫ e.hom = Q'.projection

/-- The base change of a representative represents the same right-coset quotient
formed over the extension field, with the base-changed quotient map. -/
def QuotientBaseChange : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    {G : GroupScheme k} {H : ClosedSubgroup G} (Q : Presentation H),
    ∃ hs : IsClosedImmersion ((groupBaseChange k K).map H.inclusion).hom.hom.left,
      let H' : ClosedSubgroup ((groupBaseChange k K).obj G) :=
        ⟨(groupBaseChange k K).obj H.group, (groupBaseChange k K).map H.inclusion, hs⟩
      ∃ e : rightQuotientSheaf H' ≅ schemeFppfSheaf ((baseChange k K).obj Q.scheme),
        rightQuotientProjection H' ≫ e.hom =
          (fppfOver K).uliftYoneda.map ((baseChange k K).map Q.projection)

/-- For a normal subgroup, the quasi-projective representative itself identifies
with the affine group furnished by the scheme-theoretic image factorization. -/
def QuotientAffineComparison : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val)
    (Q : Presentation H), IsNormalSubgroup H.inclusion →
    ∃ (L A : AffineAlgebraicGroup k) (f : G.val ⟶ L.val) (q : G.val ⟶ A.val)
      (i : A.val ⟶ L.val) (e : Q.scheme ≅ A.val.X),
      IsSchemeKernel f H ∧ IsSchemeKernel q H ∧
      IsImageFactorization f q i ∧ IsCanonicalImage f q i ∧
      Q.projection ≫ e.hom = q.hom.hom

open StandardGroups in
/-- The projective linear group is the affine group representative of the
right fppf quotient of the determinant localization by the scalar torus.
The inclusion on every test algebra is `u ↦ u I`. -/
def ProjectiveLinearQuotient : Prop :=
  ∀ (k : Type u) [Field k] (I : Type u) [Fintype I] [DecidableEq I] [Nonempty I],
    ∃ (hm : HopfOperations k (LaurentPolynomial k))
      (hl : HopfOperations k (GLCoordinates k I)),
      letI := hm.hopf
      letI := hl.hopf
      let M := spectrum k (LaurentPolynomial k)
      let L := spectrum k (GLCoordinates k I)
      ∃ (em : (groupPointsFunctor k).obj M.val ≅ multiplicativePoints k)
        (el : (groupPointsFunctor k).obj L.val ≅ generalLinearPoints k I)
        (s : M.val ⟶ L.val) (hs : IsClosedImmersion s.hom.hom.left),
        (∀ (R : TestAlgebra k) (a : Points M.val.X R),
          el.hom.app R (a ≫ s.hom.hom) = Matrix.GeneralLinearGroup.scalar I (em.hom.app R a)) ∧
        IsNormalSubgroup s ∧
        let H : ClosedSubgroup L.val := ⟨M.val, s, hs⟩
        ∃ (P : Presentation H) (PGL : AffineAlgebraicGroup k) (q : L.val ⟶ PGL.val)
          (e : P.scheme ≅ PGL.val.X),
          IsQuotientTorsor P ∧ IsSchemeKernel q H ∧ P.projection ≫ e.hom = q.hom.hom

end

end LinearAlgebraicGroups.Specs.HomogeneousQuotient
