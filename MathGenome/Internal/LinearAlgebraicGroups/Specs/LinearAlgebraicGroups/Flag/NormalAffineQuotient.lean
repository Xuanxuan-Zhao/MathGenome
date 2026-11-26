import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Affine.SchemeImageQuotient

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs

/-- A normal closed subgroup of an affine algebraic group is a scheme-theoretic kernel. -/
def NormalClosedSubgroupKernel : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val),
    IsNormalSubgroup H.inclusion →
    ∃ (L : AffineAlgebraicGroup k) (f : G.val ⟶ L.val), IsSchemeKernel f H

/-- The right fppf quotient by a normal closed subgroup is represented by the
affine scheme-theoretic image of a homomorphism with that subgroup as its kernel. -/
def NormalAffineQuotient : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (H : ClosedSubgroup G.val),
    IsNormalSubgroup H.inclusion →
    ∃ (L : AffineAlgebraicGroup k) (f : G.val ⟶ L.val)
      (Q : AffineAlgebraicGroup k) (q : G.val ⟶ Q.val) (i : Q.val ⟶ L.val),
      IsSchemeKernel f H ∧ IsSchemeKernel q H ∧
      IsImageFactorization f q i ∧ IsCanonicalImage f q i ∧
      ∃ e : rightQuotientSheaf H ≅ schemeFppfSheaf Q.val.X,
        rightQuotientProjection H ≫ e.hom = (fppfOver k).uliftYoneda.map q.hom.hom

end LinearAlgebraicGroups.Specs
