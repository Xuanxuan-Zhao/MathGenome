import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.RightQuotientSheaf
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs

noncomputable section

variable {k : Type u} [Field k]

/-- The coordinate algebra of an object over the field, with its structural algebra map. -/
abbrev coordinates (X : SchemeOver k) := ((algΓ (CommRingCat.of k)).obj X).unop

/-- Pullback on coordinate algebras. -/
abbrev coordinateMap {X Y : SchemeOver k} (f : X ⟶ Y) :
    coordinates Y →ₐ[k] coordinates X :=
  ((algΓ (CommRingCat.of k)).map f).unop.hom

/-- The factor maps have the properties of a faithfully flat factorization through a closed
subgroup, with the first map of finite presentation. -/
def IsImageFactorization {G H I : GroupScheme k} (f : G ⟶ H) (p : G ⟶ I) (i : I ⟶ H) : Prop :=
  p ≫ i = f ∧ Flat p.hom.hom.left ∧ Surjective p.hom.hom.left ∧
    LocallyOfFinitePresentation p.hom.hom.left ∧ IsAffineHom p.hom.hom.left ∧
    IsClosedImmersion i.hom.hom.left

/-- A closed subgroup represents the kernel if its inclusion is the pullback of the identity
section. -/
def IsSchemeKernel {G H : GroupScheme k} (f : G ⟶ H) (N : ClosedSubgroup G) : Prop :=
  IsPullback N.inclusion.hom.hom (toUnit _) f.hom.hom η[H.X]

/-- The factorization agrees with the canonical scheme-theoretic image on underlying schemes. -/
def IsCanonicalImage {G H I : GroupScheme k} (f : G ⟶ H) (p : G ⟶ I) (i : I ⟶ H) : Prop :=
  ∃ e : I.X.left ≅ f.hom.hom.left.image,
    e.hom ≫ f.hom.hom.left.imageι = i.hom.hom.left ∧
    p.hom.hom.left ≫ e.hom = f.hom.hom.left.toImage

/-- The image is an affine algebraic group. Its coordinate algebra is the range of pullback,
with its inclusion into the source coordinates given by pullback along the projection. -/
def SchemeImageFactorization : Prop :=
  ∀ {k : Type u} [Field k] (G H : AffineAlgebraicGroup k) (f : G.val ⟶ H.val),
    ∃ (I : AffineAlgebraicGroup k) (p : G.val ⟶ I.val) (i : I.val ⟶ H.val),
      IsImageFactorization f p i ∧ IsCanonicalImage f p i ∧
      ∃ e : coordinates I.val.X ≃ₐ[k] (coordinateMap f.hom.hom).range,
        ∀ a, (e a : coordinates G.val.X) = coordinateMap p.hom.hom a

/-- Faithfully flat and closed-immersion factorizations have a unique comparison isomorphism
of group schemes compatible with both maps. -/
def SchemeImageUniqueness : Prop :=
  ∀ {k : Type u} [Field k] (G H : AffineAlgebraicGroup k) (f : G.val ⟶ H.val)
    {I J : GroupScheme k} (p : G.val ⟶ I) (i : I ⟶ H.val)
    (q : G.val ⟶ J) (j : J ⟶ H.val),
    p ≫ i = f → q ≫ j = f →
    Flat p.hom.hom.left → Surjective p.hom.hom.left → IsClosedImmersion i.hom.hom.left →
    Flat q.hom.hom.left → Surjective q.hom.hom.left → IsClosedImmersion j.hom.hom.left →
    ∃! e : I ≅ J, p ≫ e.hom = q ∧ e.hom ≫ j = i

/-- The projection to the scheme-theoretic image represents the shared fppf
sheafification of right cosets by the scheme-theoretic kernel. -/
def SchemeImageQuotient : Prop :=
  ∀ {k : Type u} [Field k] (G H : AffineAlgebraicGroup k) (f : G.val ⟶ H.val),
    ∃ (I : AffineAlgebraicGroup k) (p : G.val ⟶ I.val) (i : I.val ⟶ H.val)
      (N : ClosedSubgroup G.val),
      IsImageFactorization f p i ∧ IsCanonicalImage f p i ∧ IsSchemeKernel f N ∧
      ∃ e : rightQuotientSheaf N ≅ schemeFppfSheaf I.val.X,
        rightQuotientProjection N ≫ e.hom = (fppfOver k).uliftYoneda.map p.hom.hom

end

end LinearAlgebraicGroups.Specs
