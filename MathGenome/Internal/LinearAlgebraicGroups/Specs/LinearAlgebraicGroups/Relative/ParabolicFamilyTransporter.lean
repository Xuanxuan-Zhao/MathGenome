import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.HomogeneousQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.BorelProper

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.ParabolicFamilyTransporter

noncomputable section

variable {k : Type u} [Field k] {G : GroupScheme k} {T U : SchemeOver k}

/-- The constant group over a test scheme. -/
abbrev relativeGroup (G : GroupScheme k) (T : SchemeOver k) : Grp (Over T.left) :=
  (Over.pullback T.hom).mapGrp.obj G

/-- A smooth closed subgroup scheme of the constant group over the test scheme. -/
structure Family (G : GroupScheme k) (T : SchemeOver k) where
  group : Grp (Over T.left)
  inclusion : group ⟶ relativeGroup G T
  closed : IsClosedImmersion inclusion.hom.hom.left
  smooth : Smooth group.X.hom

abbrev Family.overField (Q : Family G T) : SchemeOver k :=
  (Over.map T.hom).obj Q.group.X

abbrev Family.base (Q : Family G T) : Q.overField ⟶ T :=
  Over.homMk Q.group.X.hom

set_option backward.isDefEq.respectTransparency false in
/-- The inclusion viewed as a morphism into the product over the ground field. -/
def Family.ambient (Q : Family G T) : Q.overField ⟶ G.X ⊗ T :=
  lift (Over.homMk
    (Q.inclusion.hom.hom.left ≫ pullback.fst G.X.hom T.hom)
    (by
      have h : Q.inclusion.hom.hom.left ≫ pullback.snd G.X.hom T.hom = Q.group.X.hom :=
        Over.w Q.inclusion.hom.hom
      calc
        _ = Q.inclusion.hom.hom.left ≫ (pullback.fst G.X.hom T.hom ≫ G.X.hom) :=
          Category.assoc _ _ _
        _ = _ := by rw [pullback.condition, ← Category.assoc, h]; rfl)) Q.base

/-- The inclusion of the conjugate of the constant subgroup over a test scheme. -/
def conjugateInclusion (P : ClosedSubgroup G) (g : U ⟶ G.X) :
    P.group.X ⊗ U ⟶ G.X ⊗ U :=
  lift (conjugateFamily P.inclusion g) (snd _ _)

/-- Containment of the conjugate of the constant subgroup in the test family. -/
def ConjugateContained (P : ClosedSubgroup G) (Q : Family G T)
    (a : U ⟶ T) (g : U ⟶ G.X) : Prop :=
  ∃ f : P.group.X ⊗ U ⟶ Q.overField,
    f ≫ Q.ambient = conjugateInclusion P g ≫ (G.X ◁ a)

/-- Equality of the two subgroup schemes after pulling the family back along `a`. -/
def Conjugates (P : ClosedSubgroup G) (Q : Family G T)
    (a : U ⟶ T) (g : U ⟶ G.X) : Prop :=
  ∃ e : P.group.X ⊗ U ≅ pullback Q.ambient (G.X ◁ a),
    e.hom ≫ pullback.snd _ _ = conjugateInclusion P g

/-- The family is geometrically of the type of `P` when it is conjugate to
`P` on every geometric fibre. -/
def SameGeometricType (P : ClosedSubgroup G) (Q : Family G T) : Prop :=
  ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
    (a : (testSpec k).obj (op (CommAlgCat.of k K)) ⟶ T),
      ∃ g, Conjugates P Q a g

/-- The universal test property of a transporter inside the constant group. -/
def RepresentsTransporter (P : ClosedSubgroup G) (Q : Family G T) {Z : SchemeOver k}
    (j : Z ⟶ G.X ⊗ T) : Prop :=
  ∀ (U : SchemeOver k) (a : U ⟶ T) (g : U ⟶ G.X),
    Conjugates P Q a g ↔ ∃ y : U ⟶ Z, y ≫ j = lift g a

/-- The scheme of conjugacies of the constant parabolic with a smooth closed
family of its geometric type is a smooth faithfully flat finitely presented
scheme over the base. -/
def ParabolicTransporter : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    BorelProper.IsParabolic G P →
    ∀ (R : TestAlgebra k) (Q : Family G.val ((testSpec k).obj (op R))),
      SameGeometricType P Q →
        ∃ (Z : SchemeOver k) (j : Z ⟶ G.val.X ⊗ (testSpec k).obj (op R)),
          IsClosedImmersion j.left ∧ RepresentsTransporter P Q j ∧
            Smooth (j ≫ snd _ _).left ∧ Flat (j ≫ snd _ _).left ∧
            Surjective (j ≫ snd _ _).left ∧
            LocallyOfFinitePresentation (j ≫ snd _ _).left ∧
            QuasiCompact (j ≫ snd _ _).left ∧ QuasiSeparated (j ≫ snd _ _).left

/-- Equality of families means equality as subgroup schemes of the ambient group. -/
def SameFamily (Q Q' : Family G T) : Prop :=
  ∃ e : Q.overField ≅ Q'.overField, e.hom ≫ Q'.ambient = Q.ambient

/-- A section of the quotient classifies a family if, on every test scheme,
its lifts to the group are exactly the conjugacies to that family. -/
def Classifies {P : ClosedSubgroup G} (D : QuotientEmbedding.Presentation P)
    (Q : Family G T) (x : T ⟶ D.scheme) : Prop :=
  ∀ (U : SchemeOver k) (a : U ⟶ T) (g : U ⟶ G.X),
    g ≫ D.projection = a ≫ x ↔ Conjugates P Q a g

/-- Pulling back a family of the fixed geometric type pulls back its classifying
parameter. The isomorphism identifies the pulled-back closed subgroup in the
constant group over the new base. -/
def ClassifiesBaseChange : Prop :=
  ∀ {k : Type u} [Field k] {G : GroupScheme k} {T U : SchemeOver k}
    {P : ClosedSubgroup G} {D : QuotientEmbedding.Presentation P}
    (Q : Family G T), SameGeometricType P Q →
    ∀ (a : U ⟶ T) {x : T ⟶ D.scheme}, Classifies D Q x →
      ∃ (Q' : Family G U) (e : Q'.overField ≅ pullback Q.ambient (G.X ◁ a)),
        e.hom ≫ pullback.snd _ _ = Q'.ambient ∧
          SameGeometricType P Q' ∧ Classifies D Q' (a ≫ x)

/-- The flag scheme represents smooth closed parabolic families of the fixed
geometric type through conjugation. The test identity gives naturality under
arbitrary base change. The parameter is unique, as is the family as a closed
subgroup of the ambient group. -/
def ParabolicFamilyRepresentability : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k) (P : ClosedSubgroup G.val),
    BorelProper.IsParabolic G P →
    Nonempty (QuotientEmbedding.Presentation P) ∧
    ∀ (D : QuotientEmbedding.Presentation P) (R : TestAlgebra k),
      let T := (testSpec k).obj (op R)
      (∀ (Q : Family G.val T), SameGeometricType P Q →
        ∃! x : T ⟶ D.scheme, Classifies D Q x) ∧
      ∀ x : T ⟶ D.scheme,
        ∃ (Q : Family G.val T), SameGeometricType P Q ∧ Classifies D Q x ∧
          ∀ Q' : Family G.val T, SameGeometricType P Q' → Classifies D Q' x → SameFamily Q Q'

end

end LinearAlgebraicGroups.Specs.ParabolicFamilyTransporter
