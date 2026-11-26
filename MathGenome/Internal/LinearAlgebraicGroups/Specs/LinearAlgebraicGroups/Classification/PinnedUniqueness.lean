import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import Mathlib.CategoryTheory.Comma.Over.Basic

open CategoryTheory

universe u

namespace LinearAlgebraicGroups.Specs.PinnedUniqueness

open AdjointRepresentation (GroupPoints)
open CharacterDescent (Character)
open Pinning (AttachedDatum BasedIso BasedRootDatum PinnedGroup PinnedIso
  SimpleRoot transportCharacter)
open RootGroups (AdditiveLine rootPoint)

noncomputable section

variable {k : Type u} [Field k]

/-- The functor of points of the scalar extension to `R`, on commutative
`R`-algebras. An object of the under category records its structure map. -/
abbrev scalarGroupPoints (R : TestAlgebra k) (G : GroupScheme k) : Under R ⥤ GrpCat.{u} :=
  Under.forget R ⋙ (groupPointsFunctor k).obj G

/-- The pinned simple-root coordinates are fixed over every test algebra
over the scalar base. -/
def FixesPinning {A : AdditiveLine k} (P : PinnedGroup A) {R : TestAlgebra k}
    (f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val) : Prop :=
  ∀ (S : Under R) (α : SimpleRoot P.pair) (a : S.right),
    (f.app S).hom (rootPoint ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion) S.right a) =
      rootPoint ((P.pin α).val.hom ≫ (P.roots α.val).val.inclusion) S.right a

/-- Identity on the torus is tested on its entire scalar-extended functor. -/
def FixesTorus {A : AdditiveLine k} (P : PinnedGroup A) {R : TestAlgebra k}
    (f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val) : Prop :=
  ∀ (S : Under R) (t : GroupPoints P.pair.T.group S.right),
    (f.app S).hom (t ≫ P.pair.T.inclusion.hom.hom) = t ≫ P.pair.T.inclusion.hom.hom

/-- Faithfulness after arbitrary scalar extension, including nonreduced bases. -/
def ScalarRigidity : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A) (R : TestAlgebra k)
    (f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val),
    FixesTorus P f → FixesPinning P f → f = 𝟙 _

/-- Ground-field characters separate all points of a split torus, even
when the test algebra has nilpotents. -/
def CharactersSeparatePoints : Prop :=
  ∀ {k : Type u} [Field k] {T : GroupScheme k}, GeometricRadicals.IsSplitTorus T →
    ∀ (R : TestAlgebra k) (t s : GroupPoints T R),
      (∀ χ : Character T, t ≫ χ.hom.hom = s ≫ χ.hom.hom) → t = s

/-- A scalar-extended endomorphism that preserves the pinning and acts
trivially on the characters of its preserved torus is the identity. -/
def ScalarCharacterRigidity : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} (P : PinnedGroup A) (R : TestAlgebra k)
    (f : scalarGroupPoints R P.pair.G.val ⟶ scalarGroupPoints R P.pair.G.val)
    (g : scalarGroupPoints R P.pair.T.group ⟶ scalarGroupPoints R P.pair.T.group),
    (∀ (S : Under R) (t : GroupPoints P.pair.T.group S.right),
      (f.app S).hom (t ≫ P.pair.T.inclusion.hom.hom) =
        ((g.app S).hom t) ≫ P.pair.T.inclusion.hom.hom) →
    (∀ (S : Under R) (t : GroupPoints P.pair.T.group S.right) (χ : Character P.pair.T.group),
      ((g.app S).hom t) ≫ χ.hom.hom = t ≫ χ.hom.hom) →
    FixesPinning P f → f = 𝟙 _

/-- Over the ground field, equality of the induced lattice maps suffices
for equality of pinned isomorphisms. Inverse pullback is used for variance. -/
def PinnedIsoUniqueness : Prop :=
  ∀ {k : Type u} [Field k] {A : AdditiveLine k} {P Q : PinnedGroup A}
    (f g : PinnedIso P Q),
    (∀ χ : Character P.pair.T.group,
      transportCharacter f.torus χ = transportCharacter g.torus χ) → f = g

/-- The based-datum functor is faithful. Its character map is the
inverse pullback on the actual lattice of the split torus. -/
def BasedDatumFunctorFaithful : Prop :=
  ∀ {k : Type u} [Field k] (A : AdditiveLine k)
    (D : ∀ P : PinnedGroup A, AttachedDatum P.pair)
    (F : PinnedGroup A ⥤ BasedRootDatum.{u})
    (hObj : ∀ P, F.obj P = (D P).toBased),
    (∀ (P Q : PinnedGroup A) (f : P ⟶ Q),
      let e : BasedIso (D P).toBased (D Q).toBased :=
        (hObj P) ▸ (hObj Q) ▸ F.map f
      ∀ χ : Character P.pair.T.group, e.val.weightEquiv (Additive.ofMul χ) =
        Additive.ofMul (transportCharacter f.torus χ)) →
    F.Faithful

end

end LinearAlgebraicGroups.Specs.PinnedUniqueness
