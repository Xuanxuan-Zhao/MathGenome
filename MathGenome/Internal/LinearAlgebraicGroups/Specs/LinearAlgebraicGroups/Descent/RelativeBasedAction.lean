import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import Mathlib.CategoryTheory.Endomorphism

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.RelativeBasedAction

open Pinning (SplitBorelPair AttachedDatum transportCharacter)
open CharacterDescent (Character Cocharacter)

noncomputable section

variable {k : Type u} [Field k]

/-- The group of sections over each object of the big slice over the test scheme. -/
abbrev sections (G : GroupScheme k) (S : SchemeOver k) : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.forget S).op ⋙ yonedaGrp.obj G

abbrev RelativeAut (G : GroupScheme k) (S : SchemeOver k) := Aut (sections G S)

abbrev scalarAut {G : GroupScheme k} (e : G ≅ G) (S : SchemeOver k) : RelativeAut G S :=
  Functor.mapAut G (yonedaGrp ⋙ (Functor.whiskeringLeft _ _ _).obj (Over.forget S).op)
    (Aut.of e)

abbrev sectionMap {G H : GroupScheme k} (i : G ⟶ H) (S : SchemeOver k) :
    sections G S ⟶ sections H S :=
  Functor.whiskerLeft (Over.forget S).op (yonedaGrp.map i)

/-- An automorphism preserving the split Borel pair induces a based automorphism
with the two indicated actions on the entire lattices. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k) (D : AttachedDatum P)
    (R : TestAlgebra k), let S := (testSpec k).obj (op R)
    Nonempty S.left →
    ∀ (f : RelativeAut P.G.val S) (b : RelativeAut P.B.group S)
      (e : P.T.group ≅ P.T.group),
      sectionMap P.T.inclusion S ≫ f.asIso.hom =
        (scalarAut e S).asIso.hom ≫ sectionMap P.T.inclusion S →
      sectionMap P.B.inclusion S ≫ f.asIso.hom =
        b.asIso.hom ≫ sectionMap P.B.inclusion S →
      ∃ d : Aut D.toBased,
        (∀ χ : Character P.T.group, d.asIso.hom.val.weightEquiv (Additive.ofMul χ) =
          Additive.ofMul (transportCharacter e χ)) ∧
        (∀ c : Cocharacter P.T.group, d.asIso.hom.val.coweightEquiv (Additive.ofMul c) =
          Additive.ofMul (c ≫ e.inv))

end

end LinearAlgebraicGroups.Specs.RelativeBasedAction
