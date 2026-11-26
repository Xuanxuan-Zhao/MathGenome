import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.FppfTorsors

open AlgebraicGeometry CategoryTheory Opposite
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.RelativeBorelAlignment

noncomputable section

variable {k : Type u} [Field k]

/-- The points of the scalar extension, evaluated on the whole slice over the base. -/
abbrev relativePoints (G : GroupScheme k) (S : SchemeOver k) : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.forget S).op ⋙ yonedaGrp.obj G

/-- Restriction of a relative isomorphism along a change of base. -/
abbrev restrictIso {G H : GroupScheme k} {S T : SchemeOver k} (a : T ⟶ S)
    (e : relativePoints G S ≅ relativePoints H S) :
    relativePoints G T ≅ relativePoints H T :=
  Functor.isoWhiskerLeft (Over.map a).op e

/-- The inclusion of the relative Borel point functor into the relative ambient group. -/
abbrev borelInclusion (P : Pinning.SplitBorelPair k) (S : SchemeOver k) :
    relativePoints P.B.group S ⟶ relativePoints P.G.val S :=
  Functor.whiskerLeft (Over.forget S).op (yonedaGrp.map P.B.inclusion)

/-- On each test scheme, conjugate by the pullback of the given section. -/
def conjugationHom {G : GroupScheme k} {S : SchemeOver k} (g : S ⟶ G.X) :
    relativePoints G S ⟶ relativePoints G S where
  app U := GrpCat.ofHom ((MulAut.conj (U.unop.hom ≫ g)).toMonoidHom)
  naturality := by
    intro U V a
    apply GrpCat.ext
    intro x
    change U.unop.left ⟶ G.X at x
    change (V.unop.hom ≫ g) * (a.unop.left ≫ x) * (V.unop.hom ≫ g)⁻¹ =
      a.unop.left ≫ ((U.unop.hom ≫ g) * x * (U.unop.hom ≫ g)⁻¹)
    simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, Over.w]

/-- Over an fppf covering sieve, the restricted automorphism followed by
conjugation preserves the scalar-extended Borel, with its actual inclusion. -/
def LocalBorelAlignment : Prop :=
  ∀ {k : Type u} [Field k] (P : Pinning.SplitBorelPair k) (S : SchemeOver k)
    (e : relativePoints P.G.val S ≅ relativePoints P.G.val S),
    ∃ C : Sieve S, C ∈ Fppf.schemeTopology k S ∧
      ∀ ⦃U : SchemeOver k⦄ (a : U ⟶ S), C a →
        ∃ (g : U ⟶ P.G.val.X) (b : relativePoints P.B.group U ≅ relativePoints P.B.group U),
          borelInclusion P U ≫ (restrictIso a e).hom ≫ conjugationHom g =
            b.hom ≫ borelInclusion P U

end

end LinearAlgebraicGroups.Specs.RelativeBorelAlignment
