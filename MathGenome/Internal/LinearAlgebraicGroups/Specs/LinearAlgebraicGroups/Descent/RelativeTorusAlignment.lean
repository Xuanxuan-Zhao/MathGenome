import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.Pinning

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace LinearAlgebraicGroups.Specs.RelativeTorusAlignment

open Pinning (SplitBorelPair)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]

/-- The group of sections of the constant group on each test in the slice. -/
abbrev relativePoints (G : GroupScheme k) (S : SchemeOver k) :
    (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  (Over.forget S).op ⋙ yonedaGrp.obj G

open scoped CategoryTheory.MonObj

/-- Evaluation of a relative point transformation on a slice object. -/
abbrev evaluate {G H : GroupScheme k} {S : SchemeOver k}
    (f : relativePoints G S ⟶ relativePoints H S) (U : Over S)
    (x : U.left ⟶ G.X) : U.left ⟶ H.X :=
  (f.app (op U)).hom x

theorem evaluate_map_comp {G H : GroupScheme k} {S V W : SchemeOver k}
    (f : relativePoints G S ⟶ relativePoints H S) (a : W ⟶ V) (b : V ⟶ S)
    (U : Over W) (x : U.left ⟶ G.X) :
    evaluate f ((Over.map (a ≫ b)).obj U) x =
      evaluate f ((Over.map b).obj ((Over.map a).obj U)) x := by
  let q := (Over.mapComp a b).hom.app U
  have e := ConcreteCategory.congr_hom (f.naturality q.op) x
  change q.left ≫ evaluate f ((Over.map b).obj ((Over.map a).obj U)) x =
    evaluate f ((Over.map (a ≫ b)).obj U) (q.left ≫ x) at e
  have hq : q.left = 𝟙 U.left := rfl
  rw [hq] at e
  have hx : 𝟙 U.left ≫ x = x := Category.id_comp x
  have hy : 𝟙 U.left ≫ evaluate f ((Over.map b).obj ((Over.map a).obj U)) x = _ :=
    Category.id_comp _
  rw [hx, hy] at e
  exact e.symm

/-- Witnesses that conjugation of the restricted Borel automorphism preserves the
specified maximal torus on every test scheme over the covering domain. -/
def Aligns {H B : GroupScheme k} (i : H ⟶ B)
    {S V : SchemeOver k} (f : relativePoints B S ≅ relativePoints B S) (b : V ⟶ S) : Prop :=
  ∃ (g : V ⟶ B.X) (t : relativePoints H V ≅ relativePoints H V),
    ∀ (U : Over V) (x : U.left ⟶ H.X),
      let y : U.left ⟶ B.X := evaluate f.hom ((Over.map b).obj U) (x ≫ i.hom.hom)
      (U.hom ≫ g) * y * (U.hom ≫ g)⁻¹ =
        evaluate t.hom U x ≫ i.hom.hom

/-- The arrows over which the Borel automorphism can be aligned with the torus. -/
def alignmentSieve {H B : GroupScheme k} (i : H ⟶ B) {S : SchemeOver k}
    (f : relativePoints B S ≅ relativePoints B S) : Sieve S where
  arrows V b := Aligns i f b
  downward_closed := by
    rintro V W b ⟨g, t, h⟩ a
    refine ⟨a ≫ g, Functor.isoWhiskerLeft (Over.map a).op t, fun U x ↦ ?_⟩
    dsimp only
    rw [evaluate_map_comp]
    change (U.hom ≫ a ≫ g) *
      (show U.left ⟶ B.X from evaluate f.hom ((Over.map b).obj ((Over.map a).obj U)) (x ≫ i.hom.hom)) *
      (U.hom ≫ a ≫ g)⁻¹ = evaluate t.hom ((Over.map a).obj U) x ≫ i.hom.hom
    simpa only [Over.map_obj_hom, Category.assoc] using h ((Over.map a).obj U) x

/-- For a split Borel pair, the specified torus can be aligned by conjugation by
Borel sections fppf locally on an arbitrary test scheme. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (P : SplitBorelPair k)
    (i : P.T.group ⟶ P.B.group), i ≫ P.B.inclusion = P.T.inclusion →
    ∀ (S : SchemeOver k) (f : relativePoints P.B.group S ≅ relativePoints P.B.group S),
      alignmentSieve i f ∈ Fppf.schemeTopology k S

end

end LinearAlgebraicGroups.Specs.RelativeTorusAlignment
