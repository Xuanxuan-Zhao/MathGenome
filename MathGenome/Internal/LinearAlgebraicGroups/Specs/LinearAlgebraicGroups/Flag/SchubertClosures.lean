import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.GallerySubwords
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

open AlgebraicGeometry CategoryTheory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.SchubertClosures

open AbstractPairing (Datum)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open BruhatOrbitParametrization (Cell IsRepresentative)
open CharacterDescent (Cocharacter)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open QuotientEmbedding (Presentation)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open SimpleRoots (IsBaseFor evaluate wordProduct)

section Words

variable {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootPairing Idx ℤ X Y) (b : P.Base)

/-- The products obtained by retaining letters in their original order. -/
def subwordProducts (l : List b.support) : Set P.weylGroup :=
  {v | ∃ r : List b.support, r.Sublist l ∧ wordProduct P b r = v}

/-- The Bruhat order defined by subwords of reduced expressions. -/
def SubwordLE (v w : P.weylGroup) : Prop :=
  ∃ l : List b.support, GallerySubwords.IsReduced P b l ∧ wordProduct P b l = w ∧
    v ∈ subwordProducts P b l

end Words

/-- The ideal of the reduced induced scheme structure on the closure of the image. -/
noncomputable def closureIdeal {X Y : Scheme.{u}} (i : X ⟶ Y) : Y.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure (Set.range i))

/-- The closure formula in the full flag scheme and in the group. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
      IsKBorel B → IsSubgroupOf T B →
      ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ (D : Datum T) (I : Identification D) (c : Cocharacter T.group)
          (b : D.rootDatum.Base),
          IsRegular T c ∧ positiveRoots T c = subgroupRoots T B ∧
          IsBaseFor D.rootDatum (evaluate D c) b ∧
          (∀ w, ∃ n, IsRepresentative I w n) ∧ Nonempty (Presentation B) ∧
          ∀ Q : Presentation B,
            ∃ a : ModObj G.val.X Q.scheme,
              lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
                μ[G.val.X] ≫ Q.projection ∧
              ∀ n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X),
                (∀ w, IsRepresentative I w (n w)) →
                let g := fun w ↦ n w ≫ I.normalizer.inclusion.hom.hom
                ∃ (A : D.rootDatum.weylGroup → ClosedSubgroup G.val)
                  (C : ∀ w, Cell (T := T) Q a (g w) (A w)),
                  let F := fun w ↦ Set.range (C w).orbitInclusion.left
                  let E := fun w ↦ Set.range (C w).doubleOrbitInclusion.left
                  (∀ w, AlgebraicGeometry.IsReduced (closureIdeal (C w).orbitInclusion.left).subscheme ∧
                    AlgebraicGeometry.IsReduced (closureIdeal (C w).doubleOrbitInclusion.left).subscheme) ∧
                  (∀ v w, SubwordLE D.rootDatum b v w ↔ F v ⊆ closure (F w)) ∧
                  ∀ (l : List b.support), GallerySubwords.IsReduced D.rootDatum b l →
                    let w := wordProduct D.rootDatum b l
                    (∀ v, (v ∈ subwordProducts D.rootDatum b l ↔
                        SubwordLE D.rootDatum b v w) ∧
                      (v ∈ subwordProducts D.rootDatum b l ↔
                        ∃ r : List b.support, r.Sublist l ∧ GallerySubwords.IsReduced D.rootDatum b r ∧
                          wordProduct D.rootDatum b r = v)) ∧
                    Set.range (closureIdeal (C w).orbitInclusion.left).subschemeι =
                      (⋃ v ∈ subwordProducts D.rootDatum b l, F v) ∧
                    Set.range (closureIdeal (C w).doubleOrbitInclusion.left).subschemeι =
                      (⋃ v ∈ subwordProducts D.rootDatum b l, E v)

end LinearAlgebraicGroups.Specs.SchubertClosures
