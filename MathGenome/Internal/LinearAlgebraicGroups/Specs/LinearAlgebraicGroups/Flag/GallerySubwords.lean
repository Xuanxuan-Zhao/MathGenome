import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SimpleRoots

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.GallerySubwords

open AbstractPairing (Datum Root)
open CharacterDescent (Cocharacter)
open CharacterPairing (pairing)
open GeometricRadicals (IsReductive IsSplitTorus)
open RankOneFlag (IsGeometricallyMaximal)
open SimpleRoots (IsBaseFor evaluate hyperplane wordLength wordProduct)

section RootPairing

variable {Idx X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootPairing Idx ℤ X Y) (b : P.Base)

/-- A word in the simple reflections is reduced when it has minimum length
among words with the same Weyl group product. -/
def IsReduced (l : List b.support) : Prop :=
  wordLength P b (wordProduct P b l) = l.length

/-- Exchange in the actual root hyperplanes, and the reduction of subwords
in the same simple reflections. -/
structure HasGallerySubwords : Prop where
  rightExchange (l : List b.support) (s : b.support) (hl : IsReduced P b l)
      (hs : wordLength P b (wordProduct P b (l ++ [s])) <
        wordLength P b (wordProduct P b l)) :
    ∃ (pre post : List b.support) (i : b.support),
      l = pre ++ (i :: post) ∧
      hyperplane P (P.weylGroupToPerm (wordProduct P b pre) i.val) =
        hyperplane P (P.weylGroupToPerm (wordProduct P b l) s.val) ∧
      wordProduct P b (pre ++ post) = wordProduct P b (l ++ [s])
  reducedSubword (l : List b.support) :
    ∃ r : List b.support, r.Sublist l ∧ IsReduced P b r ∧
      wordProduct P b r = wordProduct P b l
  subword_iff (l : List b.support) (v : P.weylGroup) :
    (∃ r : List b.support, r.Sublist l ∧ wordProduct P b r = v) ↔
      ∃ r : List b.support, r.Sublist l ∧ IsReduced P b r ∧ wordProduct P b r = v

end RootPairing

/-- For every regular positive system of a split connected reductive pair,
exchange and subword reduction hold in its base of actual simple roots.
The Weyl group of the datum is identified with the scheme normalizer quotient. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ T : ClosedSubgroup G.val, IsSplitTorus T.group → IsGeometricallyMaximal T →
      ∃ h : IsCommMonObj T.group.X, letI := h
        ∃ (D : Datum T) (_e : DatumAndWeyl.Identification D),
          ∀ cochar : Cocharacter T.group, (∀ i : Root T, pairing T.group i.val cochar ≠ 0) →
            ∃ b : D.rootDatum.Base, IsBaseFor D.rootDatum (evaluate D cochar) b ∧
              HasGallerySubwords D.rootDatum b

end LinearAlgebraicGroups.Specs.GallerySubwords
