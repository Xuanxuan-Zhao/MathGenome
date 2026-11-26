import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.BruhatOrbitParametrization
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SimpleRoots
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Reductive.BorelProper

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj Pointwise

universe u

namespace LinearAlgebraicGroups.Specs.SimpleParabolicProduct

open AbstractPairing (Datum Root)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open BruhatOrbitParametrization (IsRepresentative)
open CharacterDescent (Cocharacter)
open CharacterPairing (pairing)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open OrderedRootProducts (Enumerates Parametrizes RootSubgroupFamily)
open QuotientEmbedding (Presentation)
open RankOneFlag (Centralizer IsGeometricallyMaximal projectiveLine)
open SchemeDerivedGroup (IsSubgroupOf)
open LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The integral cocharacter is on the open face of the Borel chamber
corresponding to the simple root. -/
def IsWallCocharacter (T B : ClosedSubgroup G.val) (α : Root T)
    (c : Cocharacter T.group) : Prop :=
  (∀ β : Root T, pairing T.group β.val c = 0 ↔ β = α ∨ β.val = α.val⁻¹) ∧
  positiveRoots T c = subgroupRoots T B \ {α}

/-- The point image of the double orbit of a rational representative. -/
def doubleCoset (B : ClosedSubgroup G.val) (Y : SchemeOver k)
    (n : 𝟙_ (SchemeOver k) ⟶ G.val.X) : Set (Y ⟶ G.val.X) :=
  (SubgroupSections B Y : Set (Y ⟶ G.val.X)) * {toUnit Y ≫ n} * (SubgroupSections B Y : Set (Y ⟶ G.val.X))

/-- The standard parabolic for one simple reflection, its rank-one flag
quotient, and the rank-one double-orbit product on geometric points. -/
def Statement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    IsKBorel B → IsSubgroupOf T B →
    ∃ h : IsCommMonObj T.group.X, letI := h
      ∃ (D : Datum T) (I : Identification D) (U : RootSubgroupFamily T)
        (c : Cocharacter T.group) (b : D.rootDatum.Base),
        IsRegular T c ∧ positiveRoots T c = subgroupRoots T B ∧
        SimpleRoots.IsBaseFor D.rootDatum (SimpleRoots.evaluate D c) b ∧
        (∀ w, ∃ n, IsRepresentative I w n) ∧
        ∀ α ∈ b.support,
          let s := RootPairing.weylGroup.ofIdx D.rootDatum α
          ∃ (wall : Cocharacter T.group) (P : LimitDecomposition (wall ≫ T.inclusion))
            (H : Centralizer T α.val),
            IsWallCocharacter T B α wall ∧ BorelProper.IsParabolic G P.parabolic ∧
            (∀ l, Enumerates l (subgroupRoots T B \ {α}) →
              Parametrizes U l P.contracting.inclusion.hom.hom) ∧
            ∃ (e : P.centralizer.group ≅ H.subgroup.group)
              (j : B.group ⟶ P.parabolic.group)
              (A : ClosedSubgroup H.subgroup.group) (r : B.group ⟶ A.group)
              (hj : IsClosedImmersion j.hom.hom.left),
              e.hom ≫ H.subgroup.inclusion = P.centralizer.inclusion ∧
              j ≫ P.parabolic.inclusion = B.inclusion ∧ IsKBorel A ∧
              IsPullback j.hom.hom r.hom.hom
                (P.limit ≫ e.hom).hom.hom A.inclusion.hom.hom ∧
              Nonempty (Presentation (⟨B.group, j, hj⟩ : ClosedSubgroup P.parabolic.group)) ∧
              Nonempty (Presentation A) ∧
              (∀ (Q : Presentation (⟨B.group, j, hj⟩ : ClosedSubgroup P.parabolic.group))
                  (QH : Presentation A),
                ∃ (f : Q.scheme ≅ QH.scheme),
                  Q.projection ≫ f.hom = (P.limit ≫ e.hom).hom.hom ≫ QH.projection ∧
                  Nonempty (QH.scheme ≅ projectiveLine k)) ∧
              ∀ n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ I.normalizer.group.X),
                (∀ w, IsRepresentative I w (n w)) →
                ∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
                  let Y := Over.mk (fieldSpecMap k K)
                  let g := fun w ↦ n w ≫ I.normalizer.inclusion.hom.hom
                  let C := fun w ↦ doubleCoset B Y (g w)
                  (SubgroupSections P.parabolic Y : Set (Y ⟶ G.val.X)) =
                    (SubgroupSections B Y : Set (Y ⟶ G.val.X)) ∪ C s ∧
                  Disjoint (SubgroupSections B Y : Set (Y ⟶ G.val.X)) (C s) ∧
                  C s = (SubgroupSections (U α).val Y : Set (Y ⟶ G.val.X)) * {toUnit Y ≫ g s} *
                    (SubgroupSections B Y : Set (Y ⟶ G.val.X)) ∧
                  ∀ v, C v * (SubgroupSections P.parabolic Y : Set (Y ⟶ G.val.X)) =
                      C v ∪ C (v * s) ∧
                    (D.rootDatum.weylGroupToPerm v α ∈ subgroupRoots T B →
                      C v * C s = C (v * s))

end

end LinearAlgebraicGroups.Specs.SimpleParabolicProduct
