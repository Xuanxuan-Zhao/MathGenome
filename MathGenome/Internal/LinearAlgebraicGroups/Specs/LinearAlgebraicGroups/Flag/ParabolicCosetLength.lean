import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.StandardParabolicLevi
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.SimpleParabolicProduct

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj Pointwise

universe u v w z

namespace LinearAlgebraicGroups.Specs.ParabolicCosetLength

open AbstractPairing (Datum Root)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open BruhatOrbitParametrization (Cell IsRepresentative)
open CharacterDescent (Cocharacter)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open OrderedRootProducts (RootSubgroupFamily)
open QuotientEmbedding (Presentation)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open SimpleParabolicProduct (doubleCoset)
open SimpleRoots (IsBaseFor evaluate wordLength)
open StandardParabolicLevi (StandardParabolic parabolicWeylGroup)

noncomputable section

/-- Membership in the coset `w H` and minimum length among its elements. -/
def IsShortestInCoset {W : Type*} [Group W] (length : W → ℕ) (H : Subgroup W)
    (w m : W) : Prop :=
  w⁻¹ * m ∈ H ∧ ∀ u : H, length m ≤ length (w * u.val)

/-- The shortest representative in each standard parabolic Weyl coset is
unique, sends the positive roots of the subsystem to positive roots, and
has additive length under right multiplication by the parabolic Weyl group. -/
def LengthStatement : Prop :=
  ∀ {Idx : Type v} {X : Type w} {Y : Type z} [Finite Idx]
    [AddCommGroup X] [AddCommGroup Y] [Module.Free ℤ X] [Module.Free ℤ Y]
    [Module.Finite ℤ X] [Module.Finite ℤ Y]
    (P : RootDatum Idx X Y) [P.IsReduced] [P.flip.IsReduced] (b : P.Base)
    (I : Set Idx), I ⊆ b.support →
    let W_I := Subgroup.closure (RootPairing.weylGroup.ofIdx P '' I)
    let positiveSubsystem := {α : Idx | b.IsPos α ∧ P.root α ∈ Submodule.span ℤ (P.root '' I)}
    ∀ w : P.weylGroup,
      (∃! m, IsShortestInCoset (wordLength P b) W_I w m) ∧
      (∀ m, IsShortestInCoset (wordLength P b) W_I w m ↔
        w⁻¹ * m ∈ W_I ∧ Set.MapsTo (P.weylGroupToPerm m) positiveSubsystem {α | b.IsPos α}) ∧
      (∀ m, IsShortestInCoset (wordLength P b) W_I w m →
        ∀ u : W_I, wordLength P b (m * u.val) = wordLength P b m + wordLength P b u.val)

/-- Saturating a split Bruhat double orbit by the standard parabolic on the
right gives precisely the cells indexed by its Weyl coset. The multiplication
image is expressed on geometric points and on the underlying scheme spaces. -/
def SaturationStatement : Prop :=
  ∀ {k : Type u} [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    IsKBorel B → IsSubgroupOf T B →
    ∃ h : IsCommMonObj T.group.X, letI := h
      ∃ (D : Datum T) (W : Identification D) (U : RootSubgroupFamily T)
        (c : Cocharacter T.group) (b : D.rootDatum.Base),
        IsRegular T c ∧ positiveRoots T c = subgroupRoots T B ∧
        IsBaseFor D.rootDatum (evaluate D c) b ∧
        ∀ (I : Set (Root T)), I ⊆ b.support →
          ∃ P : StandardParabolic B D b U I,
            (∀ w, ∃ n, IsRepresentative W w n) ∧ Nonempty (Presentation B) ∧
            ∀ (Q : Presentation B)
              (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X)),
              (∀ w, IsRepresentative W w (n w)) →
              let g := fun w ↦ n w ≫ W.normalizer.inclusion.hom.hom
              ∃ (a : ModObj G.val.X Q.scheme)
                (A : D.rootDatum.weylGroup → ClosedSubgroup G.val)
                (C : ∀ w, Cell (T := T) Q a (g w) (A w)),
                lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
                  μ[G.val.X] ≫ Q.projection ∧
                let H := P.limitGroups.parabolic
                let W_I := parabolicWeylGroup D I
                (∀ (K : Type u) [Field K] [Algebra k K] [IsAlgClosed K],
                  let Y := Over.mk (fieldSpecMap k K)
                  ∀ w, doubleCoset B Y (g w) * (SubgroupSections H Y : Set (Y ⟶ G.val.X)) =
                    ⋃ v : W_I, doubleCoset B Y (g (w * v.val))) ∧
                ∀ w,
                  Set.range (((fst (C w).doubleOrbit H.group.X ≫ (C w).doubleOrbitInclusion) *
                    (snd (C w).doubleOrbit H.group.X ≫ H.inclusion.hom.hom)).left) =
                  ⋃ v : W_I, Set.range (C (w * v.val)).doubleOrbitInclusion.left

/-- The length and saturation assertions for standard parabolic cosets. -/
def Statement : Prop := SaturationStatement.{u} ∧ LengthStatement.{v, w, z}

end

end LinearAlgebraicGroups.Specs.ParabolicCosetLength
