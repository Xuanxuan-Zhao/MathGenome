import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.ParabolicCosetLength
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.ProjectiveFlags
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Flag.SchubertClosures

open AlgebraicGeometry CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.PartialFlags

open AbstractPairing (Datum Root)
open BorelsAndChambers (IsRegular positiveRoots subgroupRoots)
open BruhatOrbitParametrization (Cell IsRepresentative)
open CharacterDescent (Cocharacter)
open DatumAndWeyl (Identification)
open GeometricBorelConjugacy (IsKBorel)
open GeometricRadicals (IsReductive IsSplitTorus)
open OrderedRootProducts (RootSubgroupFamily)
open ParabolicCosetLength (IsShortestInCoset)
open QuotientEmbedding (Presentation)
open RankOneFlag (IsGeometricallyMaximal)
open SchemeDerivedGroup (IsSubgroupOf)
open SchubertClosures (SubwordLE closureIdeal)
open SimpleRoots (IsBaseFor evaluate wordLength)
open StandardParabolicLevi (StandardParabolic parabolicWeylGroup)

noncomputable section

variable {k : Type u} [Field k] {G : AffineAlgebraicGroup k}

/-- The shortest elements of the right cosets of the standard parabolic Weyl subgroup. -/
def IsMinimal {T : ClosedSubgroup G.val} [IsCommMonObj T.group.X]
    (D : Datum T) (b : D.rootDatum.Base) (I : Set (Root T))
    (w : D.rootDatum.weylGroup) : Prop :=
  IsShortestInCoset (wordLength D.rootDatum b) (parabolicWeylGroup D I) w w

/-- The projection carries the full cells onto the partial orbits. It identifies
a full cell scheme with the partial orbit scheme at every shortest representative. -/
def SplitCells : Prop :=
  ∀ (k : Type u) [Field k] (G : AffineAlgebraicGroup k), IsReductive G →
    ∀ (T B : ClosedSubgroup G.val), IsSplitTorus T.group → IsGeometricallyMaximal T →
    IsKBorel B → IsSubgroupOf T B →
    ∃ h : IsCommMonObj T.group.X, letI := h
      ∃ (D : Datum T) (W : Identification D) (U : RootSubgroupFamily T)
        (c : Cocharacter T.group) (b : D.rootDatum.Base),
        IsRegular T c ∧ positiveRoots T c = subgroupRoots T B ∧
        IsBaseFor D.rootDatum (evaluate D c) b ∧
        (∀ w, ∃ n, IsRepresentative W w n) ∧ Nonempty (Presentation B) ∧
        ∀ (I : Set (Root T)), I ⊆ b.support →
          ∃ P : StandardParabolic B D b U I,
            Nonempty (Presentation P.limitGroups.parabolic) ∧
            (∀ w, ∃! m, IsShortestInCoset (wordLength D.rootDatum b)
                (parabolicWeylGroup D I) w m) ∧
            ∀ (Q : Presentation B) (R : Presentation P.limitGroups.parabolic)
              (n : D.rootDatum.weylGroup → (𝟙_ (SchemeOver k) ⟶ W.normalizer.group.X)),
              (∀ w, IsRepresentative W w (n w)) →
              let g := fun w ↦ n w ≫ W.normalizer.inclusion.hom.hom
              ∃ (π : Q.scheme ⟶ R.scheme)
                (a : ModObj G.val.X Q.scheme) (a' : ModObj G.val.X R.scheme)
                (A : D.rootDatum.weylGroup → ClosedSubgroup G.val)
                (C : ∀ w, Cell (T := T) Q a (g w) (A w)),
                Q.projection ≫ π = R.projection ∧ IsProper π.left ∧
                lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ Q.projection) ≫ a.smul =
                  μ[G.val.X] ≫ Q.projection ∧
                lift (fst G.val.X G.val.X) (snd G.val.X G.val.X ≫ R.projection) ≫ a'.smul =
                  μ[G.val.X] ≫ R.projection ∧
                let j := fun w ↦ (C w).orbitInclusion ≫ π
                let F := fun w ↦ Set.range (j w).left
                (∀ w, F w = Set.range
                  (lift B.inclusion.hom.hom
                    (toUnit B.group.X ≫ g w ≫ R.projection) ≫ a'.smul).left) ∧
                (∀ w v, F w = F v ↔ w⁻¹ * v ∈ parabolicWeylGroup D I) ∧
                (∀ w v, w⁻¹ * v ∉ parabolicWeylGroup D I → Disjoint (F w) (F v)) ∧
                (⋃ w, F w) = Set.univ ∧
                ∀ w, IsMinimal D b I w →
                  IsImmersion (j w).left ∧
                  Nonempty ((C w).orbit ≅ BruhatCells.affineSpace k (wordLength D.rootDatum b w)) ∧
                  RepresentsSubgroup (C w).stabilizer (fun Y t ↦
                    lift (t ≫ B.inclusion.hom.hom) (toUnit Y ≫ g w ≫ R.projection) ≫
                      a'.smul = toUnit Y ≫ g w ≫ R.projection) ∧
                  AlgebraicGeometry.IsReduced (closureIdeal (j w).left).subscheme ∧
                  Set.range (closureIdeal (j w).left).subschemeι =
                    ⋃ (v : {v // IsMinimal D b I v}) (_ : SubwordLE D.rootDatum b v.val w), F v.val

/-- Smooth projective parabolic quotients and the split partial flag stratification. -/
def Statement : Prop := ProjectiveFlags.SmoothProjectiveQuotient.{u} ∧ SplitCells.{u}

end

end LinearAlgebraicGroups.Specs.PartialFlags
