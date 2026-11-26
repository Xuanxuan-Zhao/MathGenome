import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalInnerIndexParabolic

open ExceptionalAffineRootSystems (ApartmentRoots)
open ExceptionalIwahoriImageComparison (MarkedCentralCover markedGroundPoint)
open ExceptionalInnerStandardTorusDescent
  (StandardTorusAndParabolic markedCharacter markedCocharacterMap)
open ExceptionalMarkedRootDescent (MarkedFibre)
open GeometricRadicals (IsMaximalTorus)
open IntegralSemisimpleModel (Model)
open Pinning (BasedRootDatum)
open Relative.MaximalSplitTori (IsMaximalSplitTorus IsMinimalParabolic)
open SchemeDerivedGroup (IsSubgroupOf)

/-- A chamber chosen by a marked normalizer point identifies the black nodes
of the relative index with the simple characters trivial on the split torus. -/
def AdaptedIndexParabolic : Prop :=
  ∀ {F K : Type u} [Field F] [Field K] [Algebra F K]
    {D E : BasedRootDatum.{u}} {M : Model D} {M' : Model E}
    (c : MarkedCentralCover M M') (C : MarkedFibre M K)
    {H : AffineAlgebraicGroup F}
    (f : C.realization.pinned.pair.G.val ≅ (groupBaseChange F K).obj H.val)
    (N : Subgroup (ExceptionalAffineBruhat.FieldPoints M K))
    (L : (ℚ ⊗[ℤ] E.Y) ≃ₗ[ℚ] (ℚ ⊗[ℤ] E.Y)),
    StandardTorusAndParabolic c C f N L →
    ∀ (r : ℕ),
      (∀ (R : ClosedSubgroup H.val) (s : ℕ),
        Nonempty (R.group ≅ (StandardGroups.multiplicativePowerGroup F (ULift.{u} (Fin s))).val) →
          s ≤ r) →
      let fixed := LinearMap.ker (L.toLinearMap - LinearMap.id)
      Module.finrank ℚ fixed = r →
      ∀ {n : ℕ} (b : Fin n ≃ D.base.support) (I : Set (Fin n)),
        let P := C.realization.pinned.pair
        let A := ApartmentRoots.split D.datum ℚ
        ∀ (g : 𝟙_ (SchemeOver K) ⟶ P.G.val.X), markedGroundPoint C g ∈ N →
          (∀ (Q : GroupScheme K) [IsCommMonObj Q.X] (s : Q ⟶ P.T.group),
            LinearMap.range
              ((c.pushCocharacter.baseChange ℚ).comp ((markedCocharacterMap C s).baseChange ℚ)) =
                fixed →
            ∀ a : P.T.group ≅ P.T.group,
              (a.hom ≫ P.T.inclusion).hom.hom =
                (toUnit P.T.group.X ≫ g) * P.T.inclusion.hom.hom *
                  (toUnit P.T.group.X ≫ g)⁻¹ →
              let W := LinearMap.range ((markedCocharacterMap C (s ≫ a.hom)).baseChange ℚ)
              (∀ i ∈ I, ∀ y ∈ W, A.root (b i) y = 0) ∧
                ∃ y ∈ W, ∀ i ∉ I, 0 < A.root (b i) y) →
          ∃ (U S : ClosedSubgroup H.val) (uK : (groupBaseChange F K).obj U.group ≅ P.T.group),
            IsMaximalTorus U ∧ IsMaximalSplitTorus S ∧
            Nonempty (S.group ≅ (StandardGroups.multiplicativePowerGroup F (ULift.{u} (Fin r))).val) ∧
            IsSubgroupOf S U ∧
            uK.hom ≫ P.T.inclusion ≫ f.hom = (groupBaseChange F K).map U.inclusion ∧
            ∃ (J : ClosedSubgroup H.val)
              (sK : (groupBaseChange F K).obj S.group ⟶ P.T.group)
              (jK : P.B.group ⟶ (groupBaseChange F K).obj J.group),
              IsMinimalParabolic H J ∧ IsSubgroupOf S J ∧
              let gs : ((groupBaseChange F K).obj S.group).X ⟶ P.G.val.X := toUnit _ ≫ g
              let gb : P.B.group.X ⟶ P.G.val.X := toUnit _ ≫ g
              (sK ≫ P.T.inclusion).hom.hom =
                gs * (((groupBaseChange F K).map S.inclusion) ≫ f.inv).hom.hom * gs⁻¹ ∧
              (jK ≫ (groupBaseChange F K).map J.inclusion ≫ f.inv).hom.hom =
                gb⁻¹ * P.B.inclusion.hom.hom * gb ∧
              ∀ i, i ∈ I ↔ (sK ≫ markedCharacter C (b i)).hom.hom = 1

end LinearAlgebraicGroups.Specs.ExceptionalInnerIndexParabolic
