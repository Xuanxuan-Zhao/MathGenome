import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAffineBruhat
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace LinearAlgebraicGroups.Specs.ExceptionalAdaptedPinnedOuterComparison

open AdjointCocharacters (coordinateHopf coordinateHopfIso)
open AdjointRepresentation (GroupPoints)
open DiagonalizableGroups (groupAlgebra IntegerCharacters)
open ExceptionalAffineBruhat (RamifiedReference)
open ExceptionalInnerStandardTorusDescent (IsUnitComparison)
open ExceptionalMarkedRootDescent (MarkedFibre markedFibrePoint)
open ExceptionalValuedTorusNormalizer (markedDiagramEquiv simplePermutationHom)
open GeometricRadicals (IsSplitTorus)
open IntegralSemisimpleModel (Model)
open Pinning (BasedRootDatum)
open QuasiSplitPinnedPairModel (IsTransportedBasedAction)
open Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.Descent.Forms (IsScalarExtensionComparison spectrumIso)

noncomputable section

variable {F K L : Type u} [Field F] [Field K] [Field L]
variable {D : BasedRootDatum.{u}} {M : Model D}

/-- Compare the two marked fibres by their evaluations in the same integral model. -/
def RespectsIntegralMarking [Algebra F L]
    (C₀ : MarkedFibre M F) (C : MarkedFibre M L)
    (j : C.realization.pinned.pair.G.val ≅
      (groupBaseChange F L).obj C₀.realization.pinned.pair.G.val) : Prop :=
  ∀ (A : TestAlgebra L) (p : GroupPoints C.realization.pinned.pair.G.val A),
    markedFibrePoint C₀ ((restrictTestAlgebra F L).obj A)
      (baseChangePoint F L C₀.realization.pinned.pair.G.val.X A (p ≫ j.hom.hom.hom)) =
    markedFibrePoint C A p

/-- The tower isomorphism preserves the projection to each original scheme. -/
def IsTowerComparison [Algebra F K] [Algebra K L] [Algebra F L]
    (a : groupBaseChange F K ⋙ groupBaseChange K L ≅ groupBaseChange F L) : Prop :=
  ∀ X : GroupScheme F,
    (a.app X).hom.hom.hom.left ≫ pullback.fst X.X.hom (fieldSpecMap F L) =
      pullback.fst ((groupBaseChange F K).obj X).X.hom (fieldSpecMap K L) ≫
        pullback.fst X.X.hom (fieldSpecMap F K)

/-- The comparison over the finite field extension induced by a specified
isomorphism of extended coordinate Hopf algebras. -/
def descentComparison [Algebra F K] (X Y : AffineAlgebraicGroup F)
    (t : ∀ A : HopfAlgebraCategory F,
      specGroup (extendedHopf K A) ≅ (groupBaseChange F K).obj (specGroup A))
    (i : extendedHopf K (coordinateHopf X) ≅ extendedHopf K (coordinateHopf Y)) :
    (groupBaseChange F K).obj X.val ≅ (groupBaseChange F K).obj Y.val :=
  ((groupBaseChange F K).mapIso (coordinateHopfIso X)).symm ≪≫
    (t (coordinateHopf X)).symm ≪≫ spectrumIso i ≪≫ t (coordinateHopf Y) ≪≫
    (groupBaseChange F K).mapIso (coordinateHopfIso Y)

/-- The actual pinned descent compares the marked fibres and identifies
simple characters in each diagram orbit after restriction to the given
split subtorus of the descended torus. -/
def Statement : Prop :=
  ∀ (F K : Type u) [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K]
    {D : BasedRootDatum.{u}} {M : Model D} (R : RamifiedReference F K M)
    (S₀ : ClosedSubgroup R.descent.group.val),
    IsSplitTorus S₀.group →
    ∀ s : S₀.group ⟶ R.descent.torus.group,
    s ≫ R.descent.torus.inclusion = S₀.inclusion →
    let L := SeparableClosure F
    let Q := R.fibre.realization.pinned.pair
    ∃ e : K →ₐ[F] L,
      letI : Algebra K L := e.toRingHom.toAlgebra
      letI : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
      let B := groupBaseChange F K
      let E := groupBaseChange K L
      let U := groupBaseChange F L
      ∃ C : MarkedFibre M L,
        let P := C.realization.pinned.pair
        ∃ (a : B ⋙ E ≅ U)
          (t : ∀ A : HopfAlgebraCategory F, specGroup (extendedHopf K A) ≅ B.obj (specGroup A))
          (v : specGroup (groupAlgebra L IntegerCharacters) ≅
            U.obj (specGroup (groupAlgebra F IntegerCharacters)))
          (j : P.G.val ≅ U.obj Q.G.val)
          (jT : P.T.group ≅ U.obj Q.T.group)
          (jB : P.B.group ≅ U.obj Q.B.group),
          let dG := descentComparison Q.G R.descent.group t R.descent.data.groupIso
          let dT := descentComparison (closedSubgroupAlgebraicGroup Q.T)
            (closedSubgroupAlgebraicGroup R.descent.torus) t R.descent.data.torusIso
          let dB := descentComparison (closedSubgroupAlgebraicGroup Q.B)
            (closedSubgroupAlgebraicGroup R.descent.borel) t R.descent.data.borelIso
          let φ := j ≪≫ (a.app Q.G.val).symm ≪≫ E.mapIso dG ≪≫ a.app R.descent.group.val
          let τ := jT ≪≫ (a.app Q.T.group).symm ≪≫ E.mapIso dT ≪≫ a.app R.descent.torus.group
          let β := jB ≪≫ (a.app Q.B.group).symm ≪≫ E.mapIso dB ≪≫ a.app R.descent.borel.group
          IsTowerComparison a ∧ RespectsIntegralMarking R.fibre C j ∧
          IsScalarExtensionComparison t ∧ IsUnitComparison F L v ∧
          IsTransportedBasedAction R.descent.data ∧
          P.T.inclusion ≫ j.hom = jT.hom ≫ U.map Q.T.inclusion ∧
          P.B.inclusion ≫ j.hom = jB.hom ≫ U.map Q.B.inclusion ∧
          B.map Q.T.inclusion ≫ dG.hom = dT.hom ≫ B.map R.descent.torus.inclusion ∧
          B.map Q.B.inclusion ≫ dG.hom = dB.hom ≫ B.map R.descent.borel.inclusion ∧
          P.T.inclusion ≫ φ.hom = τ.hom ≫ U.map R.descent.torus.inclusion ∧
          P.B.inclusion ≫ φ.hom = β.hom ≫ U.map R.descent.borel.inclusion ∧
          ∀ (i j : D.base.support) (σ : Gal(K/F)),
            simplePermutationHom D (markedDiagramEquiv R.fibre.realization (R.descent.data.outer σ))
              i = j →
            U.map s ≫ τ.inv ≫ (C.realization.simpleRoot i).val.val =
              U.map s ≫ τ.inv ≫ (C.realization.simpleRoot j).val.val

end

end LinearAlgebraicGroups.Specs.ExceptionalAdaptedPinnedOuterComparison
