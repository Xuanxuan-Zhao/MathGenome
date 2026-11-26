import Specs.LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedPinnedOuterComparison
import LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedBaseChange
import LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent
import LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel
import LinearAlgebraicGroups.Relative.RelativeChambers
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedPinnedOuterComparison

open LinearAlgebraicGroups.Specs
open Specs.ExceptionalAdaptedPinnedOuterComparison
open Specs.CharacterDescent (Character)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.ExceptionalAffineBruhat (RamifiedReference)
open Specs.ExceptionalInnerStandardTorusDescent (markedCharacter)
open Specs.ExceptionalMarkedRootDescent (MarkedFibre)
open Specs.ExceptionalValuedTorusNormalizer (markedDiagramEquiv simplePermutationHom)
open Specs.GeometricRadicals (IsSplitTorus)
open Specs.IntegralSemisimpleModel (Model)
open Specs.Pinning (BasedRootDatum)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {D : BasedRootDatum.{u}} {M : Model D}

private abbrev multiplicativeGroup (k : Type u) [Field k] : GroupScheme k :=
  specGroup (groupAlgebra k IntegerCharacters)

section SplitFibreComparison

variable {K : Type u} [Field K]

open Opposite
open Specs.AdjointRepresentation (GroupPoints)
open Specs.ExceptionalIwahoriImageComparison (markedPositiveBorel)
open Specs.ExceptionalMarkedRootDescent (markedFibrePoint integralTestAlgebra)
open Specs.GeometricRadicals (baseChangedSubgroup)
open Specs.IntegralSemisimpleModel (splitTorus IntegralPoints)
open Specs.Unipotent (baseChangedAlgebraicGroup)
open LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison (markedPositiveBorelCoordinates)
open private positiveAndNegativeEnumerations
  from LinearAlgebraicGroups.Arithmetic.ExceptionalIwahoriImageComparison
open private fibrePointEquiv markedTorusEquiv markedTorusIncl
  from LinearAlgebraicGroups.Arithmetic.ExceptionalMarkedRootDescent
open private subgroupIso_of_pointwise baseChange_subgroupPoint_iff
  from LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedPairCompatibility

private theorem markedPoint_torus_iff (C : MarkedFibre M K) (R : TestAlgebra K)
    (p : GroupPoints C.realization.pinned.pair.G.val R) :
    (∃ t : GroupPoints C.realization.pinned.pair.T.group R,
      t ≫ C.realization.pinned.pair.T.inclusion.hom.hom = p) ↔
    ∃ v : IntegralPoints (splitTorus D) ((integralTestAlgebra K).obj R),
      v ≫ M.torus.hom.hom = markedFibrePoint C R p := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨markedTorusEquiv C R t, (markedTorusIncl C R t).symm⟩
  · rintro ⟨v, hv⟩
    obtain ⟨t, rfl⟩ := (markedTorusEquiv C R).surjective v
    refine ⟨t, (fibrePointEquiv C R).injective ?_⟩
    exact (markedTorusIncl C R t).trans hv

private theorem markedPoint_borel_iff (C : MarkedFibre M K) (R : TestAlgebra K)
    (p : GroupPoints C.realization.pinned.pair.G.val R) :
    (∃ x : GroupPoints C.realization.pinned.pair.B.group R,
      x ≫ C.realization.pinned.pair.B.inclusion.hom.hom = p) ↔
    markedFibrePoint C R p ∈ markedPositiveBorel C R := by
  have he (x : GroupPoints C.realization.pinned.pair.B.group R) :
      markedFibrePoint C R (x ≫ C.realization.pinned.pair.B.inclusion.hom.hom) =
        IntegralSemisimpleModel.forgetFibrePoint M.group R
          (x ≫ C.realization.pinned.pair.B.inclusion.hom.hom ≫ C.groupIso.inv.hom.hom) := by
    unfold markedFibrePoint
    rw [Category.assoc]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, (he x).symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (fibrePointEquiv C R).injective ((he x).trans hx)⟩

variable {L : Type u} [Field L] [Algebra K L]

/-- The integral marking comparison identifies the actual Borel and torus
in each split fibre. -/
private theorem markedFibrePairComparison (C₀ : MarkedFibre M K) (C₁ : MarkedFibre M L)
    (j : C₁.realization.pinned.pair.G.val ≅
      (groupBaseChange K L).obj C₀.realization.pinned.pair.G.val)
    (hj : RespectsIntegralMarking C₀ C₁ j) :
    let P₀ := C₀.realization.pinned.pair
    let P₁ := C₁.realization.pinned.pair
    let B := groupBaseChange K L
    ∃ (jT : P₁.T.group ≅ B.obj P₀.T.group) (jB : P₁.B.group ≅ B.obj P₀.B.group),
      P₁.T.inclusion ≫ j.hom = jT.hom ≫ B.map P₀.T.inclusion ∧
      P₁.B.inclusion ≫ j.hom = jB.hom ≫ B.map P₀.B.inclusion := by
  let P₀ := C₀.realization.pinned.pair
  let P₁ := C₁.realization.pinned.pair
  let H := baseChangedAlgebraicGroup L P₀.G
  let T := baseChangedSubgroup L P₀.T
    (baseChangeClosedSubgroup K L P₀.T.inclusion P₀.T.isClosedImmersion)
  let B := baseChangedSubgroup L P₀.B
    (baseChangeClosedSubgroup K L P₀.B.inclusion P₀.B.isClosedImmersion)
  obtain ⟨_, roots, _, hroots⟩ := positiveAndNegativeEnumerations D
  obtain ⟨jT, hT⟩ := subgroupIso_of_pointwise (H := H) P₁.T T j (by
    intro R p
    change _ ↔ ∃ t : GroupPoints ((groupBaseChange K L).obj P₀.T.group) R,
      t ≫ ((groupBaseChange K L).map P₀.T.inclusion).hom.hom = p ≫ j.hom.hom.hom
    rw [baseChange_subgroupPoint_iff, markedPoint_torus_iff C₁, markedPoint_torus_iff C₀, hj R p])
  obtain ⟨jB, hB⟩ := subgroupIso_of_pointwise (H := H) P₁.B B j (by
    intro R p
    change _ ↔ ∃ b : GroupPoints ((groupBaseChange K L).obj P₀.B.group) R,
      b ≫ ((groupBaseChange K L).map P₀.B.inclusion).hom.hom = p ≫ j.hom.hom.hom
    rw [baseChange_subgroupPoint_iff, markedPoint_borel_iff C₁, markedPoint_borel_iff C₀, hj R p,
      markedPositiveBorelCoordinates C₁ _ roots hroots,
      markedPositiveBorelCoordinates C₀ _ roots hroots])
  exact ⟨jT, jB, hT, hB⟩


open Specs.CharacterPairing (characterValue)
open Specs.ExceptionalInnerStandardTorusDescent (IsUnitComparison)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters)
open Specs.IntegralSemisimpleModel (TorusValues torusPoint Integers)
open LinearAlgebraicGroups.RootData.CharacterPairing (characterValuesDetectCharacters)
open private characterValue_extend from LinearAlgebraicGroups.Relative.RelativeChambers
open private affineTorusPointEquiv from LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

private theorem markedCharacter_evaluation (C : MarkedFibre M K) (R : TestAlgebra K)
    (p : GroupPoints C.realization.pinned.pair.T.group R) (i : D.I)
    (v : TorusValues D ((integralTestAlgebra K).obj R))
    (hv : markedTorusEquiv C R p = torusPoint D ((integralTestAlgebra K).obj R) v) :
    characterValue (markedCharacter C i) R p = (v (Multiplicative.ofAdd (D.datum.root i)) : R) := by
  have h := C.torus_eval R (p ≫ C.torusIso.inv.hom.hom) v hv (D.datum.root i)
  rw [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id] at h
  change characterValue (markedCharacter C i) R (p ≫ 𝟙 _) = _ at h
  rwa [Category.comp_id] at h

private theorem markedCharacter_baseChange (C₀ : MarkedFibre M K) (C₁ : MarkedFibre M L)
    (j : C₁.realization.pinned.pair.G.val ≅
      (groupBaseChange K L).obj C₀.realization.pinned.pair.G.val)
    (hj : RespectsIntegralMarking C₀ C₁ j)
    (jT : C₁.realization.pinned.pair.T.group ≅
      (groupBaseChange K L).obj C₀.realization.pinned.pair.T.group)
    (hjT : C₁.realization.pinned.pair.T.inclusion ≫ j.hom =
      jT.hom ≫ (groupBaseChange K L).map C₀.realization.pinned.pair.T.inclusion)
    (e : multiplicativeGroup L ≅ (groupBaseChange K L).obj (multiplicativeGroup K))
    (he : IsUnitComparison K L e) (i : D.I) :
    jT.hom ≫ (groupBaseChange K L).map (markedCharacter C₀ i) ≫ e.inv =
      markedCharacter C₁ i := by
  let T₀ := C₀.realization.pinned.pair.T
  let T₁ := C₁.realization.pinned.pair.T
  apply characterValuesDetectCharacters C₁.realization.pinned.pair.split
  intro R p
  let R₀ := (restrictTestAlgebra K L).obj R
  let p₀ := baseChangePoint K L T₀.group.X R (p ≫ jT.hom.hom.hom)
  have hp : markedTorusEquiv C₀ R₀ p₀ = markedTorusEquiv C₁ R p := by
    let _ := M.torusClosed
    let _ : Mono M.torus.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono M.torus.hom.hom).mp
    rw [← markedTorusIncl, ← markedTorusIncl]
    have h := hj R (p ≫ T₁.inclusion.hom.hom)
    change markedFibrePoint C₀ R₀
      (baseChangePoint K L C₀.realization.pinned.pair.G.val.X R
        ((p ≫ T₁.inclusion.hom.hom) ≫ j.hom.hom.hom)) = _ at h
    have hn := baseChangePointsSchemeNaturality K L T₀.inclusion.hom.hom R
      (p ≫ jT.hom.hom.hom)
    change baseChangePoint K L C₀.realization.pinned.pair.G.val.X R
      ((p ≫ jT.hom.hom.hom) ≫ ((groupBaseChange K L).map T₀.inclusion).hom.hom) =
      p₀ ≫ T₀.inclusion.hom.hom at hn
    rw [Category.assoc, ← Grp.comp_hom_hom, hjT, Grp.comp_hom_hom, ← Category.assoc] at h
    change markedFibrePoint C₀ R₀ (baseChangePoint K L _ R
      ((p ≫ jT.hom.hom.hom) ≫ ((groupBaseChange K L).map T₀.inclusion).hom.hom)) = _ at h
    exact (congrArg (markedFibrePoint C₀ R₀) hn).symm.trans h
  obtain ⟨v, hv⟩ := (affineTorusPointEquiv (k := Integers.{u}) (M := Multiplicative D.X)
    ((integralTestAlgebra L).obj R)).surjective (markedTorusEquiv C₁ R p)
  have hv₀ : markedTorusEquiv C₀ R₀ p₀ = torusPoint D ((integralTestAlgebra K).obj R₀) v :=
    hp.trans hv.symm
  calc
    _ = characterValue ((groupBaseChange K L).map (markedCharacter C₀ i) ≫ e.inv) R
          (p ≫ jT.hom.hom.hom) := by
      unfold characterValue
      rw [Grp.comp_hom_hom, ← Category.assoc]
    _ = characterValue (markedCharacter C₀ i) R₀ p₀ :=
      characterValue_extend (markedCharacter C₀ i) e he R (p ≫ jT.hom.hom.hom)
    _ = (v (Multiplicative.ofAdd (D.datum.root i)) : R) := markedCharacter_evaluation C₀ R₀ p₀ i v hv₀
    _ = _ := (markedCharacter_evaluation C₁ R p i v hv.symm).symm

end SplitFibreComparison

private theorem markedCharacter_eq_simple {k : Type u} [Field k]
    (C : MarkedFibre M k) (i : D.base.support) :
    markedCharacter C i = (C.realization.simpleRoot i).val.val := by
  let _ := C.realization.attached.comm
  apply Additive.ofMul.injective
  change C.realization.datumIso.val.weightEquiv (D.datum.root i) =
    Additive.ofMul (C.realization.simpleRoot i).val.val
  rw [← C.realization.attached.datum.root_eq]
  exact RootPairing.Hom.root_weightMap_apply _ _ i.val C.realization.datumIso.val.toHom

open private extendedGroupIso extendedSpecIso_hom_fst
  from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private extendedCoordinateIso from LinearAlgebraicGroups.Descent.AdjointBorelCohomology
open private scalarExtensionComparison scalarExtensionComparison_comm
  transportedBasedAction basedLift_of_splitSequence
  from LinearAlgebraicGroups.Arithmetic.QuasiSplitPinnedPairModel

section OuterCharacterDescent

open Opposite
open scoped TensorProduct
open Specs.AdjointBorelCohomology (extendedCharacterValue)
open Specs.DiagonalizableGroups (groupAlgebra IntegerCharacters integerGenerator)
open LinearAlgebraicGroups.Descent (SemilinearAction)
open _root_.LinearAlgebraicGroups.CharacterDescent (baseChangeCharacterMap baseChangeCharacterMap_bijective)
open _root_.LinearAlgebraicGroups.CharacterDescent (groupAlgebraBaseChange mapGroupLike)
open private integerHopfHomEquiv
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private baseHom_equivariant from LinearAlgebraicGroups.Descent.Forms
open private splitTorusCoordinateDiagonalizable
  from LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer
open private specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private extendedCoordinateIso_natural extendedGroupIso_natural
  characterCoordinates characterCoordinates_spec extendedCharacterValue_twist
  from LinearAlgebraicGroups.Descent.AdjointBorelCohomology

private theorem extendedGm_HopfHom_ext {k E : Type u} [Field k] [Field E] [Algebra k E]
    {A : HopfAlgebraCategory E} {f g : extendedHopf E (groupAlgebra k IntegerCharacters) ⟶ A}
    (h : f.hom (1 ⊗ₜ[k] MonoidAlgebra.of k _ integerGenerator) =
      g.hom (1 ⊗ₜ[k] MonoidAlgebra.of k _ integerGenerator)) :
    f = g := by
  let d : extendedHopf E (groupAlgebra k IntegerCharacters.{u}) ≅
      groupAlgebra E IntegerCharacters.{u} :=
    CommHopfAlgCat.isoMk (groupAlgebraBaseChange k E IntegerCharacters.{u})
  apply (cancel_epi d.inv).mp
  apply (integerHopfHomEquiv A).symm.injective
  apply GroupLike.val_injective
  change f.hom ((groupAlgebraBaseChange k E IntegerCharacters.{u}).symm
      (MonoidAlgebra.single integerGenerator 1)) =
    g.hom ((groupAlgebraBaseChange k E IntegerCharacters.{u}).symm
      (MonoidAlgebra.single integerGenerator 1))
  have hd : (groupAlgebraBaseChange k E IntegerCharacters.{u}).symm
      (MonoidAlgebra.single integerGenerator (1 : E)) =
      (1 : E) ⊗ₜ[k] MonoidAlgebra.single integerGenerator (1 : k) :=
    MonoidAlgebra.scalarTensorEquiv_symm_single integerGenerator 1
  rw [hd]
  exact h

private theorem finiteRestriction_under_pinnedComparison {k E : Type u}
    [Field k] [Field E] [Algebra k E]
    (U T T₀ : AffineAlgebraicGroup k) (s : U.val ⟶ T.val)
    (i : extendedHopf E (Specs.AdjointCocharacters.coordinateHopf T₀) ≅ extendedHopf E (Specs.AdjointCocharacters.coordinateHopf T))
    (χ χ' : Character T₀.val)
    (h : (extendedHopfMap E (Specs.AdjointCocharacters.coordinateHopfMap s)).hom (i.hom.hom (extendedCharacterValue E T₀ χ)) =
         (extendedHopfMap E (Specs.AdjointCocharacters.coordinateHopfMap s)).hom (i.hom.hom (extendedCharacterValue E T₀ χ'))) :
    let B := groupBaseChange k E
    let t := descentComparison T₀ T (extendedGroupIso E) i
    B.map s ≫ t.inv ≫ B.map χ = B.map s ≫ t.inv ≫ B.map χ' := by
  let B := groupBaseChange k E
  let t := descentComparison T₀ T (extendedGroupIso E) i
  let q (a : Character T₀.val) := (extendedHopfMap E (characterCoordinates a)) ≫ i.hom ≫
    extendedHopfMap E (Specs.AdjointCocharacters.coordinateHopfMap s)
  have hq : q χ = q χ' := extendedGm_HopfHom_ext h
  have eq (a : Character T₀.val) :
      (extendedCoordinateIso (K := E) U).hom ≫ B.map s ≫ t.inv ≫ B.map a =
        specGroupMap (q a) ≫ (extendedGroupIso E (groupAlgebra k IntegerCharacters)).hom := by
    have hs : (extendedCoordinateIso (K := E) U).hom ≫ B.map s =
        specGroupMap (extendedHopfMap E (Specs.AdjointCocharacters.coordinateHopfMap (G := U) (H := T) s)) ≫
          (extendedCoordinateIso (K := E) T).hom :=
      (extendedCoordinateIso_natural (G := U) (H := T) (K := E) s).symm
    have hc : (extendedCoordinateIso (K := E) T₀).hom ≫ B.map a =
        specGroupMap (extendedHopfMap E (characterCoordinates (G := T₀) a)) ≫
          (extendedGroupIso E (groupAlgebra k IntegerCharacters)).hom := by
      have h := extendedGroupIso_natural (K := E) (characterCoordinates (G := T₀) a)
      rw [characterCoordinates_spec, Functor.map_comp] at h
      exact h.symm
    have ht : t.inv = (extendedCoordinateIso (K := E) T).inv ≫ specGroupMap i.hom ≫
        (extendedCoordinateIso (K := E) T₀).hom := by
      simp only [t, descentComparison, extendedCoordinateIso, Iso.trans_inv, Iso.trans_hom,
        Iso.symm_inv, Category.assoc]
      rfl
    rw [← Category.assoc (extendedCoordinateIso (K := E) U).hom, hs, ht]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, q, specGroupMap_comp]
    rw [hc]
  change B.map s ≫ t.inv ≫ B.map χ = B.map s ≫ t.inv ≫ B.map χ'
  apply (cancel_epi (extendedCoordinateIso (K := E) U).hom).mp
  rw [eq, eq, hq]

set_option maxHeartbeats 800000 in
private theorem pinnedOrbitRestriction_eq {k E : Type u} [Field k] [Field E] [Algebra k E]
    (R : RamifiedReference k E M)
    (S : ClosedSubgroup R.descent.group.val) (hS : IsSplitTorus S.group)
    (s : S.group ⟶ R.descent.torus.group) (i j : D.base.support) (σ : Gal(E/k))
    (hij : simplePermutationHom D
      (markedDiagramEquiv R.fibre.realization (R.descent.data.outer σ)) i = j) :
    let P := R.fibre.realization.pinned.pair
    let T₀ := closedSubgroupAlgebraicGroup P.T
    let T := closedSubgroupAlgebraicGroup R.descent.torus
    let t := descentComparison T₀ T (extendedGroupIso E) R.descent.data.torusIso
    let B := groupBaseChange k E
    B.map s ≫ t.inv ≫ B.map (markedCharacter R.fibre i) =
      B.map s ≫ t.inv ≫ B.map (markedCharacter R.fibre j) := by
  let P := R.fibre.realization.pinned.pair
  let T₀ := closedSubgroupAlgebraicGroup P.T
  let T := closedSubgroupAlgebraicGroup R.descent.torus
  let U := closedSubgroupAlgebraicGroup S
  let q := Specs.AdjointCocharacters.coordinateHopfMap (G := U) (H := T) s
  obtain ⟨e, he, hρ⟩ := transportedBasedAction R.descent.data (basedLift_of_splitSequence R.sequence)
  let x := e (markedCharacter R.fibre i)
  let y := e (markedCharacter R.fibre j)
  let u := mapGroupLike (extendedHopfMap E q) x
  have hρ' : (SemilinearAction.scalarExtension (K := E) (Specs.AdjointCocharacters.coordinateHopf T)).act σ x.val = y.val := by
    have hm := (LinearAlgebraicGroups.Arithmetic.ExceptionalValuedTorusNormalizer.markedPinnedDiagramAction
      R.fibre.realization R.sequence (R.descent.data.outer σ)).1 i
    have hχ : Specs.Pinning.transportCharacter (R.pin (R.descent.data.outer σ)).asIso.hom.torus
        (markedCharacter R.fibre i) = markedCharacter R.fibre j := by
      rw [markedCharacter_eq_simple, markedCharacter_eq_simple]
      rw [← hij]
      exact hm
    have h := extendedCharacterValue_twist R.descent.data σ (markedCharacter R.fibre i)
    dsimp only at h
    rw [hχ] at h
    rw [show x.val = _ from he (markedCharacter R.fibre i),
      show y.val = _ from he (markedCharacter R.fibre j)]
    exact h
  have hu : (SemilinearAction.scalarExtension (K := E) (Specs.AdjointCocharacters.coordinateHopf U)).act σ u.val = u.val := by
    obtain ⟨v, hv⟩ := (baseChangeCharacterMap_bijective E (Specs.AdjointCocharacters.coordinateHopf U)
      (splitTorusCoordinateDiagonalizable U hS)).surjective u
    rw [← hv]
    change σ 1 ⊗ₜ[k] v.val = (1 : E) ⊗ₜ[k] v.val
    rw [map_one]
  have hq : (extendedHopfMap E q).hom y.val = (extendedHopfMap E q).hom x.val := by
    rw [← hρ']
    exact (baseHom_equivariant (K := E) q σ x.val).trans hu
  apply finiteRestriction_under_pinnedComparison U T T₀ s R.descent.data.torusIso
  exact (by rw [← he, ← he]; exact hq.symm)

end OuterCharacterDescent

section ComparisonSquares

open Specs.AdjointCocharacters (coordinateHopfMap)

private theorem descentComparison_eq_scalar {k K : Type u} [Field k] [Field K] [Algebra k K]
    (X Y : AffineAlgebraicGroup k)
    (i : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf X) ≅
      extendedHopf K (Specs.AdjointCocharacters.coordinateHopf Y)) :
    descentComparison X Y (extendedGroupIso K) i = scalarExtensionComparison X Y i := by
  simp only [descentComparison, scalarExtensionComparison, extendedCoordinateIso, Iso.trans_symm,
    Iso.trans_assoc]

private theorem descentComparison_comm {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G H X Y : AffineAlgebraicGroup k}
    (f : X.val ⟶ G.val) (g : Y.val ⟶ H.val)
    (i : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf G) ≅
      extendedHopf K (Specs.AdjointCocharacters.coordinateHopf H))
    (d : extendedHopf K (Specs.AdjointCocharacters.coordinateHopf X) ≅
      extendedHopf K (Specs.AdjointCocharacters.coordinateHopf Y))
    (h : i.hom ≫ extendedHopfMap K (coordinateHopfMap g) =
      extendedHopfMap K (coordinateHopfMap f) ≫ d.hom) :
    (groupBaseChange k K).map f ≫ (descentComparison G H (extendedGroupIso K) i).hom =
      (descentComparison X Y (extendedGroupIso K) d).hom ≫ (groupBaseChange k K).map g := by
  rw [descentComparison_eq_scalar, descentComparison_eq_scalar]
  exact scalarExtensionComparison_comm f g i d h

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  {B : C₁ ⥤ C₂} {E : C₂ ⥤ C₃} {U : C₁ ⥤ C₃}

/-- Transport the finite square through the scalar tower and the change of marking. -/
private theorem extendComparison_square (a : B ⋙ E ≅ U)
    {X₀ T₀ X₁ T₁ : C₁} {X T : C₃} (i₀ : T₀ ⟶ X₀) (i₁ : T₁ ⟶ X₁) (i : T ⟶ X)
    (g : B.obj X₀ ≅ B.obj X₁) (d : B.obj T₀ ≅ B.obj T₁)
    (j : X ≅ U.obj X₀) (jT : T ≅ U.obj T₀)
    (h₀ : i ≫ j.hom = jT.hom ≫ U.map i₀) (h₁ : B.map i₀ ≫ g.hom = d.hom ≫ B.map i₁) :
    i ≫ (j ≪≫ (a.app X₀).symm ≪≫ E.mapIso g ≪≫ a.app X₁).hom =
      (jT ≪≫ (a.app T₀).symm ≪≫ E.mapIso d ≪≫ a.app T₁).hom ≫ U.map i₁ := by
  have hinv := a.inv.naturality i₀
  change U.map i₀ ≫ (a.app X₀).inv = (a.app T₀).inv ≫ E.map (B.map i₀) at hinv
  have hmap : E.map (B.map i₀) ≫ E.map g.hom = E.map d.hom ≫ E.map (B.map i₁) := by
    rw [← E.map_comp, ← E.map_comp, h₁]
  have hhom := a.hom.naturality i₁
  change E.map (B.map i₁) ≫ (a.app X₁).hom = (a.app T₁).hom ≫ U.map i₁ at hhom
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  rw [reassoc_of% h₀, reassoc_of% hinv, reassoc_of% hmap, hhom]

/-- Express the geometric character restriction as scalar extension of its finite restriction. -/
private theorem extendComparison_restriction (a : B ⋙ E ≅ U)
    {S T₀ T₁ A : C₁} {T Gm : C₃} (s : S ⟶ T₁) (χ : T₀ ⟶ A) (ψ : T ⟶ Gm)
    (d : B.obj T₀ ≅ B.obj T₁) (jT : T ≅ U.obj T₀) (v : Gm ≅ U.obj A)
    (hχ : jT.hom ≫ U.map χ ≫ v.inv = ψ) :
    U.map s ≫ (jT ≪≫ (a.app T₀).symm ≪≫ E.mapIso d ≪≫ a.app T₁).inv ≫ ψ =
      (a.app S).inv ≫ E.map (B.map s ≫ d.inv ≫ B.map χ) ≫ (a.app A).hom ≫ v.inv := by
  have hinv := a.inv.naturality s
  change U.map s ≫ (a.app T₁).inv = (a.app S).inv ≫ E.map (B.map s) at hinv
  have hhom := a.hom.naturality χ
  change E.map (B.map χ) ≫ (a.app A).hom = (a.app T₀).hom ≫ U.map χ at hhom
  rw [← hχ]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Category.assoc,
    Iso.inv_hom_id_assoc, Functor.map_comp]
  rw [reassoc_of% hinv, reassoc_of% hhom]

end ComparisonSquares

open Specs.ExceptionalInnerStandardTorusDescent (IsUnitComparison)
open Specs.QuasiSplitPinnedPairModel (IsTransportedBasedAction)
open Descent.Forms (IsScalarExtensionComparison)
open LinearAlgebraicGroups.Arithmetic.ExceptionalInnerStandardTorusDescent (unitComparison)
open LinearAlgebraicGroups.Arithmetic.ExceptionalPinnedBaseChange (markedSplitGroupComparison)
open private groupBaseChangeTowerIso groupBaseChangeTowerIso_fst
  from LinearAlgebraicGroups.Relative.RationalCocharacter

/-- Transport the equality of finite restrictions to the simple roots of the marked fibre. -/
private theorem pinnedOrbitRestriction_overTower {F K L : Type u}
    [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L]
    (R : RamifiedReference F K M) (S : ClosedSubgroup R.descent.group.val) (hS : IsSplitTorus S.group)
    (s : S.group ⟶ R.descent.torus.group) (C : MarkedFibre M L)
    (a : groupBaseChange F K ⋙ groupBaseChange K L ≅ groupBaseChange F L)
    (j : C.realization.pinned.pair.G.val ≅
      (groupBaseChange F L).obj R.fibre.realization.pinned.pair.G.val)
    (hj : RespectsIntegralMarking R.fibre C j)
    (jT : C.realization.pinned.pair.T.group ≅
      (groupBaseChange F L).obj R.fibre.realization.pinned.pair.T.group)
    (hjT : C.realization.pinned.pair.T.inclusion ≫ j.hom =
      jT.hom ≫ (groupBaseChange F L).map R.fibre.realization.pinned.pair.T.inclusion)
    (v : multiplicativeGroup L ≅ (groupBaseChange F L).obj (multiplicativeGroup F))
    (hv : IsUnitComparison F L v) (i i' : D.base.support) (σ : Gal(K/F))
    (hσ : simplePermutationHom D
      (markedDiagramEquiv R.fibre.realization (R.descent.data.outer σ)) i = i') :
    let E := groupBaseChange K L
    let U := groupBaseChange F L
    let Q := R.fibre.realization.pinned.pair
    let dT := descentComparison (closedSubgroupAlgebraicGroup Q.T)
      (closedSubgroupAlgebraicGroup R.descent.torus) (extendedGroupIso (k := F) K) R.descent.data.torusIso
    let τ := jT ≪≫ (a.app Q.T.group).symm ≪≫ E.mapIso dT ≪≫ a.app R.descent.torus.group
    U.map s ≫ τ.inv ≫ (C.realization.simpleRoot i).val.val =
      U.map s ≫ τ.inv ≫ (C.realization.simpleRoot i').val.val := by
  let B := groupBaseChange F K
  let E := groupBaseChange K L
  let U := groupBaseChange F L
  let Q := R.fibre.realization.pinned.pair
  let dT := descentComparison (closedSubgroupAlgebraicGroup Q.T)
    (closedSubgroupAlgebraicGroup R.descent.torus) (extendedGroupIso (k := F) K) R.descent.data.torusIso
  let τ := jT ≪≫ (a.app Q.T.group).symm ≪≫ E.mapIso dT ≪≫ a.app R.descent.torus.group
  have hcomp (m : D.base.support) :
      U.map s ≫ τ.inv ≫ (C.realization.simpleRoot m).val.val =
        (a.app S.group).inv ≫ E.map (B.map s ≫ dT.inv ≫ B.map (markedCharacter R.fibre m)) ≫
          (a.app (multiplicativeGroup F)).hom ≫ v.inv :=
    extendComparison_restriction (B := B) (E := E) (U := U) a s
      (markedCharacter R.fibre m) (C.realization.simpleRoot m).val.val dT jT v
      ((markedCharacter_baseChange R.fibre C j hj jT hjT v hv m).trans
        (markedCharacter_eq_simple C m))
  have hf : B.map s ≫ dT.inv ≫ B.map (markedCharacter R.fibre i) =
      B.map s ≫ dT.inv ≫ B.map (markedCharacter R.fibre i') :=
    pinnedOrbitRestriction_eq R S hS s i i' σ hσ
  exact (hcomp i).trans ((congrArg
    (fun f => (a.app S.group).inv ≫ E.map f ≫ (a.app (multiplicativeGroup F)).hom ≫ v.inv)
    hf).trans (hcomp i').symm)


set_option maxHeartbeats 1200000 in
/-- Compare the pinned descent with the split marked fibre over the separable closure. -/
theorem pinnedOuterComparison : Statement.{u} := by
  intro F K _ _ _ _ _ D M R S hS s _
  let L := SeparableClosure F
  let e : K →ₐ[F] L := IsSepClosed.lift
  refine ⟨e, ?_⟩
  let : Algebra K L := e.toRingHom.toAlgebra
  let : IsScalarTower F K L := IsScalarTower.of_algebraMap_eq fun x => (e.commutes x).symm
  let C : MarkedFibre M L := Classical.choice (ExceptionalMarkedRootDescent.markedFibreExists M L)
  obtain ⟨j, hj⟩ := markedSplitGroupComparison R.fibre C
  obtain ⟨jT, jB, hjT, hjB⟩ := markedFibrePairComparison R.fibre C j hj
  obtain ⟨v, hv⟩ := unitComparison F L
  let a := groupBaseChangeTowerIso (k := F) (K := K) (L := L)
  let B := groupBaseChange F K
  let E := groupBaseChange K L
  let U := groupBaseChange F L
  let Q := R.fibre.realization.pinned.pair
  let P := C.realization.pinned.pair
  let t := extendedGroupIso (k := F) K
  let dG := descentComparison Q.G R.descent.group t R.descent.data.groupIso
  let dT := descentComparison (closedSubgroupAlgebraicGroup Q.T)
    (closedSubgroupAlgebraicGroup R.descent.torus) t R.descent.data.torusIso
  let dB := descentComparison (closedSubgroupAlgebraicGroup Q.B)
    (closedSubgroupAlgebraicGroup R.descent.borel) t R.descent.data.borelIso
  have hTfinite : B.map Q.T.inclusion ≫ dG.hom = dT.hom ≫ B.map R.descent.torus.inclusion :=
    descentComparison_comm (G := Q.G) (H := R.descent.group)
      (X := closedSubgroupAlgebraicGroup Q.T) (Y := closedSubgroupAlgebraicGroup R.descent.torus)
      Q.T.inclusion R.descent.torus.inclusion
      R.descent.data.groupIso R.descent.data.torusIso R.descent.data.torusComm
  have hBfinite : B.map Q.B.inclusion ≫ dG.hom = dB.hom ≫ B.map R.descent.borel.inclusion :=
    descentComparison_comm (G := Q.G) (H := R.descent.group)
      (X := closedSubgroupAlgebraicGroup Q.B) (Y := closedSubgroupAlgebraicGroup R.descent.borel)
      Q.B.inclusion R.descent.borel.inclusion
      R.descent.data.groupIso R.descent.data.borelIso R.descent.data.borelComm
  have hTgeom := extendComparison_square (B := B) (E := E) (U := U) a Q.T.inclusion
    R.descent.torus.inclusion P.T.inclusion dG dT j jT hjT hTfinite
  have hBgeom := extendComparison_square (B := B) (E := E) (U := U) a Q.B.inclusion
    R.descent.borel.inclusion P.B.inclusion dG dB j jB hjB hBfinite
  have ha : IsTowerComparison a := groupBaseChangeTowerIso_fst
  have ht : IsScalarExtensionComparison t := extendedSpecIso_hom_fst K
  have haction : IsTransportedBasedAction R.descent.data :=
    transportedBasedAction R.descent.data (basedLift_of_splitSequence R.sequence)
  refine ⟨C, a, t, v, j, jT, jB, ha, hj, ht, hv, haction, hjT, hjB,
    hTfinite, hBfinite, hTgeom, hBgeom, ?_⟩
  intro i i' σ hσ
  exact pinnedOrbitRestriction_overTower R S hS s C a j hj jT hjT v hv i i' σ hσ

end

end LinearAlgebraicGroups.Arithmetic.ExceptionalAdaptedPinnedOuterComparison
