import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeRankAdjoint
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.CartesianMonoidalCategory Opposite Coalgebra
open scoped CategoryTheory.MonoidalCategory CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Descent.RelativeRank

noncomputable section

open _root_.LinearAlgebraicGroups.Specs
open Specs.GeometricRadicals (IsReductive IsSemisimple IsSplitTorus IsTorus)
open Specs.AdjointCocharacters (IsAdjointQuotient)
open Specs.Unipotent (closedSubgroupAlgebraicGroup)
open LinearAlgebraicGroups.CentralFrobeniusDescent
  (powerHom powerHom_onSections torus_commutative torus_power_flat_surjective)
open private torusInMaximalTorus reductive_of_central_quotient
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
open private quotientKernelPair preimageSubgroup kernel_of_preimage
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent
open private scheme_dimension_eq_of_finite_surjective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Classification.CentralIsogenies
open private splitTorusImage
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Relative.MaximalSplitTori
open private isTorus_of_split
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.FiniteFieldFlags
open private connected_of_geometricallyConnected
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.BorelsAndChambers
open private reductive_of_semisimple split_dimension_le_rank
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.RelativeRank

open Specs.SmoothnessAndIsogenies (pullbackCharacter)
open Specs.CharacterDescent (GeometricCharacters MultiplicativeTypeHopf)
open LinearAlgebraicGroups.CharacterDescent (geometricCharacterFunctor geometricAction)

open private coordinatePresentationMap coordinatePresentationTorus coordinatePresentationSurjective
  coordinatePresentationFiniteKernel pullbackCharacter_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Descent.AdjointCocharacters
open private geometricCharacterFunctor_full geometricCharacterFunctor_faithful
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.CharacterDescent
open private splitByCharacters
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Multiplicative.SmoothnessAndIsogenies
open private extendedGroupIso extendedSpecIso_natural specGroupMap_comp
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private isCommMonObj_of_groupIso
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.HopfAlgebras
open private powerHom_iso powerHom_baseChange splitDiagonal_commutative
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Reductive.CentralFrobeniusDescent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1300000

variable {k : Type u} [Field k]

private theorem geometricPowerPullback
    {K : Type u} [Field K] [Algebra k K] [IsSepClosure k K]
    (A : HopfAlgebraCategory k) (hA : Specs.CharacterDescent.IsMultiplicativeType A)
    [IsCommMonObj (specGroup A).X] (n : ℕ) (a : A ⟶ A)
    (ha : specGroupMap a = powerHom (specGroup A) n) (χ : GeometricCharacters K A) :
    pullbackCharacter K a χ = χ ^ n := by
  let E := extendedGroupIso K A
  let D := (hopfSpec (CommRingCat.of K)).mapIso (splitByCharacters (K := K) A hA).op
  letI : IsCommMonObj (specGroup (extendedHopf K A)).X :=
    isCommMonObj_of_groupIso D.symm (splitDiagonal_commutative (GeometricCharacters K A))
  letI : IsCommMonObj ((groupBaseChange k K).obj (specGroup A)).X :=
    isCommMonObj_of_groupIso E inferInstance
  have hpower : specGroupMap (extendedHopfMap K a) =
      powerHom (specGroup (extendedHopf K A)) n := by
    apply (cancel_mono E.hom).mp
    rw [powerHom_iso E, ← powerHom_baseChange K n, ← ha]
    exact Grp.hom_ext _ _ (extendedSpecIso_natural K a)
  obtain ⟨e, he, _⟩ := LinearAlgebraicGroups.CharacterDescent.characterInterpretation (k := K)
  apply (e _).injective
  rw [map_pow]
  change e _ ⟨_, _⟩ = _
  rw [he, hpower]
  apply Grp.hom_ext
  change (powerHom (specGroup (extendedHopf K A)) n).hom.hom ≫ (e _ χ).hom.hom =
    ((e _ χ) ^ n).hom.hom
  simp only [powerHom, Grp.Hom.hom_pow, Mon.Hom.hom_pow]
  rw [MonObj.pow_comp]
  change ((𝟙 (specGroup (extendedHopf K A)).X) ≫ (e _ χ).hom.hom) ^ n = _
  rw [Category.id_comp]

private theorem finiteIndexReversePower {X Y : Type u} [CommGroup X] [CommGroup Y]
    (a : X →* Y) (ha : Function.Injective a) [Finite (Y ⧸ a.range)] :
    ∃ (n : ℕ), 0 < n ∧ ∃ b : Y →* X,
      (∀ x, a (b x) = x ^ n) ∧ (∀ y, b (a y) = y ^ n) := by
  let n := Nat.card (Y ⧸ a.range)
  have hpow (x : Y) : x ^ n ∈ a.range := by
    apply (QuotientGroup.eq_one_iff _).mp
    rw [QuotientGroup.mk_pow]
    exact pow_card_eq_one'
  let b₀ : Y →* a.range :=
    { toFun := fun x ↦ ⟨x ^ n, hpow x⟩
      map_one' := Subtype.ext (one_pow n)
      map_mul' := fun x y ↦ Subtype.ext (mul_pow x y n) }
  let e := MulEquiv.ofBijective a.rangeRestrict
    ⟨fun _ _ h ↦ ha (congrArg Subtype.val h), a.rangeRestrict_surjective⟩
  let b := e.symm.toMonoidHom.comp b₀
  have hab (x : Y) : a (b x) = x ^ n :=
    congrArg Subtype.val (e.apply_symm_apply (b₀ x))
  refine ⟨n, Nat.card_pos, b, hab, fun x ↦ ha ?_⟩
  rw [hab, map_pow]

set_option backward.isDefEq.respectTransparency true in
private theorem geometricReversePower
    {K : Type u} [Field K] [Algebra k K] [IsSepClosure k K]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B)
    (hAm : Specs.CharacterDescent.IsMultiplicativeType A)
    (hBm : Specs.CharacterDescent.IsMultiplicativeType B)
    (ha : Function.Injective (pullbackCharacter K f))
    [Finite (GeometricCharacters K B ⧸ (pullbackCharacter K f).range)]
    (z : ℕ → (A ⟶ A))
    (hz : ∀ (n : ℕ) (x : GeometricCharacters K A), pullbackCharacter K (z n) x = x ^ n) :
    ∃ (n : ℕ), 0 < n ∧ ∃ g : B ⟶ A, f ≫ g = z n := by
  let a := pullbackCharacter K f
  obtain ⟨n, hn, b, hab, hba⟩ := finiteIndexReversePower a ha
  let A' : MultiplicativeTypeHopf k :=
    ⟨⟨A, (LinearAlgebraicGroups.CharacterDescent.multiplicativeTypeProperties A hAm).1⟩, hAm⟩
  let B' : MultiplicativeTypeHopf k :=
    ⟨⟨B, (LinearAlgebraicGroups.CharacterDescent.multiplicativeTypeProperties B hBm).1⟩, hBm⟩
  let F := geometricCharacterFunctor (k := k) K
  letI : F.Full := geometricCharacterFunctor_full K
  letI : F.Faithful := geometricCharacterFunctor_faithful K
  have haGal (σ : Gal(K/k)) (x : GeometricCharacters K A) :
      a ((geometricAction K A σ).asHom x) = (geometricAction K B σ).asHom (a x) := by
    apply GroupLike.val_injective
    exact (LinearAlgebraicGroups.SmoothnessAndIsogenies.characterPullbackEquivariant
      (K := K) f hAm hBm σ x _ rfl).symm
  let b' : F.obj B' ⟶ F.obj A' := ObjectProperty.homMk
    { hom := CommGrpCat.ofHom b
      comm σ := by
        apply CommGrpCat.ext
        intro x
        change GeometricCharacters K B at x
        change b ((geometricAction K B σ).asHom x) = (geometricAction K A σ).asHom (b x)
        apply ha
        rw [hab, haGal, hab, map_pow] }
  let g' := F.preimage b'
  let g : B ⟶ A := g'.hom.hom
  have hg (x : GeometricCharacters K B) : pullbackCharacter K g x = b x :=
    congrArg (fun t : F.obj B' ⟶ F.obj A' ↦ t.hom.hom.hom x) (F.map_preimage b')
  have heq : f ≫ g = z n := by
    let f' : A' ⟶ B' := ObjectProperty.homMk (InducedCategory.homMk f)
    let z' : A' ⟶ A' := ObjectProperty.homMk (InducedCategory.homMk (z n))
    have hfg : f' ≫ g' = z' := by
      apply F.map_injective
      apply ObjectProperty.hom_ext
      apply Action.hom_ext
      exact CommGrpCat.ext (fun x ↦ by
        change GeometricCharacters K A at x
        change pullbackCharacter K (f ≫ g) x = pullbackCharacter K (z n) x
        rw [pullbackCharacter_comp, hg, hz]
        exact hba x)
    exact congrArg (fun t : A' ⟶ A' ↦ t.hom.hom) hfg
  exact ⟨n, hn, g, heq⟩

/-- A torus isogeny has a reverse map up to a positive power of the target. -/
private theorem torusIsogenyPowerSection {P Q : AffineAlgebraicGroup k}
    (p : P.val ⟶ Q.val) (hP : IsTorus P.val) (hQ : IsTorus Q.val)
    (hs : Surjective p.hom.hom.left) (N : ClosedSubgroup P.val) (hN : IsSchemeKernel p N)
    (hfin : IsFinite N.group.X.hom) [IsCommMonObj Q.val.X] :
    ∃ (n : ℕ), 0 < n ∧ ∃ s : Q.val ⟶ P.val, s ≫ p = powerHom Q.val n := by
  let K := SeparableClosure k
  let A := Specs.AdjointCocharacters.coordinateHopf Q
  let B := Specs.AdjointCocharacters.coordinateHopf P
  let f := Specs.AdjointCocharacters.coordinateHopfMap (G := P) (H := Q) p
  have hA := coordinatePresentationTorus Q hQ
  have hB := coordinatePresentationTorus P hP
  obtain ⟨J, hJ, hJfin⟩ := coordinatePresentationFiniteKernel (G := P) (H := Q) p N hN hfin
  have hsur := coordinatePresentationSurjective (G := P) (H := Q) p hs
  obtain ⟨hinj, hind⟩ :=
    (LinearAlgebraicGroups.SmoothnessAndIsogenies.torusIsogenyCriterion (K := K) f hA hB).mp
      ⟨hsur, J, hJ, hJfin⟩
  letI := hind
  have hAm := LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType A hA
  have hBm := LinearAlgebraicGroups.CharacterDescent.torusIsMultiplicativeType B hB
  let eP : specGroup B ≅ P.val := Specs.AdjointCocharacters.coordinateHopfIso P
  let eQ : specGroup A ≅ Q.val := Specs.AdjointCocharacters.coordinateHopfIso Q
  letI : IsCommMonObj (specGroup A).X :=
    isCommMonObj_of_groupIso eQ.symm (inferInstanceAs (IsCommMonObj Q.val.X))
  let FF := hopfSpec.fullyFaithful (R := CommRingCat.of k)
  let z (n : ℕ) : A ⟶ A := (FF.preimage (powerHom (specGroup A) n)).unop
  have hz (n : ℕ) : specGroupMap (z n) = powerHom (specGroup A) n := FF.map_preimage _
  obtain ⟨n, hn, g, heq⟩ := geometricReversePower (K := K) f hAm hBm hinj z
    (fun n x ↦ geometricPowerPullback A hAm n (z n) (hz n) x)
  refine ⟨n, hn, eQ.inv ≫ specGroupMap g ≫ eP.hom, ?_⟩
  have hmap : specGroupMap g ≫ specGroupMap f = powerHom (specGroup A) n := by
    rw [← specGroupMap_comp, heq, hz]
  have hf : specGroupMap f ≫ eQ.hom = eP.hom ≫ p := by
    rw [coordinatePresentationMap (G := P) (H := Q) p, Category.assoc, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  calc
    (eQ.inv ≫ specGroupMap g ≫ eP.hom) ≫ p =
        eQ.inv ≫ (specGroupMap g ≫ specGroupMap f) ≫ eQ.hom := by
          simp only [Category.assoc, hf]
    _ = powerHom Q.val n := by
      rw [hmap, powerHom_iso eQ n, Iso.inv_hom_id_assoc]


private theorem adjointQuotientFinite {G Q : AffineAlgebraicGroup k}
    {Z : ClosedSubgroup G.val} {q : G.val ⟶ Q.val}
    (hq : IsAdjointQuotient Z q) (hZ : IsFinite Z.group.X.hom) :
    IsFinite q.hom.hom.left := by
  let q₀ := q.hom.hom.left
  letI : Flat q₀ := hq.2.2.2.1
  letI : Surjective q₀ := hq.2.2.2.2.1
  letI : LocallyOfFinitePresentation q₀ := hq.2.2.2.2.2
  letI : IsAffine G.val.X.left := G.property.1
  letI : IsAffine Q.val.X.left := Q.property.1
  have hp := (quotientKernelPair hq.2.1).map (Over.forget _)
  have hprod := Over.isPullback_of_binaryFan_isLimit _ (prodIsProd G.val.X Z.group.X)
  haveI : IsFinite (prod.fst : G.val.X ⨯ Z.group.X ⟶ G.val.X).left :=
    MorphismProperty.of_isPullback hprod.flip hZ
  have hcover : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) q₀ :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hclosedProd : UniversallyClosed (prod.fst : G.val.X ⨯ Z.group.X ⟶ G.val.X).left := inferInstance
  have hclosed : UniversallyClosed q₀ :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed)
      hp hcover hclosedProd
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hclosed, inferInstance⟩,
      inferInstance⟩

private theorem finiteRestriction {G Q : AffineAlgebraicGroup k}
    {q : G.val ⟶ Q.val} (hq : IsFinite q.hom.hom.left)
    (S : ClosedSubgroup G.val) (T : ClosedSubgroup Q.val) (p : S.group ⟶ T.group)
    (hp : S.inclusion ≫ q = p ≫ T.inclusion) : IsFinite p.hom.hom.left := by
  letI := hq
  letI := S.isClosedImmersion
  letI := T.isClosedImmersion
  haveI : IsFinite (p.hom.hom.left ≫ T.inclusion.hom.hom.left) := by
    change IsFinite (p ≫ T.inclusion).hom.hom.left
    rw [← hp]
    change IsFinite (S.inclusion.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  exact IsFinite.of_comp _ T.inclusion.hom.hom.left

private theorem finiteRestrictionDimension {G Q : AffineAlgebraicGroup k}
    {q : G.val ⟶ Q.val} (hq : IsFinite q.hom.hom.left)
    (S : ClosedSubgroup G.val) (T : ClosedSubgroup Q.val) (p : S.group ⟶ T.group)
    (hp : S.inclusion ≫ q = p ≫ T.inclusion) (hs : Surjective p.hom.hom.left) :
    topologicalKrullDim S.group.X.left = topologicalKrullDim T.group.X.left := by
  letI : IsAffine S.group.X.left := (closedSubgroupAlgebraicGroup S).property.1
  letI : IsAffine T.group.X.left := (closedSubgroupAlgebraicGroup T).property.1
  letI := finiteRestriction hq S T p hp
  letI := hs
  exact scheme_dimension_eq_of_finite_surjective p.hom.hom.left

private theorem powerNaturality {S T : GroupScheme k} [IsCommMonObj S.X] [IsCommMonObj T.X]
    (f : S ⟶ T) (n : ℕ) : f ≫ powerHom T n = powerHom S n ≫ f := by
  apply Grp.hom_ext
  change f.hom.hom ≫ (powerHom T n).hom.hom = (powerHom S n).hom.hom ≫ f.hom.hom
  rw [powerHom_onSections]
  simp only [powerHom, Grp.Hom.hom_pow, Mon.Hom.hom_pow]
  rw [MonObj.pow_comp]
  change f.hom.hom ^ n = ((𝟙 S.X) ≫ f.hom.hom) ^ n
  rw [Category.id_comp]

private theorem splitTorusLiftsOfPowerSection
    {G Q : AffineAlgebraicGroup k} {q : G.val ⟶ Q.val}
    (S : ClosedSubgroup Q.val) (hS : IsSplitTorus S.group)
    (n : ℕ) (hn : 0 < n) (l : S.group ⟶ G.val) [IsCommMonObj S.group.X]
    (hl : l ≫ q = powerHom S.group n ≫ S.inclusion) :
    ∃ (T : ClosedSubgroup G.val) (f : T.group ⟶ S.group), IsSplitTorus T.group ∧
      T.inclusion ≫ q = f ≫ S.inclusion ∧ Surjective f.hom.hom.left := by
  obtain ⟨P, r, hP⟩ := preimageSubgroup q S
  let a := hP.lift l (powerHom S.group n) hl
  let A := closedSubgroupAlgebraicGroup S
  let B := closedSubgroupAlgebraicGroup P
  obtain ⟨I, t, hI, ht⟩ := splitTorusImage A B hS a
  letI := I.isClosedImmersion
  letI := P.isClosedImmersion
  letI : IsCommMonObj A.val.X := inferInstanceAs (IsCommMonObj S.group.X)
  let T : ClosedSubgroup G.val := ⟨I.group, I.inclusion ≫ P.inclusion,
    IsClosedImmersion.comp I.inclusion.hom.hom.left P.inclusion.hom.hom.left⟩
  let f := I.inclusion ≫ r
  have hcomp : t ≫ f = powerHom S.group n := by
    rw [← Category.assoc, ht.1, IsPullback.lift_snd]
  have hsur : Surjective (t.hom.hom.left ≫ f.hom.hom.left) := by
    change Surjective (t ≫ f).hom.hom.left
    rw [hcomp]
    exact (torus_power_flat_surjective A (isTorus_of_split hS) n hn.ne').2
  refine ⟨T, f, hI, ?_, Surjective.of_comp t.hom.hom.left _⟩
  change (I.inclusion ≫ P.inclusion) ≫ q = (I.inclusion ≫ r) ≫ S.inclusion
  rw [Category.assoc, hP.w, Category.assoc]

/-- The adjoint quotient of a connected semisimple group preserves
the supremum of the dimensions of closed split tori over the ground field. -/
theorem semisimpleAdjointRank : Specs.RelativeRank.SemisimpleAdjointRank.{u} := by
  intro k _ G Q Z q hss hq
  have hG := reductive_of_semisimple G hss
  have hFinZ := (LinearAlgebraicGroups.Reductive.CentralDerived.semisimpleIffFiniteCentre
    G hG Z hq.1).mp hss
  have hFin := adjointQuotientFinite hq hFinZ
  have hQ := reductive_of_central_quotient hG hq.2.1 hq.1 hq.2.2.2.1
    hq.2.2.2.2.1 hq.2.2.2.2.2
  apply le_antisymm
  · change (⨆ S : {S : ClosedSubgroup G.val // IsSplitTorus S.group},
      topologicalKrullDim S.val.group.X.left) ≤ _
    apply iSup_le
    rintro ⟨S, hS⟩
    obtain ⟨T, p, hT, hp⟩ := splitTorusImage (closedSubgroupAlgebraicGroup S) Q hS (S.inclusion ≫ q)
    rw [finiteRestrictionDimension hFin S T p hp.1.symm hp.2.2.1]
    exact split_dimension_le_rank Q T hT
  · change (⨆ S : {S : ClosedSubgroup Q.val // IsSplitTorus S.group},
      topologicalKrullDim S.val.group.X.left) ≤ _
    apply iSup_le
    rintro ⟨S, hS⟩
    obtain ⟨T', ht', hm', ⟨j, hj⟩⟩ := torusInMaximalTorus hQ.1
      (connected_of_geometricallyConnected hQ.2.1) S (isTorus_of_split hS)
    obtain ⟨T, p, hp⟩ := LinearAlgebraicGroups.Descent.AdjointCocharacters.maximalTorusPreimage
      Z q hG hq T' ht' hm'
    obtain ⟨z, hz, _, hker⟩ := kernel_of_preimage hq.2.1
      (IsPullback.of_map_of_faithful (Grp.forget (SchemeOver k)) hp.1)
    letI : IsCommMonObj (closedSubgroupAlgebraicGroup T').val.X :=
      torus_commutative (closedSubgroupAlgebraicGroup T') ht'
    letI : IsCommMonObj T'.group.X := inferInstanceAs (IsCommMonObj (closedSubgroupAlgebraicGroup T').val.X)
    letI : IsCommMonObj S.group.X := torus_commutative (closedSubgroupAlgebraicGroup S) (isTorus_of_split hS)
    obtain ⟨n, hn, s, hs⟩ := torusIsogenyPowerSection
      (P := closedSubgroupAlgebraicGroup T) (Q := closedSubgroupAlgebraicGroup T')
      p hp.2.1.1 ht' hp.2.2.2.2
      ⟨Z.group, z, hz⟩ hker hFinZ
    have hs' : s ≫ p = powerHom T'.group n := hs
    have htw : T.inclusion ≫ q = p ≫ T'.inclusion := Grp.hom_ext _ _ hp.1.w
    let l := j ≫ s ≫ T.inclusion
    have hl : l ≫ q = powerHom S.group n ≫ S.inclusion := by
      calc
        l ≫ q = (j ≫ (s ≫ p)) ≫ T'.inclusion := by simp only [l, Category.assoc, htw]
        _ = _ := by rw [hs', powerNaturality j n, Category.assoc, hj]
    obtain ⟨V, f, hV, hf, hsur⟩ := splitTorusLiftsOfPowerSection S hS n hn l hl
    rw [← finiteRestrictionDimension hFin V S f hf hsur]
    exact split_dimension_le_rank G V hV

end

end LinearAlgebraicGroups.Descent.RelativeRank
