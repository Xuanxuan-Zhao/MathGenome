import Specs.LinearAlgebraicGroups.Reductive.CentralTorus
import Specs.LinearAlgebraicGroups.Reductive.MaximalToriExist
import Specs.LinearAlgebraicGroups.Reductive.TorusCentralizer
import LinearAlgebraicGroups.Affine.Stabilizers
import LinearAlgebraicGroups.Multiplicative.CharacterDescent
import LinearAlgebraicGroups.Affine.FaithfulLinearization
import LinearAlgebraicGroups.Multiplicative.WeightDecomposition
import LinearAlgebraicGroups.Reductive.DerivedSubgroup
import LinearAlgebraicGroups.Unipotent.ExactOperations
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Batteries.Tactic.OpenPrivate

import LinearAlgebraicGroups.Reductive.MaximalToriExist
import LinearAlgebraicGroups.Reductive.TorusCentralizer
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Coalgebra
open scoped TensorProduct MonoidAlgebra Topology
open Topology
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u

namespace LinearAlgebraicGroups.CentralTorus

open LinearAlgebraicGroups.Specs LinearAlgebraicGroups.Specs.CentralTorus
open Specs.CharacterDescent (GeometricCharacters IsMultiplicativeType IsDiagonalizable
  MultiplicativeTypeHopf CharacterModule StandardLattice)
open CharacterDescent (extendedHopfFunctor extendedHopfTower monomialCharacterEquiv mapGroupLike
  geometricCharacterFunctor baseChangeCharacterMap)
open Specs.GeometricRadicals (IsReductive IsTorus IsSplitTorus baseChangedSubgroup)
open Specs.DiagonalizableGroups (FGAbelianGroup groupAlgebra diagonalClosedInclusion diagonalGroup)
open Specs.SchemeDerivedGroup (IsDerivedSubgroup IsSubgroupOf)

open private centralizes_iff from LinearAlgebraicGroups.Affine.Stabilizers
open private isMonHom_of_comp_closed from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private extendedGroupIso extendedSpecIso_natural specGroupMap_comp from LinearAlgebraicGroups.Affine.ClosedSubgroups
open private groupLikeSpanOfSplit groupLikeIso splitBaseChange geometricCharacterFunctor_full
  geometricCharacterFunctor_faithful geometricCharacterFunctor_essSurj
  from LinearAlgebraicGroups.Multiplicative.CharacterDescent

noncomputable section

set_option maxHeartbeats 1200000
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k] {G : GroupScheme k}

local instance underlying_isIso {H J : GroupScheme k} (f : H ⟶ J) [IsIso f] :
    IsIso f.hom.hom.left :=
  (Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))).map_isIso f


private theorem centre_le_of_selfCentralizer {Z T : ClosedSubgroup G}
    (hZ : IsSchemeCentre Z) (hT : SubtorusCentralizer.IsCentralizer T T) :
    IsSubgroupOf Z T := by
  have hc : Centralizes (𝟙 G) Z.inclusion.hom.hom :=
    (hZ Z.group.X Z.inclusion.hom.hom).mpr ⟨𝟙 _, Category.id_comp _⟩
  have hx : Centralizes T.inclusion Z.inclusion.hom.hom := by
    rw [centralizes_iff] at hc ⊢
    intro U t h
    simpa using hc U t (h ≫ T.inclusion.hom.hom)
  obtain ⟨j, hj⟩ := (hT Z.group.X Z.inclusion.hom.hom).mp hx
  letI := T.isClosedImmersion
  letI := isMonHom_of_comp_closed j Z.inclusion T.inclusion hj
  exact ⟨Grp.homMk j, Grp.hom_ext _ _ hj⟩

private theorem centre_splits
    (existsT : Specs.MaximalToriExist.GeometricallyMaximalTorusExists.{u})
    (selfCentralizing : Specs.TorusCentralizer.MaximalTorusCentralizer.{u})
    (G : AffineAlgebraicGroup k) (hG : IsReductive G)
    (Z : ClosedSubgroup G.val) (hZ : IsSchemeCentre Z) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra k E) (_ : Algebra.IsSeparable k E)
      (M : FGAbelianGroup.{u}),
      Nonempty ((groupBaseChange k E).obj Z.group ≅ specGroup (groupAlgebra E M.obj)) := by
  letI := hG.2.1
  have hconn : ConnectedSpace G.val.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton G.val.X.hom
  obtain ⟨T, ht, hmax⟩ := existsT G hG.1 hconn
  obtain ⟨j, hj⟩ := centre_le_of_selfCentralizer hZ (selfCentralizing G hG T ht hmax)
  letI := T.isClosedImmersion
  have hjc : IsClosedImmersion j.hom.hom.left := by
    have hcomp : IsClosedImmersion (j ≫ T.inclusion).hom.hom.left := by rw [hj]; exact Z.isClosedImmersion
    exact @IsClosedImmersion.of_comp_isClosedImmersion _ _ _ j.hom.hom.left
      T.inclusion.hom.hom.left T.isClosedImmersion hcomp
  obtain ⟨E, _, _, hsep, r, ⟨e⟩⟩ := ht
  let M := Multiplicative (ULift.{u} (Fin r) → ℤ)
  obtain ⟨d⟩ := DiagonalizableGroups.diagonalIntegerPowers E (ULift.{u} (Fin r))
  let i := (groupBaseChange k E).map j ≫ e.hom ≫ d.inv
  haveI := baseChangeClosedSubgroup k E j hjc
  let F := Grp.forget (SchemeOver E) ⋙ Over.forget (Spec (CommRingCat.of E))
  have : IsIso e.hom.hom.hom.left := F.map_isIso e.hom
  have : IsIso d.inv.hom.hom.left := F.map_isIso d.inv
  have hi : IsClosedImmersion i.hom.hom.left := by
    change IsClosedImmersion
      (((groupBaseChange k E).map j).hom.hom.left ≫ e.hom.hom.hom.left ≫ d.inv.hom.hom.left)
    infer_instance
  obtain ⟨N, ⟨f, _⟩, _⟩ :=
    (DiagonalizableGroups.diagonalClosedSubgroups E M _ i).mp hi
  exact ⟨E, inferInstance, inferInstance, hsep, ⟨CommGrpCat.of (M ⧸ N), inferInstance⟩, ⟨f⟩⟩

theorem centreMultiplicativeType_conditional :
    Specs.MaximalToriExist.GeometricallyMaximalTorusExists.{u} →
    Specs.TorusCentralizer.MaximalTorusCentralizer.{u} →
    CentreMultiplicativeType.{u} := by
  intro existsT selfCentralizing k _ G hG
  let whole : ClosedSubgroup G.val :=
    ⟨G.val, 𝟙 G.val, by change IsClosedImmersion (𝟙 G.val.X.left); infer_instance⟩
  obtain ⟨Z, hZ⟩ := centralizerScheme k G whole
  exact ⟨Z, hZ, centre_splits existsT selfCentralizing G hG Z hZ⟩

/-- A finite rank torsion-free character group is a split torus lattice. -/
private theorem freeCharacterLattice (M : Type u) [CommGroup M] [Group.FG M]
    [IsMulTorsionFree M] : ∃ r : ℕ, Nonempty (M ≃* StandardLattice.{u} r) := by
  letI : Module.Finite ℤ (Additive M) :=
    Module.Finite.iff_addGroup_fg.mpr inferInstance
  letI : Module.IsTorsionFree ℤ (Additive M) := ⟨fun n hn ↦ by
    intro a b eq
    apply sub_eq_zero.mp
    apply (IsAddTorsionFree.zsmul_eq_zero_iff_right (isRegular_iff_ne_zero.mp hn)).mp
    rw [smul_sub]
    change n • a = n • b at eq
    rw [eq, sub_self]⟩
  letI : Module.Free ℤ (Additive M) := inferInstance
  let r := Module.finrank ℤ (Additive M)
  let b := Module.Free.chooseBasis ℤ (Additive M)
  let e := b.equivFun.toAddEquiv
  let i : Module.Free.ChooseBasisIndex ℤ (Additive M) ≃ Fin r :=
    Fintype.equivFinOfCardEq (Module.finrank_eq_card_basis b).symm
  let j : ((Module.Free.ChooseBasisIndex ℤ (Additive M)) → ℤ) ≃+
      (Fin r → ℤ) :=
    { toEquiv := Equiv.arrowCongr i (Equiv.refl ℤ)
      map_add' := fun _ _ ↦ rfl }
  let a : Multiplicative (Fin r → ℤ) ≃* StandardLattice.{u} r :=
    { toFun := fun x i ↦ ⟨Multiplicative.ofAdd (x.toAdd i)⟩
      invFun := fun x ↦ Multiplicative.ofAdd (fun i ↦ (x i).down.toAdd)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl }
  exact ⟨r, ⟨(e.trans j).toMultiplicative.trans a⟩⟩

private def geometricPullback (K : Type u) [Field K] [Algebra k K]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    GeometricCharacters K A →* GeometricCharacters K B :=
  mapGroupLike (extendedHopfMap K f)

private theorem surjective_of_geometricPullback {A B : HopfAlgebraCategory k}
    (K : Type u) [Field K] [Algebra k K] (f : A ⟶ B)
    (hB : IsDiagonalizable (extendedHopf K B))
    (hf : Function.Surjective (geometricPullback K f)) : Function.Surjective f.hom := by
  change Function.Surjective f.hom.toAlgHom.toLinearMap
  apply (Module.FaithfullyFlat.lTensor_surjective_iff_surjective k K _).mp
  change Function.Surjective (extendedHopfMap K f).hom.toAlgHom.toLinearMap
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← groupLikeSpanOfSplit _ hB]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hf x
  exact ⟨y.val, congrArg GroupLike.val hy⟩

private def quotientCharacterModule {K : Type u} [Field K] [Algebra k K]
    (M : CharacterModule k K) : CharacterModule k K := by
  let N := CommGroup.torsion M.obj.V
  letI := M.property.1
  let Q : Action CommGrpCat.{u} Gal(K/k) := ⟨CommGrpCat.of (M.obj.V ⧸ N),
    { toFun := fun σ ↦ End.of <| CommGrpCat.ofHom <| QuotientGroup.map N N
        (M.obj.ρ σ).asHom.hom (CommGroup.le_comap_torsion _)
      map_one' := by
        apply End.ext
        apply CommGrpCat.ext
        intro x
        induction x using QuotientGroup.induction_on with
        | _ x =>
          change QuotientGroup.mk' N ((M.obj.ρ 1).asHom x) = QuotientGroup.mk' N x
          rw [map_one]
          rfl
      map_mul' := by
        intro σ τ
        apply End.ext
        apply CommGrpCat.ext
        intro x
        induction x using QuotientGroup.induction_on with
        | _ x =>
          change QuotientGroup.mk' N ((M.obj.ρ (σ * τ)).asHom x) =
            QuotientGroup.mk' N ((M.obj.ρ σ).asHom ((M.obj.ρ τ).asHom x))
          rw [map_mul]
          rfl }⟩
  refine ⟨Q, inferInstance, fun x ↦ ?_⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N x
  let y := QuotientGroup.mk' N m
  let H : Subgroup Gal(K/k) :=
    { carrier := {σ | (Q.ρ σ).asHom y = y}
      one_mem' := by simp
      mul_mem' := fun {σ τ} hσ hτ ↦ by
        change (Q.ρ (σ * τ)).asHom y = y
        rw [map_mul]
        change (Q.ρ σ).asHom ((Q.ρ τ).asHom y) = y
        rw [show (Q.ρ τ).asHom y = y from hτ]
        exact hσ
      inv_mem' := fun {σ} hσ ↦ by
        change (Q.ρ σ⁻¹).asHom y = y
        have he : Q.ρ (σ⁻¹ * σ) = 1 := by simp
        have he' := congrArg (fun f : End Q.V ↦ f.asHom y) he
        rw [map_mul] at he'
        change (Q.ρ σ⁻¹).asHom ((Q.ρ σ).asHom y) = y at he'
        rwa [show (Q.ρ σ).asHom y = y from hσ] at he'  }
  apply H.isOpen_of_mem_nhds (g := 1)
  apply Filter.mem_of_superset ((M.property.2 m).mem_nhds ?_)
  · intro σ hσ
    change QuotientGroup.mk' N ((M.obj.ρ σ).asHom m) = QuotientGroup.mk' N m
    exact congrArg (QuotientGroup.mk' N) hσ
  · change (M.obj.ρ 1).asHom m = m
    rw [map_one]
    rfl

private def quotientCharacters {K : Type u} [Field K] [Algebra k K]
    (M : CharacterModule k K) : M ⟶ quotientCharacterModule M :=
  ObjectProperty.homMk
    { hom := CommGrpCat.ofHom (QuotientGroup.mk' (CommGroup.torsion M.obj.V))
      comm := by intro σ; apply CommGrpCat.ext; intro x; rfl }

private theorem torus_of_torsionFreeCharacters (K : Type u) [Field K] [Algebra k K]
    [IsSepClosure k K] (B : MultiplicativeTypeHopf k)
    [IsMulTorsionFree (GeometricCharacters K B.obj.val)] :
    Specs.CharacterDescent.IsTorus B.obj.val := by
  let F := geometricCharacterFunctor (k := k) K
  letI : Group.FG (GeometricCharacters K B.obj.val) := (F.obj B).property.1
  exact ((CharacterDescent.torusAndSplitCriteria B.obj.val B.property).1).2
    (freeCharacterLattice (GeometricCharacters K B.obj.val))

private theorem exists_torus_quotient (K : Type u) [Field K] [Algebra k K] [IsSepClosure k K]
    (A : MultiplicativeTypeHopf k) :
    ∃ (B : MultiplicativeTypeHopf k) (f : A.obj.val ⟶ B.obj.val),
      Function.Surjective (geometricPullback K f) ∧
      (geometricPullback K f).ker = CommGroup.torsion (GeometricCharacters K A.obj.val) := by
  let F := geometricCharacterFunctor (k := k) K
  letI : F.Full := geometricCharacterFunctor_full K
  letI : F.EssSurj := geometricCharacterFunctor_essSurj K
  let Q := quotientCharacterModule (F.obj A)
  let B := F.objPreimage Q
  let e := F.objObjPreimageIso Q
  let p := quotientCharacters (F.obj A)
  let f := F.preimage (p ≫ e.inv)
  have hf : F.map f = p ≫ e.inv := F.map_preimage _
  let i : (F.obj B).obj.V ≃* Q.obj.V :=
    ((Action.forget _ _).mapIso ((ObjectProperty.ι _).mapIso e)).commGroupIsoToMulEquiv
  have eq (x : GeometricCharacters K A.obj.val) :
      geometricPullback K f.hom.hom x =
        i.symm (QuotientGroup.mk' (CommGroup.torsion _) x) := by
    exact congrArg (fun g : F.obj A ⟶ F.obj B ↦ g.hom.hom.hom x) hf
  refine ⟨B, f.hom.hom, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion _) (i y)
    exact ⟨x, by rw [eq, hx, i.symm_apply_apply]⟩
  · ext x
    change geometricPullback K f.hom.hom x = 1 ↔ _
    rw [eq, ← i.symm.map_one, i.symm.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x

private theorem geometric_torus_of_quotient (K : Type u) [Field K] [Algebra k K]
    [IsSepClosure k K] {A B : MultiplicativeTypeHopf k} (f : A.obj.val ⟶ B.obj.val)
    (hs : Function.Surjective (geometricPullback K f))
    (hk : (geometricPullback K f).ker = CommGroup.torsion _) :
    Specs.CharacterDescent.IsTorus B.obj.val := by
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (geometricPullback K f) hs)
  letI := Function.Injective.isMulTorsionFree e.symm.toMonoidHom e.symm.injective
  exact torus_of_torsionFreeCharacters K B

private theorem torus_quotient_factors (K : Type u) [Field K] [Algebra k K] [IsSepClosure k K]
    {A B C : MultiplicativeTypeHopf k} (f : A.obj.val ⟶ B.obj.val) (g : A.obj.val ⟶ C.obj.val)
    (hs : Function.Surjective (geometricPullback K f))
    (hk : (geometricPullback K f).ker = CommGroup.torsion _)
    (hC : Specs.CharacterDescent.IsTorus C.obj.val) :
    ∃ j : B.obj.val ⟶ C.obj.val, f ≫ j = g := by
  let F := geometricCharacterFunctor (k := k) K
  letI : F.Full := geometricCharacterFunctor_full K
  letI : F.Faithful := geometricCharacterFunctor_faithful K
  let f' : A ⟶ B := ObjectProperty.homMk (InducedCategory.homMk f)
  let g' : A ⟶ C := ObjectProperty.homMk (InducedCategory.homMk g)
  obtain ⟨r, ⟨eC⟩⟩ := ((CharacterDescent.torusAndSplitCriteria (K := K) C.obj.val C.property).1).1 hC
  let i : ULift.{u} (Multiplicative ℤ) ≃* Multiplicative ℤ := MulEquiv.ulift
  letI : IsMulTorsionFree (ULift.{u} (Multiplicative ℤ)) :=
    Function.Injective.isMulTorsionFree i.toMonoidHom i.injective
  letI : IsMulTorsionFree (StandardLattice.{u} r) := by
    change IsMulTorsionFree (Fin r → ULift.{u} (Multiplicative ℤ))
    infer_instance
  letI := Function.Injective.isMulTorsionFree eC.toMonoidHom eC.injective
  let a := geometricPullback K f
  let b := geometricPullback K g
  let e := QuotientGroup.quotientKerEquivOfSurjective (geometricPullback K f) hs
  have hle : a.ker ≤ b.ker := by
    intro x hx
    have hx' : x ∈ (geometricPullback K f).ker := hx
    rw [hk] at hx'
    have ht : IsOfFinOrder x := hx'
    exact (b.isOfFinOrder ht).eq_one'
  let v : GeometricCharacters K B.obj.val →* GeometricCharacters K C.obj.val :=
    (QuotientGroup.lift a.ker b hle).comp e.symm.toMonoidHom
  have hv (x : GeometricCharacters K A.obj.val) : v (a x) = b x := by
    change QuotientGroup.lift _ b hle (e.symm (e (QuotientGroup.mk' a.ker x))) = _
    rw [e.symm_apply_apply]
    rfl
  let d : F.obj B ⟶ F.obj C := ObjectProperty.homMk
    { hom := CommGrpCat.ofHom v
      comm := by
        intro σ
        apply CommGrpCat.ext
        intro y
        obtain ⟨x, rfl⟩ := hs y
        have ha := DFunLike.congr_fun (congrArg CommGrpCat.Hom.hom
          ((F.map f').hom.comm σ)) x
        have hb := DFunLike.congr_fun (congrArg CommGrpCat.Hom.hom
          ((F.map g').hom.comm σ)) x
        change a ((((F.obj A).obj.ρ σ).asHom) x) = ((F.obj B).obj.ρ σ).asHom (a x) at ha
        change b ((((F.obj A).obj.ρ σ).asHom) x) = ((F.obj C).obj.ρ σ).asHom (b x) at hb
        change v (((F.obj B).obj.ρ σ).asHom (a x)) = ((F.obj C).obj.ρ σ).asHom (v (a x))
        rw [← ha, hv, hv, hb] }
  let j := F.preimage d
  have h : f' ≫ j = g' := by
    apply F.map_injective
    rw [F.map_comp, F.map_preimage]
    apply ObjectProperty.hom_ext
    apply Action.hom_ext
    apply CommGrpCat.ext
    exact hv
  exact ⟨j.hom.hom, congrArg (fun m : A ⟶ C ↦ m.hom.hom) h⟩

private def hopfPreimage {A B : HopfAlgebraCategory k} (f : specGroup B ⟶ specGroup A) :
    A ⟶ B := ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimage f).unop

private theorem specGroupMap_hopfPreimage {A B : HopfAlgebraCategory k}
    (f : specGroup B ⟶ specGroup A) : specGroupMap (hopfPreimage f) = f :=
  (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage f

private theorem torus_iso {S T : GroupScheme k} (e : S ≅ T) (hT : IsTorus T) : IsTorus S := by
  obtain ⟨E, _, _, _, r, ⟨a⟩⟩ := hT
  exact ⟨E, inferInstance, inferInstance, inferInstance, r,
    ⟨(groupBaseChange k E).mapIso e ≪≫ a⟩⟩

private theorem isLargest_of_torus_quotient (K : Type u) [Field K] [Algebra k K] [IsSepClosure k K]
    {A B : MultiplicativeTypeHopf k} (f : A.obj.val ⟶ B.obj.val)
    (hs : Function.Surjective (geometricPullback K f))
    (hk : (geometricPullback K f).ker = CommGroup.torsion _)
    {Z : GroupScheme k} (e : specGroup A.obj.val ≅ Z)
    (h : IsClosedImmersion (specGroupMap f ≫ e.hom).hom.hom.left) :
    IsLargestTorus (⟨_, specGroupMap f ≫ e.hom, h⟩ : ClosedSubgroup Z) := by
  have ht : Specs.CharacterDescent.IsTorus B.obj.val := geometric_torus_of_quotient K f hs hk
  refine ⟨(CharacterDescent.torusOnSchemes B.obj.val).mp ht, ?_⟩
  intro S hS
  haveI : IsAffine Z.X.left := by
    let d := (Grp.forget (SchemeOver k)).mapIso e
    have : IsIso d.inv.left := (Over.forget _).map_isIso d.inv
    have : IsAffine (specGroup A.obj.val).X.left := by
      change IsAffine (Spec (CommRingCat.of A.obj.val))
      infer_instance
    change IsAffine Z.X.left
    exact @isAffine_of_isAffineHom Z.X.left (specGroup A.obj.val).X.left
      d.inv.left inferInstance ‹IsAffine (specGroup A.obj.val).X.left›
  letI := S.isClosedImmersion
  let S' : AffineGroupCategory k :=
    ⟨S.group, isAffine_of_isAffineHom S.inclusion.hom.hom.left⟩
  let C := coordinateHopf S'
  let d : specGroup C ≅ S.group := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso S')
  have hC : Specs.CharacterDescent.IsTorus C :=
    (CharacterDescent.torusOnSchemes C).mpr (torus_iso d hS)
  have hCmt := CharacterDescent.torusIsMultiplicativeType C hC
  let C' : MultiplicativeTypeHopf k :=
    ⟨⟨C, (CharacterDescent.multiplicativeTypeProperties C hCmt).1⟩, hCmt⟩
  let g : A.obj.val ⟶ C'.obj.val := hopfPreimage (d.hom ≫ S.inclusion ≫ e.inv)
  obtain ⟨j, hj⟩ := torus_quotient_factors K f (C := C') g hs hk hC
  refine ⟨d.inv ≫ specGroupMap j, ?_⟩
  change (d.inv ≫ specGroupMap j) ≫ specGroupMap f ≫ e.hom = S.inclusion
  rw [Category.assoc, ← Category.assoc (specGroupMap j), ← specGroupMap_comp, hj]
  change d.inv ≫ specGroupMap (hopfPreimage (d.hom ≫ S.inclusion ≫ e.inv)) ≫ e.hom = _
  rw [specGroupMap_hopfPreimage]
  simp

private theorem extendedGroupIso_natural (L : Type u) [Field L] [Algebra k L]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B) :
    specGroupMap (extendedHopfMap L f) ≫ (extendedGroupIso L A).hom =
      (extendedGroupIso L B).hom ≫ (groupBaseChange k L).map (specGroupMap f) :=
  Grp.hom_ext _ _ (extendedSpecIso_natural L f)

private def geometricBaseChangeEquiv {K L S : Type u} [Field K] [Field L] [Field S]
    [Algebra k K] [Algebra k L] [Algebra k S] [Algebra K S] [Algebra L S]
    [IsScalarTower k K S] [IsScalarTower k L S]
    (A : HopfAlgebraCategory k) (h : IsDiagonalizable (extendedHopf K A)) :
    GeometricCharacters K A ≃* GeometricCharacters S (extendedHopf L A) :=
  ((MulEquiv.ofBijective (baseChangeCharacterMap S (extendedHopf K A))
      (CharacterDescent.baseChangeCharacterMap_bijective S _ h)).trans
    (groupLikeIso (extendedHopfTower (K := K) S A))).trans
      (groupLikeIso (extendedHopfTower (K := L) S A).symm)

private theorem geometricBaseChangeEquiv_natural {K L S : Type u} [Field K] [Field L] [Field S]
    [Algebra k K] [Algebra k L] [Algebra k S] [Algebra K S] [Algebra L S]
    [IsScalarTower k K S] [IsScalarTower k L S]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B)
    (hA : IsDiagonalizable (extendedHopf K A)) (hB : IsDiagonalizable (extendedHopf K B))
    (x : GeometricCharacters K A) :
    geometricBaseChangeEquiv (L := L) (S := S) B hB (geometricPullback K f x) =
      geometricPullback S (extendedHopfMap L f) (geometricBaseChangeEquiv A hA x) := by
  apply GroupLike.val_injective
  change (extendedHopfTower (K := L) S B).inv.hom
      ((extendedHopfTower (K := K) S B).hom.hom
        ((1 : S) ⊗ₜ[K] ((extendedHopfMap K f).hom x.val))) =
    (extendedHopfMap S (extendedHopfMap L f)).hom
      ((extendedHopfTower (K := L) S A).inv.hom
        ((extendedHopfTower (K := K) S A).hom.hom ((1 : S) ⊗ₜ[K] x.val)))
  have natural (P : Type u) [Field P] [Algebra k P] [Algebra P S] [IsScalarTower k P S]
      (y : S ⊗[P] (P ⊗[k] A)) :
      (extendedHopfTower (K := P) S B).hom.hom ((extendedHopfMap S (extendedHopfMap P f)).hom y) =
        (extendedHopfMap S f).hom ((extendedHopfTower (K := P) S A).hom.hom y) := by
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul r y =>
      induction y using TensorProduct.inductionOn with
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
      | tmul s a => rfl
  apply (CommHopfAlgCat.ofIso (extendedHopfTower (K := L) S B)).injective
  change (extendedHopfTower (K := L) S B).hom.hom _ =
    (extendedHopfTower (K := L) S B).hom.hom _
  rw [CommHopfAlgCat.hom_inv_apply, natural L, CommHopfAlgCat.hom_inv_apply]
  exact natural K ((1 : S) ⊗ₜ[K] x.val)

private theorem quotient_after_scalar_extension {K L S : Type u} [Field K] [Field L] [Field S]
    [Algebra k K] [Algebra k L] [Algebra k S] [Algebra K S] [Algebra L S]
    [IsScalarTower k K S] [IsScalarTower k L S]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B)
    (hA : IsDiagonalizable (extendedHopf K A)) (hB : IsDiagonalizable (extendedHopf K B))
    (hs : Function.Surjective (geometricPullback K f))
    (hk : (geometricPullback K f).ker = CommGroup.torsion _) :
    Function.Surjective (geometricPullback S (extendedHopfMap L f)) ∧
    (geometricPullback S (extendedHopfMap L f)).ker = CommGroup.torsion _ := by
  let a := geometricBaseChangeEquiv (L := L) (S := S) A hA
  let b := geometricBaseChangeEquiv (L := L) (S := S) B hB
  have he (x : GeometricCharacters K A) :
      b (geometricPullback K f x) = geometricPullback S (extendedHopfMap L f) (a x) :=
    geometricBaseChangeEquiv_natural f hA hB x
  constructor
  · intro y
    obtain ⟨z, rfl⟩ := b.surjective y
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨a x, (he x).symm⟩
  · ext y
    obtain ⟨x, rfl⟩ := a.surjective y
    change geometricPullback S (extendedHopfMap L f) (a x) = 1 ↔
      a x ∈ CommGroup.torsion _
    rw [← he, ← b.map_one, b.injective.eq_iff]
    change x ∈ (geometricPullback K f).ker ↔
      x ∈ (CommGroup.torsion _).comap a.toMonoidHom
    rw [hk]
    exact (a.injective.isOfFinOrder_iff).symm

private theorem quotient_between_splitting_fields {K S : Type u} [Field K] [Field S]
    [Algebra k K] [Algebra k S] [Algebra K S] [IsScalarTower k K S]
    {A B : HopfAlgebraCategory k} (f : A ⟶ B)
    (hA : IsDiagonalizable (extendedHopf K A)) (hB : IsDiagonalizable (extendedHopf K B))
    (hs : Function.Surjective (geometricPullback K f))
    (hk : (geometricPullback K f).ker = CommGroup.torsion _) :
    Function.Surjective (geometricPullback S f) ∧
    (geometricPullback S f).ker = CommGroup.torsion _ := by
  let a := (MulEquiv.ofBijective (baseChangeCharacterMap S (extendedHopf K A))
    (CharacterDescent.baseChangeCharacterMap_bijective S _ hA)).trans
      (groupLikeIso (extendedHopfTower (K := K) S A))
  let b := (MulEquiv.ofBijective (baseChangeCharacterMap S (extendedHopf K B))
    (CharacterDescent.baseChangeCharacterMap_bijective S _ hB)).trans
      (groupLikeIso (extendedHopfTower (K := K) S B))
  have he (x : GeometricCharacters K A) :
      b (geometricPullback K f x) = geometricPullback S f (a x) := by
    apply GroupLike.val_injective
    change (extendedHopfTower (K := K) S B).hom.hom
        ((1 : S) ⊗ₜ[K] ((extendedHopfMap K f).hom x.val)) =
      (extendedHopfMap S f).hom
        ((extendedHopfTower (K := K) S A).hom.hom ((1 : S) ⊗ₜ[K] x.val))
    generalize x.val = y
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, TensorProduct.tmul_add, hy, hz]
    | tmul r y => rfl
  constructor
  · intro y
    obtain ⟨z, rfl⟩ := b.surjective y
    obtain ⟨x, rfl⟩ := hs z
    exact ⟨a x, (he x).symm⟩
  · ext y
    obtain ⟨x, rfl⟩ := a.surjective y
    change geometricPullback S f (a x) = 1 ↔ a x ∈ CommGroup.torsion _
    rw [← he, ← b.map_one, b.injective.eq_iff]
    change x ∈ (geometricPullback K f).ker ↔ x ∈ (CommGroup.torsion _).comap a.toMonoidHom
    rw [hk]
    exact (a.injective.isOfFinOrder_iff).symm

private theorem centre_baseChange {Z : ClosedSubgroup G} (h : IsSchemeCentre Z)
    (L : Type u) [Field L] [Algebra k L] :
    ∃ hZ : IsClosedImmersion ((groupBaseChange k L).map Z.inclusion).hom.hom.left,
      IsSchemeCentre (baseChangedSubgroup L Z hZ) := by
  obtain ⟨hZ, hp⟩ := centralizerSchemeBaseChange k L (𝟙 G) Z h
  have hid : (groupBaseChange k L).map (𝟙 G) = 𝟙 ((groupBaseChange k L).obj G) :=
    CategoryTheory.Functor.map_id _ _
  refine ⟨hZ, ?_⟩
  change RepresentsSubgroup (scalarExtendedSubgroup L Z hZ)
    (fun _ g ↦ Centralizes (𝟙 ((groupBaseChange k L).obj G)) g)
  simpa only [hid] using hp

private theorem isLargest_transport {Z : GroupScheme k} (X Y : ClosedSubgroup Z)
    (hY : IsLargestTorus Y) (e : X.group ≅ Y.group) (he : e.hom ≫ Y.inclusion = X.inclusion) :
    IsLargestTorus X := by
  refine ⟨torus_iso e hY.1, ?_⟩
  intro S hS
  obtain ⟨f, hf⟩ := hY.2 S hS
  exact ⟨f ≫ e.inv, by rw [Category.assoc, ← he, Iso.inv_hom_id_assoc, hf]⟩

theorem largestCentralTorus_conditional :
    Specs.MaximalToriExist.GeometricallyMaximalTorusExists.{u} →
    Specs.TorusCentralizer.MaximalTorusCentralizer.{u} →
    LargestCentralTorus.{u} := by
  intro existsT selfCentralizing k _ G hG Z hZ
  letI := Z.isClosedImmersion
  haveI : IsAffine G.val.X.left := G.property.1
  let Z' : AffineGroupCategory k := ⟨Z.group, isAffine_of_isAffineHom Z.inclusion.hom.hom.left⟩
  let A := coordinateHopf Z'
  let e : specGroup A ≅ Z.group := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso Z')
  have ha : IsMultiplicativeType A := by
    apply (CharacterDescent.multiplicativeTypeOnSchemes A).mpr
    obtain ⟨E, _, _, _, M, ⟨d⟩⟩ := centre_splits existsT selfCentralizing G hG Z hZ
    exact ⟨E, inferInstance, inferInstance, inferInstance, M,
      ⟨(groupBaseChange k E).mapIso e ≪≫ d⟩⟩
  let A' : MultiplicativeTypeHopf k :=
    ⟨⟨A, (CharacterDescent.multiplicativeTypeProperties A ha).1⟩, ha⟩
  let K := SeparableClosure k
  obtain ⟨B, f, hs, hk⟩ := exists_torus_quotient K A'
  have hb := (CharacterDescent.splitsOverSeparableClosure (K := K) B.obj.val).mp B.property
  have hf := (hopfMapClosedImmersion k f).mpr (surjective_of_geometricPullback K f hb hs)
  letI := hf
  let h : IsClosedImmersion (specGroupMap f ≫ e.hom).hom.hom.left := by
    change IsClosedImmersion ((specGroupMap f).hom.hom.left ≫ e.hom.hom.hom.left)
    infer_instance
  let T : ClosedSubgroup Z.group := ⟨_, specGroupMap f ≫ e.hom, h⟩
  refine ⟨T, isLargest_of_torus_quotient K f hs hk e h, ?_⟩
  intro L _ _
  obtain ⟨hz, hz'⟩ := centre_baseChange hZ L
  let ht := baseChangeClosedSubgroup k L T.inclusion T.isClosedImmersion
  refine ⟨hz, ht, hz', ?_⟩
  let K' := separableClosure k (AlgebraicClosure L)
  let S := SeparableClosure L
  obtain ⟨a, haTower⟩ := CharacterDescent.compatibleSeparableClosures k L
  letI : Algebra K' S := a
  letI : IsScalarTower k K' S := haTower
  have haL := (CharacterDescent.baseChangeRestrictsAction (k := k) (L := L) (K := K') (S := S) A ha).1
  have hbL := (CharacterDescent.baseChangeRestrictsAction (k := k) (L := L) (K := K') (S := S) B.obj.val B.property).1
  let A_L : MultiplicativeTypeHopf L :=
    ⟨⟨_, (CharacterDescent.multiplicativeTypeProperties _ haL).1⟩, haL⟩
  let B_L : MultiplicativeTypeHopf L :=
    ⟨⟨_, (CharacterDescent.multiplicativeTypeProperties _ hbL).1⟩, hbL⟩
  let j := IsSepClosure.equiv k K K'
  letI : Algebra K K' := j.toRingHom.toAlgebra
  letI : IsScalarTower k K K' := IsScalarTower.of_algebraMap_eq' j.toAlgHom.comp_algebraMap.symm
  have hAK := (CharacterDescent.splitsOverSeparableClosure (K := K) A).mp ha
  have hAK' := (CharacterDescent.splitsOverSeparableClosure (K := K') A).mp ha
  have hBK' := (CharacterDescent.splitsOverSeparableClosure (K := K') B.obj.val).mp B.property
  obtain ⟨hs', hk'⟩ := quotient_between_splitting_fields (S := K') f hAK hb hs hk
  obtain ⟨hsL, hkL⟩ := quotient_after_scalar_extension (L := L) (S := S) f hAK' hBK' hs' hk'
  let eL := extendedGroupIso L A ≪≫ (groupBaseChange k L).mapIso e
  let d := extendedGroupIso L B.obj.val
  let fL := extendedHopfMap L f
  have heq : specGroupMap fL ≫ eL.hom = d.hom ≫ (groupBaseChange k L).map T.inclusion := by
    change specGroupMap fL ≫ (extendedGroupIso L A).hom ≫ (groupBaseChange k L).map e.hom =
      d.hom ≫ (groupBaseChange k L).map (specGroupMap f ≫ e.hom)
    rw [← Category.assoc, extendedGroupIso_natural, Category.assoc, CategoryTheory.Functor.map_comp]
  have hclosed : IsClosedImmersion (specGroupMap fL ≫ eL.hom).hom.hom.left := by
    rw [heq]
    letI := ht
    change IsClosedImmersion (d.hom.hom.hom.left ≫ ((groupBaseChange k L).map T.inclusion).hom.hom.left)
    infer_instance
  exact isLargest_transport _ _
    (isLargest_of_torus_quotient S (A := A_L) (B := B_L) fL hsL hkL eL hclosed)
    d.symm (by
      change d.inv ≫ specGroupMap fL ≫ eL.hom = (groupBaseChange k L).map T.inclusion
      rw [heq, Iso.inv_hom_id_assoc])

private theorem split_quotient_characterizes_torus {Z : GroupScheme k} (M : FGAbelianGroup.{u})
    (e : Z ≅ specGroup (groupAlgebra k M.obj)) (T : ClosedSubgroup Z)
    (ht : IsLargestTorus T) :
    ∃ j : T.group ≅ specGroup (groupAlgebra k (M.obj ⧸ CommGroup.torsion M.obj)),
      j.hom ≫ diagonalClosedInclusion k (CommGroup.torsion M.obj) = T.inclusion ≫ e.hom := by
  letI := M.property
  let N := CommGroup.torsion M.obj
  let A := groupAlgebra k M.obj
  let B := groupAlgebra k (M.obj ⧸ N)
  have hA : IsDiagonalizable A := ⟨M, ⟨Iso.refl _⟩⟩
  have hB : IsDiagonalizable B := ⟨⟨CommGrpCat.of _, inferInstance⟩, ⟨Iso.refl _⟩⟩
  let K := SeparableClosure k
  have hAmt : IsMultiplicativeType A := ⟨k, inferInstance, inferInstance, inferInstance,
    by exact splitBaseChange (K := k) A hA⟩
  have hBmt : IsMultiplicativeType B := ⟨k, inferInstance, inferInstance, inferInstance,
    by exact splitBaseChange (K := k) B hB⟩
  let A' : MultiplicativeTypeHopf k := ⟨⟨A, inferInstance⟩, hAmt⟩
  let B' : MultiplicativeTypeHopf k := ⟨⟨B, inferInstance⟩, hBmt⟩
  let f := Specs.DiagonalizableGroups.groupAlgebraMap k (QuotientGroup.mk' N)
  let charEquiv (C : HopfAlgebraCategory k) (hs : IsDiagonalizable C) :
      GroupLike k C ≃* GeometricCharacters K C :=
    MulEquiv.ofBijective (baseChangeCharacterMap K C)
      (CharacterDescent.baseChangeCharacterMap_bijective K C hs)
  let a : M.obj ≃* GeometricCharacters K A := (monomialCharacterEquiv k).trans (charEquiv A hA)
  let b : (M.obj ⧸ N) ≃* GeometricCharacters K B :=
    (monomialCharacterEquiv k).trans (charEquiv B hB)
  have hf (x : M.obj) : geometricPullback K f (a x) = b (QuotientGroup.mk' N x) := by
    apply GroupLike.val_injective
    change (1 : K) ⊗ₜ[k] (f.hom (MonoidAlgebra.of k _ x)) =
      (1 : K) ⊗ₜ[k] (MonoidAlgebra.of k _ (QuotientGroup.mk' N x))
    change (1 : K) ⊗ₜ[k] (MonoidAlgebra.mapDomainBialgHom k (QuotientGroup.mk' N)
      (MonoidAlgebra.single x 1)) = (1 : K) ⊗ₜ[k] (MonoidAlgebra.single (QuotientGroup.mk' N x) 1)
    rw [MonoidAlgebra.mapDomainBialgHom_single]
  have hsurj : Function.Surjective (geometricPullback K f) := by
    intro y
    obtain ⟨z, rfl⟩ := b.surjective y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    exact ⟨a x, hf x⟩
  let pull : GeometricCharacters K A →* GeometricCharacters K B := geometricPullback K f
  have hker : MonoidHom.ker (G := GeometricCharacters K A) (M := GeometricCharacters K B)
      pull = CommGroup.torsion (GeometricCharacters K A) := by
    ext y
    obtain ⟨x, rfl⟩ := a.surjective y
    change geometricPullback K f (a x) = 1 ↔ a x ∈ CommGroup.torsion _
    rw [hf]
    have h1 : b (1 : M.obj ⧸ N) = (1 : GeometricCharacters K B) := map_one b
    rw [← h1, b.injective.eq_iff]
    change ((x : M.obj) : M.obj ⧸ N) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    change IsOfFinOrder x ↔ IsOfFinOrder (a x)
    rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
    constructor
    · rintro ⟨n, hn, hx⟩
      exact ⟨n, hn, (map_pow a x n).symm.trans (by rw [hx]; exact map_one a)⟩
    · rintro ⟨n, hn, hx⟩
      refine ⟨n, hn, a.injective ?_⟩
      rw [map_pow, hx, map_one]
  letI := (hopfMapClosedImmersion k f).mpr
    (surjective_of_geometricPullback K f (splitBaseChange B hB) hsurj)
  have hc : IsClosedImmersion (specGroupMap f ≫ e.inv).hom.hom.left := by
    change IsClosedImmersion ((specGroupMap f).hom.hom.left ≫ e.inv.hom.hom.left)
    infer_instance
  let U : ClosedSubgroup Z := ⟨_, specGroupMap f ≫ e.inv, hc⟩
  have hu := isLargest_of_torus_quotient K (A := A') (B := B') f hsurj hker e.symm hc
  change IsLargestTorus U at hu
  obtain ⟨t, htu⟩ := hu.2 T ht.1
  obtain ⟨s, hut⟩ := ht.2 U hu.1
  letI : Mono T.inclusion.hom.hom := by
    letI := T.isClosedImmersion
    exact Over.mono_of_mono_left _
  letI : Mono U.inclusion.hom.hom := by
    letI := U.isClosedImmersion
    exact Over.mono_of_mono_left _
  let F := Grp.forget (SchemeOver k)
  letI : Mono T.inclusion := F.mono_of_mono_map (show Mono (F.map T.inclusion) from
    (show Mono T.inclusion.hom.hom from inferInstance))
  letI : Mono U.inclusion := F.mono_of_mono_map (show Mono (F.map U.inclusion) from
    (show Mono U.inclusion.hom.hom from inferInstance))
  refine ⟨⟨t, s, ?_, ?_⟩, ?_⟩
  · rw [← cancel_mono T.inclusion, Category.assoc, hut, htu, Category.id_comp]
  · rw [← cancel_mono U.inclusion, Category.assoc, htu, hut, Category.id_comp]
  · have q := congrArg (· ≫ e.hom) htu
    simpa [U, Category.assoc, diagonalClosedInclusion, f] using q

theorem splitCentralTorus_conditional :
    Specs.MaximalToriExist.GeometricallyMaximalTorusExists.{u} →
    Specs.TorusCentralizer.MaximalTorusCentralizer.{u} →
    SplitCentralTorus.{u} := by
  intro _ _ k _ _ _ Z _ T hT M e
  exact split_quotient_characterizes_torus M e T hT

open scoped CategoryTheory.MonObj
open WithConv

open RationalRepresentations (coefficients IsCoactionMatrix coaction_apply_basis
  coefficients_isCoactionMatrix matrixPointHom)
open WeightDecomposition (weightSpace mem_weightSpace)

open private restrictCoaction from LinearAlgebraicGroups.Unipotent.ExactOperations
open private basis_vector_eq_sum_coefficients from LinearAlgebraicGroups.Affine.FaithfulLinearization

private theorem diagonal_coefficients {M V J : Type u} [CommGroup M]
    [AddCommGroup V] [Module k V] [Fintype J] [DecidableEq J]
    {A : HopfAlgebraCategory k} (q : A ⟶ groupAlgebra k M)
    (ρ : RightComodule k A V) (b : Module.Basis J k V) (w : J → M)
    (hw : ∀ j, b j ∈ weightSpace (restrictCoaction q ρ) (w j))
    (i j : J) :
    q.hom (coefficients A b ρ i j) = if i = j then MonoidAlgebra.of k M (w j) else 0 := by
  have h := mem_weightSpace.mp (hw j)
  change (q.hom.toLinearMap.lTensor V) (ρ.coaction (b j)) =
    b j ⊗ₜ[k] MonoidAlgebra.of k M (w j) at h
  rw [coaction_apply_basis A b ρ, map_sum] at h
  have h' := congrArg (RationalRepresentations.tensorCoordinate b i) h
  simpa [RationalRepresentations.tensorCoordinate, LinearMap.rTensor_tmul,
    LinearMap.lTensor_tmul, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply, eq_comm] using! h'

/-- The universal point of the closed central subgroup commutes with that of the
ambient group over the tensor product of their coordinate algebras. -/
private theorem offBlock_zero {M J : Type u} [CommGroup M] [Fintype J] [DecidableEq J]
    {A : HopfAlgebraCategory k} (q : A ⟶ groupAlgebra k M) (X : Matrix J J A)
    (hX : IsCoactionMatrix A X) (w : J → M)
    (hq : ∀ i j, q.hom (X i j) = if i = j then MonoidAlgebra.of k M (w j) else 0)
    (hcentral : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R) (c : MonoidAlgebra k M →ₐ[k] R),
      letI := convolutionGroup A R
      Commute (toConv a) (toConv (c.comp q.hom.toAlgHom)))
    (i j : J) (hij : w i ≠ w j) :
    X i j = 0 := by
  classical
  let B := MonoidAlgebra k M
  let R := CommAlgCat.of k (A ⊗[k] B)
  let a : A →ₐ[k] R := Algebra.TensorProduct.includeLeft
  let c : B →ₐ[k] R := Algebra.TensorProduct.includeRight
  letI := convolutionGroup A R
  let τ := (matrixPointHom A X hX).app R
  have he := (hcentral R a c).map τ.hom
  have he' : a.mapMatrix X * (c.comp q.hom.toAlgHom).mapMatrix X =
      (c.comp q.hom.toAlgHom).mapMatrix X * a.mapMatrix X :=
    congrArg Units.val he.eq
  have hd : (c.comp q.hom.toAlgHom).mapMatrix X =
      Matrix.diagonal (fun l ↦ (1 : A) ⊗ₜ[k] MonoidAlgebra.of k M (w l)) := by
    ext a b
    change c (q.hom (X a b)) = _
    rw [hq]
    by_cases hab : a = b
    · subst b
      rw [ite_eq_left rfl, Matrix.diagonal_apply_eq]
      rfl
    · simp [hab]
  rw [hd] at he'
  have h := congrFun (congrFun he' i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  change (X i j ⊗ₜ[k] (1 : B)) * ((1 : A) ⊗ₜ[k] MonoidAlgebra.of k M (w j)) =
    ((1 : A) ⊗ₜ[k] MonoidAlgebra.of k M (w i)) * (X i j ⊗ₜ[k] (1 : B)) at h
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h
  let p := (MonoidAlgebra.basis M k).coord (w j)
  have e := congrArg (fun z : A ⊗[k] B ↦
    TensorProduct.rid k A (p.lTensor A z)) h
  change TensorProduct.rid k A (p.lTensor A (X i j ⊗ₜ[k] MonoidAlgebra.of k M (w j))) =
    TensorProduct.rid k A (p.lTensor A (X i j ⊗ₜ[k] MonoidAlgebra.of k M (w i))) at e
  simp only [LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at e
  have h₁ : p (MonoidAlgebra.of k M (w j)) = 1 := by
    change (MonoidAlgebra.basis M k).coord (w j) ((MonoidAlgebra.basis M k) (w j)) = 1
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same]
  have h₀ : p (MonoidAlgebra.of k M (w i)) = 0 := by
    change (MonoidAlgebra.basis M k).coord (w j) ((MonoidAlgebra.basis M k) (w i)) = 0
    rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne (Ne.symm hij)]
  rwa [h₁, h₀, one_smul, zero_smul] at e

private theorem block_isCoactionMatrix {J M : Type u} [Fintype J] [DecidableEq J] [DecidableEq M]
    {A : HopfAlgebraCategory k} (X : Matrix J J A) (hX : IsCoactionMatrix A X)
    (w : J → M) (hzero : ∀ i j, w i ≠ w j → X i j = 0) (m : M) :
    IsCoactionMatrix A (X.submatrix (Subtype.val : {i // w i = m} → J) Subtype.val) := by
  constructor
  · intro i j
    change comul (R := k) (X i j) = ∑ l : {i // w i = m}, X i l ⊗ₜ[k] X l j
    rw [hX.comul]
    rw [← Finset.subtype_univ (fun l : J ↦ w l = m)]
    rw [Finset.sum_subtype_eq_sum_filter (fun l : J ↦ X i.val l ⊗ₜ[k] X l j.val)]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro l _ hl
    have h : w i ≠ w l := by
      intro h
      exact hl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.symm.trans i.property⟩)
    rw [hzero i l h, TensorProduct.zero_tmul]
  · intro i j
    change counit (R := k) (X i j) = (1 : Matrix {i // w i = m} {i // w i = m} k) i j
    rw [hX.counit]
    by_cases he : i = j
    · subst j
      simp
    · have hn : (i : J) ≠ (j : J) := fun h ↦ he (Subtype.ext h)
      simp [he, hn]

private theorem determinant_isGroupLike {J : Type u} [Fintype J] [DecidableEq J]
    {A : HopfAlgebraCategory k} (X : Matrix J J A) (hX : IsCoactionMatrix A X) :
    IsGroupLikeElem k X.det := by
  constructor
  · have hu : (Bialgebra.counitAlgHom k A).mapMatrix X = 1 := by
      ext i j
      exact hX.counit i j
    change (Bialgebra.counitAlgHom k A) X.det = 1
    rw [AlgHom.map_det, hu, Matrix.det_one]
  · let l : A →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.includeLeft
    let r : A →ₐ[k] A ⊗[k] A := Algebra.TensorProduct.includeRight
    have he : (Bialgebra.comulAlgHom k A).mapMatrix X = l.mapMatrix X * r.mapMatrix X := by
      ext i j
      change Coalgebra.comul (R := k) (X i j) = ∑ h, (X i h ⊗ₜ[k] (1 : A)) * (1 ⊗ₜ[k] X h j)
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      exact hX.comul i j
    change (Bialgebra.comulAlgHom k A) X.det = _
    rw [AlgHom.map_det, he, Matrix.det_mul, ← AlgHom.map_det, ← AlgHom.map_det]
    change (X.det ⊗ₜ[k] (1 : A)) * (1 ⊗ₜ[k] X.det) = _
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

private theorem integral_diagonal_coefficient {M J : Type u} [CommGroup M] [Fintype J] [DecidableEq J]
    {A : HopfAlgebraCategory k} (q : A ⟶ groupAlgebra k M) (X : Matrix J J A)
    (hX : IsCoactionMatrix A X) (w : J → M)
    (hdiag : ∀ i j, q.hom (X i j) = if i = j then MonoidAlgebra.of k M (w j) else 0)
    (hzero : ∀ i j, w i ≠ w j → X i j = 0)
    (hderived : ∀ x : GroupLike k A, q.hom x.val = 1)
    (i j : J) : IsIntegral k (q.hom (X i j)) := by
  classical
  rw [hdiag i j]
  by_cases hij : i = j
  · rw [ite_eq_left hij]
    let B := X.submatrix (Subtype.val : {i // w i = w j} → J) (Subtype.val : {i // w i = w j} → J)
    have hB := block_isCoactionMatrix X hX w hzero (w j)
    have hone := hderived ⟨B.det, determinant_isGroupLike B hB⟩
    change q.hom B.det = 1 at hone
    let e := MonoidAlgebra.of k M (w j)
    have he : q.hom.toAlgHom.mapMatrix B = Matrix.diagonal (fun _ ↦ e) := by
      apply Matrix.ext
      intro a b
      change q.hom (X a b) = _
      rw [hdiag, show (w b.val) = w j from b.property, Matrix.diagonal_apply]
      by_cases h : a = b
      · subst b
        simp [e]
      · have h' : a.val ≠ b.val := fun he ↦ h (Subtype.ext he)
        simp [h, h']
    have hp : e ^ Fintype.card {i // w i = w j} = 1 := calc
      _ = (Matrix.diagonal (fun _ : {i // w i = w j} ↦ e)).det := by
        rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ]
      _ = (q.hom.toAlgHom.mapMatrix B).det := by rw [he]
      _ = q.hom B.det := (RingHom.map_det q.hom.toAlgHom.toRingHom B).symm
      _ = 1 := hone
    have hc : 0 < Fintype.card {i // w i = w j} := Fintype.card_pos_iff.mpr ⟨⟨j, rfl⟩⟩
    exact IsIntegral.of_pow hc (hp ▸ isIntegral_one)
  · rw [ite_eq_right hij]
    exact isIntegral_zero

private theorem finite_split_central_coordinate_quotient {M : Type u} [CommGroup M]
    {A : HopfAlgebraCategory k} [Algebra.FiniteType k A]
    (q : A ⟶ groupAlgebra k M) (hq : Function.Surjective q.hom)
    (hcentral : ∀ (R : TestAlgebra k) (a : A →ₐ[k] R) (c : MonoidAlgebra k M →ₐ[k] R),
      letI := convolutionGroup A R
      Commute (toConv a) (toConv (c.comp q.hom.toAlgHom)))
    (hderived : ∀ x : GroupLike k A, q.hom x.val = 1) :
    Module.Finite k (MonoidAlgebra k M) := by
  classical
  let ρ : RightComodule k A A := RightComodule.regular
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType k A).out
  obtain ⟨W₀, hsW⟩ := ρ.exists_finiteSubcomodule_containing (s : Set A) s.finite_toSet
  let W := W₀.val
  letI : FiniteDimensional k W := W₀.property.2
  obtain ⟨σ, hσ⟩ := (ρ.isSubcomodule_iff_exists_coaction W).mp W₀.property.1
  let V := weightSpace (restrictCoaction q σ)
  let bs (m : M) := Module.Basis.ofVectorSpace k (V m)
  have hw := WeightDecomposition.weightDecomposition (restrictCoaction q σ)
  let b := hw.collectedBasis bs
  let J := Σ m : M, Module.Basis.ofVectorSpaceIndex k (V m)
  letI : Finite J := Module.Finite.finite_basis b
  letI : Fintype J := Fintype.ofFinite J
  let X := coefficients A b σ
  have hX := coefficients_isCoactionMatrix A b σ
  have hdiag : ∀ i j : J, q.hom (X i j) =
      if i = j then MonoidAlgebra.of k M j.1 else 0 :=
    diagonal_coefficients q σ b Sigma.fst (fun j ↦ hw.collectedBasis_mem bs j)
  have hzero : ∀ i j : J, i.1 ≠ j.1 → X i j = 0 :=
    offBlock_zero q X hX Sigma.fst hdiag hcentral
  let C := integralClosure k (MonoidAlgebra k M)
  have hC (i j : J) : q.hom (X i j) ∈ C :=
    integral_diagonal_coefficient q X hX Sigma.fst hdiag hzero hderived i j
  have hb (j : J) : q.hom (b j : A) ∈ C := by
    rw [basis_vector_eq_sum_coefficients A W b σ hσ j, map_sum]
    exact C.toSubmodule.sum_mem fun i _ ↦ by
      rw [map_smul]
      exact C.toSubmodule.smul_mem _ (hC i j)
  have hW (x : W) : q.hom (x : A) ∈ C := by
    rw [← b.sum_repr x]
    change q.hom (W.subtype (∑ i, b.repr x i • b i)) ∈ C
    rw [map_sum, map_sum]
    exact C.toSubmodule.sum_mem fun i _ ↦ by
      rw [map_smul, map_smul]
      exact C.toSubmodule.smul_mem _ (hb i)
  have htop : C.comap q.hom.toAlgHom = ⊤ := by
    apply top_unique
    rw [← hs]
    exact Algebra.adjoin_le fun x hx ↦ hW ⟨x, hsW hx⟩
  have hI : Algebra.IsIntegral k (MonoidAlgebra k M) := by
    constructor
    intro x
    obtain ⟨a, rfl⟩ := hq x
    change a ∈ C.comap q.hom.toAlgHom
    rw [htop]
    exact Algebra.mem_top
  let hfg := Algebra.FiniteType.of_surjective q.hom.toAlgHom hq
  exact RingHom.finite_algebraMap.mp
    ((algebraMap_isIntegral_iff.mpr hI).to_finite (RingHom.finiteType_algebraMap.mpr hfg))

open Specs.CharacterDescent (Character)
open Specs.SchemeDerivedGroup (commutatorMap FactorsThrough)
open private schemeKernel_exists schemeKernel_sections from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private kernel_normal from LinearAlgebraicGroups.Solvable.SchemeDerivedGroup

private theorem derived_kills_character {G : GroupScheme k} (D : ClosedSubgroup G)
    (hD : IsDerivedSubgroup D) (χ : Character G) : D.inclusion ≫ χ = 1 := by
  have : IsAffine (specGroup (groupAlgebra k
      Specs.DiagonalizableGroups.IntegerCharacters)).X.left := by
    change IsAffine (Spec (CommRingCat.of (MonoidAlgebra k
      Specs.DiagonalizableGroups.IntegerCharacters)))
    infer_instance
  obtain ⟨N, hN⟩ := schemeKernel_exists χ
  have hc : FactorsThrough N (commutatorMap (𝟙 G) (𝟙 G)) := by
    apply (schemeKernel_sections hN _).mpr
    have hid : (𝟙 G : G ⟶ G).hom.hom = 𝟙 G.X := rfl
    simp only [commutatorMap, hid, Category.comp_id, MonObj.mul_comp, GrpObj.inv_comp]
    let Y := (specGroup (groupAlgebra k Specs.DiagonalizableGroups.IntegerCharacters)).X
    let x : G.X ⊗ G.X ⟶ Y := fst _ _ ≫ χ.hom.hom
    let y : G.X ⊗ G.X ⟶ Y := snd _ _ ≫ χ.hom.hom
    change x * y * x⁻¹ * y⁻¹ = 1
    have h : Commute x y := mul_comm _ _
    rw [h.eq, mul_assoc y x x⁻¹, mul_inv_cancel, mul_one, mul_inv_cancel]
  obtain ⟨j, hj⟩ := hD.2.2 N (kernel_normal hN) hc
  apply Grp.hom_ext
  have hm : D.inclusion.hom.hom ∈ SubgroupSections N D.group.X :=
    ⟨j.hom.hom, congrArg (Grp.forget (SchemeOver k)).map hj⟩
  exact (schemeKernel_sections hN _).mp hm

private theorem commute_from_centre {G : GroupScheme k} {U : SchemeOver k}
    {g : U ⟶ G.X} (hg : Centralizes (𝟙 G) g)
    {R : SchemeOver k} (x : R ⟶ U) (y : R ⟶ G.X) :
    Commute (x ≫ g) y := by
  have h := (centralizes_iff _ _).mp hg R x y
  simpa using h

private theorem finite_structure_of_finite_hopf (A : HopfAlgebraCategory k) [Module.Finite k A] :
    IsFinite (specGroup A).X.hom := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k A)))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

private theorem finite_diagonal_subgroup_of_centre_and_derived (G : AffineAlgebraicGroup k)
    (D : ClosedSubgroup G.val) (hD : IsDerivedSubgroup D)
    {H : GroupScheme k} (i : H ⟶ G.val) (hi : IsClosedImmersion i.hom.hom.left)
    (hcent : Centralizes (𝟙 G.val) i.hom.hom)
    (p : H ⟶ D.group) (hp : p ≫ D.inclusion = i)
    (M : Type u) [CommGroup M] (e : specGroup (groupAlgebra k M) ≅ H) :
    IsFinite H.X.hom := by
  let Eq := finiteTypeHopfEquivalence k
  let As := (Eq.inverse.obj G).unop
  let A := As.val
  letI : Algebra.FiniteType k A := As.property
  let E : specGroup A ≅ G.val := (inducedFunctor Subtype.val).mapIso (Eq.counitIso.app G)
  let B := groupAlgebra k M
  let j := e.hom ≫ i ≫ E.inv
  let q : A ⟶ B := hopfPreimage j
  have hq : specGroupMap q = j := specGroupMap_hopfPreimage j
  have hqi : IsClosedImmersion (specGroupMap q).hom.hom.left := by
    rw [hq]
    letI := hi
    change IsClosedImmersion (e.hom.hom.hom.left ≫ i.hom.hom.left ≫ E.inv.hom.hom.left)
    infer_instance
  have hqsurj := (hopfMapClosedImmersion k q).mp hqi
  obtain ⟨conv, _, hn⟩ := hopfSpecPoints k
  have hcentral (R : TestAlgebra k) (a : A →ₐ[k] R) (c : MonoidAlgebra k M →ₐ[k] R) :
      letI := convolutionGroup A R
      Commute (toConv a) (toConv (c.comp q.hom.toAlgHom)) := by
    letI := convolutionGroup A R
    let α := (conv A).hom.app R
    let β := (conv B).hom.app R
    apply Commute.of_map (f := α.hom) (ConcreteCategory.bijective_of_isIso α).1
    have hc := hn q R (toConv c)
    change ((conv A).hom.app R (toConv (c.comp q.hom.toAlgHom)) : Points _ R) =
      (β (toConv c) : Points _ R) ≫ (specGroupMap q).hom.hom at hc
    change Commute (α (toConv a) : Points _ R) (α (toConv (c.comp q.hom.toAlgHom)) : Points _ R)
    rw [hc]
    let f := (yonedaGrp.map E.hom).app (op ((testSpec k).obj (op R)))
    apply Commute.of_map (f := f.hom) (ConcreteCategory.bijective_of_isIso f).1
    change Commute
      ((α (toConv a) : Points _ R) ≫ E.hom.hom.hom)
      (((β (toConv c) : Points _ R) ≫ (specGroupMap q).hom.hom) ≫ E.hom.hom.hom)
    have hj : (specGroupMap q).hom.hom ≫ E.hom.hom.hom = e.hom.hom.hom ≫ i.hom.hom := by
      have hx : specGroupMap q ≫ E.hom = e.hom ≫ i := by rw [hq]; simp [j]
      exact congrArg (Grp.forget (SchemeOver k)).map hx
    rw [Category.assoc, hj, ← Category.assoc]
    exact (commute_from_centre hcent _ _).symm
  obtain ⟨chars, hchars, _⟩ := CharacterDescent.characterInterpretation (k := k)
  have hderived (x : GroupLike k A) : q.hom x.val = 1 := by
    let ψ := chars A x
    let χ : Character G.val := E.inv ≫ ψ
    have hk := derived_kills_character D hD χ
    have hχ : specGroupMap q ≫ ψ = 1 := by
      rw [hq]
      change e.hom ≫ i ≫ χ = 1
      rw [← hp, Category.assoc, hk]
      apply Grp.hom_ext
      change (e.hom ≫ p).hom.hom ≫ (1 : D.group.X ⟶ _) = 1
      rw [MonObj.comp_one]
    have h := hchars A B q x
    change chars B (mapGroupLike q x) = specGroupMap q ≫ ψ at h
    rw [hχ, ← map_one (chars B)] at h
    exact congrArg GroupLike.val ((chars B).injective h)
  letI := finite_split_central_coordinate_quotient q hqsurj hcentral hderived
  have hfinite := finite_structure_of_finite_hopf B
  rw [← e.inv.hom.hom.w]
  letI := hfinite
  infer_instance

private theorem finite_of_finite_group_baseChange (K : Type u) [Field K] [Algebra k K]
    (G : GroupScheme k) (hG : IsAffine G.X.left)
    (hK : IsFinite ((groupBaseChange k K).obj G).X.hom) : IsFinite G.X.hom := by
  let G' : AffineGroupCategory k := ⟨G, hG⟩
  let A := coordinateHopf G'
  let E : specGroup A ≅ G := (affineGroupInclusion k).mapIso (coordinateHopfSpecIso G')
  let e := extendedGroupIso K A ≪≫ (groupBaseChange k K).mapIso E
  have he : IsFinite (specGroup (extendedHopf K A)).X.hom := by
    rw [← e.hom.hom.hom.w]
    letI := hK
    infer_instance
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A)))) at he
  have : Module.Finite K (K ⊗[k] A) :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp he)
  letI : Module.Finite k A := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat K
  have : IsFinite (specGroup A).X.hom := finite_structure_of_finite_hopf A
  rw [← E.inv.hom.hom.w]
  infer_instance

open Specs.Unipotent (baseChangedAlgebraicGroup)

theorem centralTorusDerivedIntersectionFinite_conditional :
    Specs.MaximalToriExist.GeometricallyMaximalTorusExists.{u} →
    Specs.TorusCentralizer.MaximalTorusCentralizer.{u} →
    CentralTorusDerivedIntersectionFinite.{u} := by
  intro _ _ k _ G hG Z hZ T hT D hD
  let i : T.group ⟶ G.val := T.inclusion ≫ Z.inclusion
  let I := pullback i D.inclusion
  let p : I ⟶ T.group := pullback.fst i D.inclusion
  let q : I ⟶ D.group := pullback.snd i D.inclusion
  have hI : IsPullback p q i D.inclusion := IsPullback.of_hasPullback _ _
  refine ⟨I, p, q, hI, ?_⟩
  have hp : IsClosedImmersion p.hom.hom.left := by
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
      (F.map_isPullback hI).flip D.isClosedImmersion
  letI := hp
  letI := T.isClosedImmersion
  letI := Z.isClosedImmersion
  have hi : IsClosedImmersion (p ≫ i).hom.hom.left := by
    change IsClosedImmersion
      (p.hom.hom.left ≫ T.inclusion.hom.hom.left ≫ Z.inclusion.hom.hom.left)
    infer_instance
  have hAff : IsAffine I.X.left := by
    letI := hi
    letI := G.property.1
    exact isAffine_of_isAffineHom (p ≫ i).hom.hom.left
  obtain ⟨K, _, _, _, r, ⟨e⟩⟩ := hT.1
  apply finite_of_finite_group_baseChange K I hAff
  let F := groupBaseChange k K
  let G' := baseChangedAlgebraicGroup K G
  obtain ⟨hZc, hZK⟩ := centre_baseChange hZ K
  obtain ⟨hDc, hDK, _⟩ := Reductive.DerivedSubgroup.derivedSubgroupBaseChange K G D hD hG.1 hG.2.1
  let Z' := baseChangedSubgroup K Z hZc
  let D' : ClosedSubgroup G'.val := ⟨F.obj D.group, F.map D.inclusion, hDc⟩
  let i' := F.map (p ≫ i)
  have hi' := baseChangeClosedSubgroup k K (p ≫ i) hi
  have hc : Centralizes (𝟙 G'.val) i'.hom.hom := by
    apply (hZK (F.obj I).X i'.hom.hom).mpr
    refine ⟨(F.map (p ≫ T.inclusion)).hom.hom, ?_⟩
    have h : F.map (p ≫ T.inclusion) ≫ Z'.inclusion = i' := by
      change F.map (p ≫ T.inclusion) ≫ F.map Z.inclusion = F.map (p ≫ i)
      rw [← CategoryTheory.Functor.map_comp, Category.assoc]
    exact congrArg (Grp.forget (SchemeOver K)).map h
  have hq' : F.map q ≫ D'.inclusion = i' := by
    change F.map q ≫ F.map D.inclusion = F.map (p ≫ i)
    rw [← CategoryTheory.Functor.map_comp, hI.w]
  let M := Multiplicative (ULift.{u} (Fin r) → ℤ)
  obtain ⟨d⟩ := DiagonalizableGroups.diagonalIntegerPowers K (ULift.{u} (Fin r))
  let j := F.map p ≫ e.hom ≫ d.inv
  letI := baseChangeClosedSubgroup k K p hp
  have hj : IsClosedImmersion j.hom.hom.left := by
    change IsClosedImmersion ((F.map p).hom.hom.left ≫ e.hom.hom.hom.left ≫ d.inv.hom.hom.left)
    infer_instance
  obtain ⟨N, ⟨t, _⟩, _⟩ :=
    (DiagonalizableGroups.diagonalClosedSubgroups K M _ j).mp hj
  exact finite_diagonal_subgroup_of_centre_and_derived G' D' hDK i' hi' hc (F.map q) hq'
    (M ⧸ N) t.symm

end

end LinearAlgebraicGroups.CentralTorus

universe v8_closure_8d2b9715f35613c1_u0
theorem _root_.«LinearAlgebraicGroups».«CentralTorus».«centralTorusDerivedIntersectionFinite» : _root_.«LinearAlgebraicGroups».«Specs».«CentralTorus».«CentralTorusDerivedIntersectionFinite».{v8_closure_8d2b9715f35613c1_u0} :=
  @_root_.«LinearAlgebraicGroups».«CentralTorus».«centralTorusDerivedIntersectionFinite_conditional».{v8_closure_8d2b9715f35613c1_u0} (@_root_.«LinearAlgebraicGroups».«MaximalToriExist».«geometricallyMaximalTorusExists».{v8_closure_8d2b9715f35613c1_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«TorusCentralizer».«maximalTorusCentralizer».{v8_closure_8d2b9715f35613c1_u0})
theorem _root_.«LinearAlgebraicGroups».«CentralTorus».«centreMultiplicativeType» : _root_.«LinearAlgebraicGroups».«Specs».«CentralTorus».«CentreMultiplicativeType».{v8_closure_8d2b9715f35613c1_u0} :=
  @_root_.«LinearAlgebraicGroups».«CentralTorus».«centreMultiplicativeType_conditional».{v8_closure_8d2b9715f35613c1_u0} (@_root_.«LinearAlgebraicGroups».«MaximalToriExist».«geometricallyMaximalTorusExists».{v8_closure_8d2b9715f35613c1_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«TorusCentralizer».«maximalTorusCentralizer».{v8_closure_8d2b9715f35613c1_u0})
theorem _root_.«LinearAlgebraicGroups».«CentralTorus».«largestCentralTorus» : _root_.«LinearAlgebraicGroups».«Specs».«CentralTorus».«LargestCentralTorus».{v8_closure_8d2b9715f35613c1_u0} :=
  @_root_.«LinearAlgebraicGroups».«CentralTorus».«largestCentralTorus_conditional».{v8_closure_8d2b9715f35613c1_u0} (@_root_.«LinearAlgebraicGroups».«MaximalToriExist».«geometricallyMaximalTorusExists».{v8_closure_8d2b9715f35613c1_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«TorusCentralizer».«maximalTorusCentralizer».{v8_closure_8d2b9715f35613c1_u0})
theorem _root_.«LinearAlgebraicGroups».«CentralTorus».«splitCentralTorus» : _root_.«LinearAlgebraicGroups».«Specs».«CentralTorus».«SplitCentralTorus».{v8_closure_8d2b9715f35613c1_u0} :=
  @_root_.«LinearAlgebraicGroups».«CentralTorus».«splitCentralTorus_conditional».{v8_closure_8d2b9715f35613c1_u0} (@_root_.«LinearAlgebraicGroups».«MaximalToriExist».«geometricallyMaximalTorusExists».{v8_closure_8d2b9715f35613c1_u0}) (@_root_.«LinearAlgebraicGroups».«Reductive».«TorusCentralizer».«maximalTorusCentralizer».{v8_closure_8d2b9715f35613c1_u0})
