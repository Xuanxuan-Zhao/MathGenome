import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Multiplicative.DiagonalizableGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.StandardGroups
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory Opposite Coalgebra HopfAlgebra WithConv
open scoped TensorProduct MonoidAlgebra

set_option maxHeartbeats 1200000

universe u

namespace LinearAlgebraicGroups.DiagonalizableGroups

open Specs.DiagonalizableGroups

noncomputable section

abbrev diagonalGroup : DiagonalGroupType.{u} := @Specs.DiagonalizableGroups.diagonalGroup
abbrev diagonalFunctor : DiagonalFunctorType.{u} := @Specs.DiagonalizableGroups.diagonalFunctor

theorem groupAlgebraBasisAndHopfStructure : GroupAlgebraBasisAndHopfStructure.{u} := by
  intro k M _ _
  refine ⟨MonoidAlgebra.basis M k, fun _ => rfl, ?_⟩
  intro m
  change comul (R := k) (MonoidAlgebra.single m (1 : k)) = _ ∧ _ ∧ _
  have h := MonoidAlgebra.isGroupLikeElem_single_one (R := k) (A := k) m
  exact ⟨h.comul_eq_tmul_self, h.counit_eq_one, by simp⟩

variable {k : Type u} [Field k]

/-- The convolution of algebra maps corresponds to pointwise multiplication of characters. -/
def convolutionCharacterIso (M : Type u) [CommGroup M] :
    convolutionPoints (groupAlgebra k M) ≅ characterValuedPoints k M := by
  let e (R : TestAlgebra k) :
      (convolutionPoints (groupAlgebra k M)).obj R ≃* (characterValuedPoints k M).obj R :=
    (MonoidAlgebra.liftMulEquiv k R M).symm.trans MonoidHom.toHomUnitsMulEquiv
  refine NatIso.ofComponents (fun R => (e R).toGrpIso) ?_
  intro R S a
  apply GrpCat.ext
  intro f
  apply MonoidHom.ext
  intro m
  apply Units.ext
  rfl

theorem diagonalPoints : DiagonalPoints.{u} := by
  intro k M _ _ _
  let e := hopfSpecPointIso (groupAlgebra k M)
  refine ⟨e, fun _ _ => rfl, e.symm ≪≫ convolutionCharacterIso M, ?_⟩
  intro R f m
  have h : e ≪≫ (e.symm ≪≫ convolutionCharacterIso M) = convolutionCharacterIso M := by simp
  change ((show M →* Rˣ from (e ≪≫ (e.symm ≪≫ convolutionCharacterIso M)).hom.app R
    (toConv f)) m).val = _
  rw [h]
  rfl

theorem diagonalAntiequivalence : DiagonalAntiequivalence.{u} := by
  intro k _
  let ff : (groupAlgebraFunctor k).FullyFaithful :=
    { preimage := fun f => ObjectProperty.homMk
        (CommGrpCat.ofHom (MonoidAlgebra.mapDomainOfBialgHom f.hom.hom))
      map_preimage := by
        intro X Y f
        apply InducedCategory.hom_ext
        apply CommHopfAlgCat.hom_ext
        exact MonoidAlgebra.mapDomainBialgHom_mapDomainOfBialgHom f.hom.hom
      preimage_map := by
        intro X Y f
        apply InducedCategory.hom_ext
        apply CommGrpCat.ext
        exact DFunLike.congr_fun (MonoidAlgebra.mapDomainOfBialgHom_mapDomainBialgHom
          (R := k) f.hom.hom) }
  let := ff.full
  let := ff.faithful
  let := finiteTypeHopfSpecEquivalence k
  change ((groupAlgebraFunctor k).op ⋙ finiteTypeHopfSpec k).toEssImage.IsEquivalence
  infer_instance


section HopfMaps

open MonoidAlgebra

variable {M N : Type u} [CommGroup M] [CommGroup N]

private theorem groupAlgebraMap_injective (f : M →* N) (hf : Function.Injective f) :
    Function.Injective (mapDomainBialgHom k f) :=
  mapDomain_injective hf

private theorem groupAlgebraMap_surjective (f : M →* N) (hf : Function.Surjective f) :
    Function.Surjective (mapDomainBialgHom k f) := by
  intro x
  obtain ⟨y, hy⟩ := Finsupp.mapDomain_surjective hf x.coeff
  exact ⟨ofCoeff y, coeff_injective hy⟩

private def liftCharacters {A : HopfAlgebraCategory k} (f : M →* GroupLike k A) :
    MonoidAlgebra k M →ₐc[k] A :=
  (liftGroupLikeBialgHom (R := k) (A := A)).comp (mapDomainBialgHom k f)

private theorem liftCharacters_single {A : HopfAlgebraCategory k} (f : M →* GroupLike k A)
    (m : M) : liftCharacters f (single m 1) = (f m).val := by
  change liftGroupLikeBialgHom (mapDomainBialgHom k f (single m 1)) = _
  rw [mapDomainBialgHom_single]
  simp [liftGroupLikeBialgHom]

private theorem liftCharacters_injective {A : HopfAlgebraCategory k}
    (f : M →* GroupLike k A) (hf : Function.Injective f) :
    Function.Injective (liftCharacters f) := by
  have hind := (linearIndep_groupLikeVal (R := k) (A := A)).comp f hf
  have h : (Finsupp.linearCombination k (GroupLike.val ∘ f)).comp
      (coeffLinearEquiv k (M := M)).toLinearMap = (liftCharacters f).toAlgHom.toLinearMap := by
    apply (basis M k).ext
    intro m
    change Finsupp.linearCombination k (GroupLike.val ∘ f) (Finsupp.single m 1) =
      liftCharacters f (single m 1)
    rw [Finsupp.linearCombination_single, one_smul, liftCharacters_single]
    rfl
  have hi := (linearIndependent_iff_injective_finsuppLinearCombination.mp hind).comp
    (coeffLinearEquiv k (M := M)).injective
  intro x y hxy
  apply hi
  exact (LinearMap.congr_fun h x).trans (hxy.trans (LinearMap.congr_fun h y).symm)

theorem hopfQuotientClassification : HopfQuotientClassification.{u} := by
  intro k M _ _ A a
  constructor
  · intro ha
    let f := imageCharacters k a
    let q := QuotientGroup.mk' f.ker
    let b := liftCharacters (QuotientGroup.kerLift f)
    have hb : b.comp (mapDomainBialgHom k q) = a.hom := by
      apply bialgHom_ext _ (Subsingleton.elim _ _)
      intro m
      change b (mapDomainBialgHom k q (single m 1)) = _
      rw [mapDomainBialgHom_single, liftCharacters_single]
      rfl
    have hsurj : Function.Surjective b := by
      intro x
      obtain ⟨y, rfl⟩ := ha x
      exact ⟨mapDomainBialgHom k q y, DFunLike.congr_fun hb y⟩
    refine ⟨f.ker, ⟨BialgEquiv.ofBijective b
      ⟨liftCharacters_injective _ (QuotientGroup.kerLift_injective f), hsurj⟩, hb⟩, ?_⟩
    rintro N ⟨e, he⟩
    ext m
    have h := DFunLike.congr_fun he (single m (1 : k))
    change e (mapDomainBialgHom k (QuotientGroup.mk' N) (single m 1)) = a.hom (single m 1) at h
    rw [mapDomainBialgHom_single] at h
    have hf : m ∈ f.ker ↔ a.hom (single m 1) = 1 :=
      ⟨fun hm => congrArg GroupLike.val hm, fun hm => GroupLike.val_injective hm⟩
    rw [hf, ← h, ← map_one e]
    exact (QuotientGroup.eq_one_iff m).symm.trans <| by
      rw [show (1 : MonoidAlgebra k (M ⧸ N)) = single 1 1 from one_def,
        (show Function.Injective (fun x => e x) from e.injective).eq_iff,
        (single_left_injective (R := k) one_ne_zero).eq_iff]
      rfl
  · rintro ⟨N, ⟨e, he⟩, _⟩
    rw [← he]
    exact e.surjective.comp (groupAlgebraMap_surjective _ QuotientGroup.mk_surjective)

/-- Slicing the second tensor factor by the coefficient functional for `m`
extracts the `m`-term of a group-algebra element. -/
private theorem slice_comul (m : M) :
    (TensorProduct.rid k (MonoidAlgebra k M)).toLinearMap.comp
      ((TensorProduct.map (LinearMap.id : MonoidAlgebra k M →ₗ[k] MonoidAlgebra k M)
        ((basis M k).coord m)).comp comul) =
    (lsingle m).comp ((basis M k).coord m) := by
  classical
  apply (basis M k).ext
  intro i
  change (TensorProduct.rid k (MonoidAlgebra k M))
    (TensorProduct.map LinearMap.id ((basis M k).coord m) (comul (single i 1))) =
    single m ((basis M k).coord m (single i 1))
  rw [(isGroupLikeElem_single_one (R := k) (A := k) i).comul_eq_tmul_self,
    TensorProduct.map_tmul, TensorProduct.rid_tmul]
  simp only [LinearMap.id_apply, ← basis_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with h
  · subst m
    simp
  · simp

theorem hopfSubalgebraClassification : HopfSubalgebraClassification.{u} := by
  classical
  intro k M _ _ A a
  constructor
  · intro ha
    let χ : GroupLike k A →* M :=
      mapDomainOfBialgHom (a.hom.comp liftGroupLikeBialgHom)
    have hχ (x : GroupLike k A) : of k M (χ x) = a.hom x.val := by
      rw [show of k M (χ x) = single (χ x) 1 from rfl, single_mapDomainOfBialgHom]
      change a.hom (liftGroupLikeBialgHom (single x 1)) = _
      simp [liftGroupLikeBialgHom]
    have hiχ : Function.Injective χ :=
      fun x y h => GroupLike.val_injective (ha ((hχ x).symm.trans ((congrArg (of k M) h).trans (hχ y))))
    let N := χ.range
    let b := liftCharacters ((MonoidHom.ofInjective hiχ).symm.toMonoidHom)
    have hb : a.hom.comp b = mapDomainBialgHom k N.subtype := by
      apply bialgHom_ext _ (Subsingleton.elim _ _)
      intro m
      change a.hom (b (single m 1)) = _
      rw [liftCharacters_single, mapDomainBialgHom_single, ← hχ]
      change of k M ((MonoidHom.ofInjective hiχ)
        ((MonoidHom.ofInjective hiχ).symm m) : N).val = _
      rw [MulEquiv.apply_symm_apply]
      rfl
    have hsupport (x : A) : ↑(a.hom x).coeff.support ⊆ Set.range N.subtype := by
      intro m hm
      have hc : (a.hom x).coeff m ≠ 0 := Finsupp.mem_support_iff.mp hm
      let l := a.hom.toAlgHom.toLinearMap
      let p := (basis M k).coord m
      let L := (TensorProduct.rid k A).toLinearMap.comp (TensorProduct.map LinearMap.id (p.comp l))
      have hL : l.comp L = (TensorProduct.rid k (MonoidAlgebra k M)).toLinearMap.comp
          (TensorProduct.map LinearMap.id p ∘ₗ TensorProduct.map l l) := by
        apply TensorProduct.ext
        apply LinearMap.ext
        intro y
        apply LinearMap.ext
        intro z
        simp [L, TensorProduct.map_tmul, TensorProduct.rid_tmul]
      have hs : l (L (comul x)) = single m ((a.hom x).coeff m) := by
        have he := LinearMap.congr_fun hL (comul (R := k) x)
        simp only [LinearMap.comp_apply] at he
        rw [show TensorProduct.map l l (comul x) = comul (a.hom x) from
          CoalgHomClass.map_comp_comul_apply a.hom x] at he
        exact he.trans (LinearMap.congr_fun (slice_comul (k := k) m) (a.hom x))
      let y := ((a.hom x).coeff m)⁻¹ • L (comul (R := k) x)
      have hy : a.hom y = of k M m := by
        change l (_ • _) = _
        rw [map_smul, hs, smul_single, smul_eq_mul, inv_mul_cancel₀ hc]
        rfl
      have hy' : IsGroupLikeElem k y := by
        have h := isGroupLikeElem_of (R := k) (A := k) m
        rw [← hy] at h
        refine ⟨?_, ?_⟩
        · rw [← CoalgHomClass.counit_comp_apply a.hom]
          exact h.counit_eq_one
        · apply TensorProduct.map_injective_of_flat_flat l l ha ha
          rw [show TensorProduct.map l l (comul y) = comul (a.hom y) from
            CoalgHomClass.map_comp_comul_apply a.hom y, TensorProduct.map_tmul]
          exact h.comul_eq_tmul_self
      have he : χ ⟨y, hy'⟩ = m := of_injective ((hχ ⟨y, hy'⟩).trans hy)
      exact ⟨⟨m, ⟨⟨y, hy'⟩, he⟩⟩, rfl⟩
    have hsurj : Function.Surjective b := by
      intro x
      refine ⟨comapDomain N.subtype Subtype.val_injective (a.hom x), ha ?_⟩
      refine (DFunLike.congr_fun hb _).trans ?_
      exact mapDomain_comapDomain (hsupport x) Subtype.val_injective
    refine ⟨N, ⟨BialgEquiv.ofBijective b ⟨?_, hsurj⟩, hb⟩, ?_⟩
    · apply liftCharacters_injective
      exact (MonoidHom.ofInjective hiχ).symm.injective
    · rintro P ⟨e, he⟩
      ext m
      constructor
      · intro hm
        have h := DFunLike.congr_fun he (single ⟨m, hm⟩ (1 : k))
        change a.hom (e (single (⟨m, hm⟩ : P) (1 : k))) = _ at h
        rw [mapDomainBialgHom_single] at h
        let g : GroupLike k A := ⟨e (single (⟨m, hm⟩ : P) (1 : k)),
          (isGroupLikeElem_single_one (R := k) (A := k) _).map e.toBialgHom⟩
        exact ⟨g, of_injective ((hχ g).trans h)⟩
      · rintro ⟨g, rfl⟩
        obtain ⟨p, hp⟩ := isGroupLikeElem_iff_mem_range_of.mp (g.2.map e.symm.toBialgHom)
        have h := DFunLike.congr_fun he (of k P p)
        change a.hom (e (of k P p)) = mapDomainBialgHom k P.subtype (single p 1) at h
        rw [mapDomainBialgHom_single, hp] at h
        change a.hom (e (e.symm g.val)) = of k M p.val at h
        rw [e.apply_symm_apply, ← hχ] at h
        rw [of_injective h]
        exact p.property
  · rintro ⟨N, ⟨e, he⟩, _⟩
    have h := groupAlgebraMap_injective (k := k) N.subtype Subtype.val_injective
    rw [← he] at h
    exact Function.Injective.of_comp_right h e.surjective

theorem groupLikeElements : GroupLikeElements.{u} := by
  intro k M _ _ a
  rw [isGroupLikeElem_iff_mem_range_of]
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, hm, fun n hn =>
      single_left_injective (R := k) one_ne_zero (hn.trans hm.symm)⟩
  · rintro ⟨m, hm, _⟩
    exact ⟨m, hm⟩

theorem groupLikeSpanning : GroupLikeSpanning.{u} := by
  intro k _ A _
  constructor
  · intro h
    let l := liftCharacters (MonoidHom.id (GroupLike k A))
    have hs : Function.Surjective l := by
      change Function.Surjective l.toAlgHom.toLinearMap
      apply LinearMap.range_eq_top.mp
      apply top_unique
      rw [← h]
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      exact ⟨single g 1, liftCharacters_single _ g⟩
    let e := BialgEquiv.ofBijective l ⟨liftCharacters_injective _ Function.injective_id, hs⟩
    have hft : Algebra.FiniteType k (MonoidAlgebra k (GroupLike k A)) :=
      Algebra.FiniteType.equiv inferInstance e.symm.toAlgEquiv
    exact ⟨GroupLike k A, inferInstance, finiteType_iff_group_fg.mp hft, ⟨e⟩⟩
  · rintro ⟨M, _, _, ⟨e⟩⟩
    let b := (basis M k).map e.toAlgEquiv.toLinearEquiv
    apply top_unique
    rw [← b.span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    exact Submodule.subset_span ⟨⟨e (single m 1),
      (isGroupLikeElem_single_one (R := k) (A := k) m).map e.toBialgHom⟩, rfl⟩

end HopfMaps

section SchemeMaps

open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open Specs (IsImageFactorization IsSchemeKernel)

open private specGroupMap_comp specGroupMap_injective
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups
open private quotientRepresentsImage
  from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.SchemeImageQuotient

local notation "SpecHopf" => hopfSpec (CommRingCat.of k)

private def specIso {A B : HopfAlgebraCategory k} (e : A ≃ₐc[k] B) :
    specGroup B ≅ specGroup A :=
  (SpecHopf).mapIso (CommHopfAlgCat.isoMk e).op

private def hopfIso {A B : HopfAlgebraCategory k} (e : specGroup B ≅ specGroup A) :
    A ≃ₐc[k] B :=
  CommHopfAlgCat.ofIso ((hopfSpec.fullyFaithful (R := CommRingCat.of k)).preimageIso e).unop

private theorem spec_hopfIso_hom {A B : HopfAlgebraCategory k}
    (e : specGroup B ≅ specGroup A) :
    specGroupMap (CommHopfAlgCat.ofHom (hopfIso e).toBialgHom) = e.hom :=
  (hopfSpec.fullyFaithful (R := CommRingCat.of k)).map_preimage e.hom

theorem diagonalClosedSubgroups : DiagonalClosedSubgroups.{u} := by
  intro k M _ _ _ H i
  let A := groupAlgebra k M
  constructor
  · intro hi
    obtain ⟨J, ⟨hJ, e, he⟩, _⟩ := (closedSubgroupClassification k A H i).mp hi
    let := hJ
    let q := hopfQuotientMap A J
    obtain ⟨N, ⟨E, hE⟩, hN⟩ := (hopfQuotientClassification k M q).mp
      Ideal.Quotient.mk_surjective
    refine ⟨N, ⟨e ≪≫ specIso E, ?_⟩, ?_⟩
    · rw [Iso.trans_hom, Category.assoc]
      change e.hom ≫ specGroupMap (CommHopfAlgCat.ofHom E.toBialgHom) ≫
        specGroupMap (groupAlgebraMap k (QuotientGroup.mk' N)) = i
      rw [← specGroupMap_comp, ← he]
      rw [show groupAlgebraMap k (QuotientGroup.mk' N) ≫
        CommHopfAlgCat.ofHom E.toBialgHom = q from CommHopfAlgCat.hom_ext hE]
    · rintro P ⟨e', he'⟩
      let h := e.symm ≪≫ e'
      let E' := hopfIso h
      apply hN
      refine ⟨E', ?_⟩
      have hcomp : h.hom ≫ diagonalClosedInclusion k P = specGroupMap q := by
        change (e.inv ≫ e'.hom) ≫ diagonalClosedInclusion k P = _
        rw [Category.assoc, he', ← he, Iso.inv_hom_id_assoc]
      have hh := specGroupMap_injective (A := A) (B := hopfQuotient A J)
      have hmap : specGroupMap (groupAlgebraMap k (QuotientGroup.mk' P) ≫
          CommHopfAlgCat.ofHom E'.toBialgHom) = specGroupMap q := by
        rw [specGroupMap_comp, spec_hopfIso_hom]
        exact hcomp
      exact congrArg CommHopfAlgCat.Hom.hom (hh hmap)
  · rintro ⟨N, ⟨e, he⟩, _⟩
    rw [← he]
    have h := (hopfMapClosedImmersion k (groupAlgebraMap k (QuotientGroup.mk' N))).mpr
      (groupAlgebraMap_surjective _ QuotientGroup.mk_surjective)
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    have : IsIso e.hom.hom.hom.left := F.map_isIso e.hom
    have hN : IsClosedImmersion (diagonalClosedInclusion k N).hom.hom.left := h
    have hE : IsClosedImmersion e.hom.hom.hom.left := by infer_instance
    exact IsClosedImmersion.comp e.hom.hom.hom.left (diagonalClosedInclusion k N).hom.hom.left

/-- Every subgroup of a finitely generated abelian group is finitely generated. -/
theorem subgroupFG {M : Type u} [CommGroup M] [Group.FG M] (N : Subgroup M) : Group.FG N := by
  let : Module.Finite ℤ (Additive M) :=
    Module.Finite.iff_addGroup_fg.mpr (inferInstance : AddGroup.FG (Additive M))
  exact (Group.fg_iff_subgroup_fg N).mpr
    ((Subgroup.fg_iff_add_fg N).mpr
      ((Submodule.fg_iff_addSubgroup_fg N.toAddSubgroup.toIntSubmodule).mp
        (IsNoetherian.noetherian _)))

set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionProperties {M : Type u} [CommGroup M] [Group.FG M]
    (N : Subgroup M) :
    Flat (diagonalRestriction k N).hom.hom.left ∧
    Surjective (diagonalRestriction k N).hom.hom.left ∧
    LocallyOfFinitePresentation (diagonalRestriction k N).hom.hom.left ∧
    IsAffineHom (diagonalRestriction k N).hom.hom.left := by
  let : Group.FG N := subgroupFG N
  let a := groupAlgebraMap k N.subtype
  let r := CommRingCat.ofHom a.hom.toAlgHom.toRingHom
  have h := (flat_and_surjective_SpecMap_iff r).mpr
    (hopfFaithfulFlatness k a (groupAlgebraMap_injective _ Subtype.val_injective))
  have : IsNoetherianRing (MonoidAlgebra k N) := Algebra.FiniteType.isNoetherianRing k _
  have hft : r.hom.FiniteType := RingHom.FiniteType.of_comp_finiteType
    (f := algebraMap k (MonoidAlgebra k N)) (by
      rw [show r.hom.comp _ = algebraMap k (MonoidAlgebra k M) from a.hom.toAlgHom.comp_algebraMap]
      exact RingHom.finiteType_algebraMap.mpr inferInstance)
  exact ⟨h.1, h.2, (LocallyOfFinitePresentation.SpecMap_iff r).mpr
    (RingHom.FinitePresentation.of_finiteType.mp hft),
    inferInstanceAs (IsAffineHom (Spec.map r))⟩

set_option backward.isDefEq.respectTransparency.types false in
theorem diagonalFaithfullyFlatQuotients : DiagonalFaithfullyFlatQuotients.{u} := by
  intro k M _ _ _ H p
  change specGroup (groupAlgebra k M) ⟶ H.val at p
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  constructor
  · rintro ⟨hflat, hsurj⟩
    let A := coordinateHopf H
    let e : specGroup A ≅ H.val := (inducedFunctor Subtype.val).mapIso (coordinateHopfSpecIso H)
    let ff := hopfSpec.fullyFaithful (R := CommRingCat.of k)
    let a : A ⟶ groupAlgebra k M := (ff.preimage (p ≫ e.inv)).unop
    have ha : specGroupMap a = p ≫ e.inv := ff.map_preimage _
    have : IsIso e.inv.hom.hom.left := F.map_isIso e.inv
    let r := CommRingCat.ofHom a.hom.toAlgHom.toRingHom
    have hr : Spec.map r = F.map (p ≫ e.inv) := congrArg F.map ha
    rw [Functor.map_comp] at hr
    have hi : Function.Injective a.hom :=
      ((flat_and_surjective_SpecMap_iff r).mp (by
        rw [hr]
        exact ⟨MorphismProperty.comp_mem _ _ _ hflat (MorphismProperty.of_isIso _ _),
          MorphismProperty.comp_mem _ _ _ hsurj (MorphismProperty.of_isIso _ _)⟩)).injective
    obtain ⟨N, ⟨E, hE⟩, hN⟩ := (hopfSubalgebraClassification k M a).mp hi
    refine ⟨N, ⟨(specIso E).symm ≪≫ e, ?_⟩, ?_⟩
    · have h : diagonalRestriction k N = specGroupMap a ≫ (specIso E).hom := by
        change specGroupMap (groupAlgebraMap k N.subtype) =
          specGroupMap a ≫ specGroupMap (CommHopfAlgCat.ofHom E.toBialgHom)
        rw [← specGroupMap_comp]
        exact congrArg specGroupMap
          (show groupAlgebraMap k N.subtype = CommHopfAlgCat.ofHom E.toBialgHom ≫ a from
            CommHopfAlgCat.hom_ext hE.symm)
      rw [Iso.trans_hom, Iso.symm_hom, h, Category.assoc, Iso.hom_inv_id_assoc, ha,
        Category.assoc, Iso.inv_hom_id, Category.comp_id]
    · rintro P ⟨e', he'⟩
      let h := e ≪≫ e'.symm
      let E' := hopfIso h
      apply hN
      refine ⟨E', ?_⟩
      have hh := specGroupMap_injective (A := groupAlgebra k P) (B := groupAlgebra k M)
      have hmap : specGroupMap (CommHopfAlgCat.ofHom E'.toBialgHom ≫ a) =
          diagonalRestriction k P := by
        rw [specGroupMap_comp, spec_hopfIso_hom, ha]
        change (p ≫ e.inv) ≫ e.hom ≫ e'.inv = diagonalRestriction k P
        rw [Category.assoc, Iso.inv_hom_id_assoc, ← he', Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      exact congrArg CommHopfAlgCat.Hom.hom (hh hmap)
  · rintro ⟨N, ⟨e, he⟩, _⟩
    have h := restrictionProperties (k := k) N
    have : IsIso e.hom.hom.hom.left := F.map_isIso e.hom
    rw [← he]
    exact ⟨MorphismProperty.comp_mem _ _ _ h.1 (MorphismProperty.of_isIso _ _),
      MorphismProperty.comp_mem _ _ _ h.2.1 (MorphismProperty.of_isIso _ _)⟩

open MonoidAlgebra in
private theorem restrictionPushout {M : Type u} [CommGroup M] (N : Subgroup M) :
    let A := groupAlgebra k N
    let Q := groupAlgebra k (M ⧸ N)
    IsPushout (CommAlgCat.ofHom (groupAlgebraMap k N.subtype).hom.toAlgHom)
      (CommAlgCat.ofHom (hopfCounit A).hom.toAlgHom)
      (CommAlgCat.ofHom (groupAlgebraMap k (QuotientGroup.mk' N)).hom.toAlgHom)
      (CommAlgCat.ofHom (hopfUnit Q).hom.toAlgHom) := by
  apply IsPushout.mk'
  · apply CommAlgCat.hom_ext
    apply algHom_ext _ (Subsingleton.elim _ _)
    intro m
    change mapDomainBialgHom k (QuotientGroup.mk' N) (mapDomainBialgHom k N.subtype
      (single m 1)) = algebraMap k (MonoidAlgebra k (M ⧸ N)) (counit (R := k) (single m (1 : k)))
    rw [mapDomainBialgHom_single, mapDomainBialgHom_single,
      show QuotientGroup.mk' N (N.subtype m) = 1 from (QuotientGroup.eq_one_iff _).mpr m.property,
      (isGroupLikeElem_single_one (R := k) (A := k) m).counit_eq_one, map_one, MonoidAlgebra.one_def]
  · intro T f g hf _
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    obtain ⟨y, rfl⟩ := groupAlgebraMap_surjective (k := k) (QuotientGroup.mk' N) QuotientGroup.mk_surjective x
    exact ConcreteCategory.congr_hom hf y
  · intro T f g h
    let φ := (lift k T M).symm f.hom
    have hker : N ≤ φ.ker := by
      intro m hm
      have he := ConcreteCategory.congr_hom h (single (⟨m, hm⟩ : N) (1 : k))
      change f.hom (mapDomainBialgHom k N.subtype (single (⟨m, hm⟩ : N) (1 : k))) =
        g.hom (counit (R := k) (single (⟨m, hm⟩ : N) (1 : k))) at he
      rw [mapDomainBialgHom_single,
        (isGroupLikeElem_single_one (R := k) (A := k) (⟨m, hm⟩ : N)).counit_eq_one,
        map_one] at he
      exact he
    let l := lift k T (M ⧸ N) (QuotientGroup.lift N φ hker)
    refine ⟨CommAlgCat.ofHom l, ?_, CommAlgCat.hom_ext (Subsingleton.elim _ _)⟩
    apply CommAlgCat.hom_ext
    apply algHom_ext _ (Subsingleton.elim _ _)
    intro m
    change l (mapDomainBialgHom k (QuotientGroup.mk' N) (single m 1)) = f.hom (single m 1)
    rw [mapDomainBialgHom_single]
    exact congrArg (fun g : M ⧸ N →* T => g (QuotientGroup.mk' N m))
      ((lift k T (M ⧸ N)).symm_apply_apply (QuotientGroup.lift N φ hker))

private theorem restrictionKernel {M : Type u} [CommGroup M] (N : Subgroup M)
    (hc : IsClosedImmersion (diagonalClosedInclusion k N).hom.hom.left) :
    IsSchemeKernel (diagonalRestriction k N)
      ⟨specGroup (groupAlgebra k (M ⧸ N)), diagonalClosedInclusion k N, hc⟩ := by
  let A := groupAlgebra k N
  let Q := groupAlgebra k (M ⧸ N)
  let F := algSpec (CommRingCat.of k)
  have : PreservesLimitsOfSize.{u,u} F := AlgebraicGeometry.preservesLimitsOfSize_algSpec
  have h := (F.map_isPullback (restrictionPushout (k := k) N).op).flip
  change IsPullback (diagonalClosedInclusion k N).hom.hom (specGroupMap (hopfUnit Q)).hom.hom
    (diagonalRestriction k N).hom.hom (specGroupMap (hopfCounit A)).hom.hom at h
  let e : (specGroup (CommHopfAlgCat.of k k)).X ≅ 𝟙_ (SchemeOver k) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
      change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of k))
      rw [Spec.map_id, Category.comp_id])
  apply h.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp
  · exact (isTerminalTensorUnit (C := SchemeOver k)).hom_ext _ _
  · simp
  · apply Over.OverMorphism.ext
    change (specGroupMap (hopfCounit A)).hom.hom.left ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact (hopfSpecOperations k A).2.1.symm

theorem diagonalRestrictionKernelAndQuotient : DiagonalRestrictionKernelAndQuotient.{u} := by
  intro k M _ _ _ N
  have hc := (hopfMapClosedImmersion k (groupAlgebraMap k (QuotientGroup.mk' N))).mpr
    (groupAlgebraMap_surjective _ QuotientGroup.mk_surjective)
  let K : ClosedSubgroup (diagonalGroup k M).val :=
    ⟨specGroup (groupAlgebra k (M ⧸ N)), diagonalClosedInclusion k N, hc⟩
  have hK : IsSchemeKernel (diagonalRestriction k N) K := restrictionKernel N hc
  obtain ⟨hf, hs, hp, ha⟩ := restrictionProperties (k := k) N
  have hF : IsImageFactorization (diagonalRestriction k N) (diagonalRestriction k N)
      (𝟙 (specGroup (groupAlgebra k N))) := by
    refine ⟨Category.comp_id _, hf, hs, hp, ha, ?_⟩
    change IsClosedImmersion (𝟙 _)
    infer_instance
  exact ⟨hc, hf, hs, hp, hK, quotientRepresentsImage hF hK⟩


end SchemeMaps

section Characters

open MonoidAlgebra
open private specGroupMap_comp from MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.Affine.ClosedSubgroups

/-- The point comparison for the spectrum of a group algebra. -/
def groupAlgebraPointsIso (k : Type u) [Field k] (M : Type u) [CommGroup M] :
    (groupPointsFunctor k).obj (specGroup (groupAlgebra k M)) ≅ characterValuedPoints k M :=
  (hopfSpecPointIso (groupAlgebra k M)).symm ≪≫ convolutionCharacterIso M

private theorem pointsIso_spec (M : Type u) [CommGroup M] (R : TestAlgebra k)
    (f : MonoidAlgebra k M →ₐ[k] R) (m : M) :
    ((show M →* Rˣ from (groupAlgebraPointsIso k M).hom.app R
      ((hopfSpecPointIso (groupAlgebra k M)).hom.app R (toConv f))) m).val = f (single m 1) := by
  change ((show M →* Rˣ from ((hopfSpecPointIso (groupAlgebra k M)) ≪≫
    (groupAlgebraPointsIso k M)).hom.app R (toConv f)) m).val = _
  rw [show (hopfSpecPointIso (groupAlgebra k M)) ≪≫ (groupAlgebraPointsIso k M) =
    convolutionCharacterIso M from by simp [groupAlgebraPointsIso]]
  rfl

private theorem pointsIso_precompose {M N : Type u} [CommGroup M] [CommGroup N]
    (f : M →* N) (R : TestAlgebra k)
    (x : ((groupPointsFunctor k).obj (specGroup (groupAlgebra k N))).obj R) (m : M) :
    (show M →* Rˣ from (groupAlgebraPointsIso k M).hom.app R
      (((groupPointsFunctor k).map (specGroupMap (groupAlgebraMap k f))).app R x)) m =
      (show N →* Rˣ from (groupAlgebraPointsIso k N).hom.app R x) (f m) := by
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    ((hopfSpecPointIso (groupAlgebra k N)).hom.app R)).2 x
  let b := toConv (a.ofConv.comp (mapDomainBialgHom k f).toAlgHom)
  have h : ((groupPointsFunctor k).map (specGroupMap (groupAlgebraMap k f))).app R
      ((hopfSpecPointIso (groupAlgebra k N)).hom.app R a) =
      (hopfSpecPointIso (groupAlgebra k M)).hom.app R b := by
    apply Over.OverMorphism.ext
    exact (Spec.map_comp (CommRingCat.ofHom
      (mapDomainBialgHom k f).toAlgHom.toRingHom)
      (CommRingCat.ofHom a.ofConv.toRingHom)).symm
  change (show M →* Rˣ from (groupAlgebraPointsIso k M).hom.app R
    (((groupPointsFunctor k).map (specGroupMap (groupAlgebraMap k f))).app R
      ((hopfSpecPointIso (groupAlgebra k N)).hom.app R a))) m = _
  rw [h]
  apply Units.ext
  rw [pointsIso_spec]
  change a.ofConv (mapDomainBialgHom k f (single m 1)) = _
  rw [mapDomainBialgHom_single]
  exact (pointsIso_spec N R a.ofConv (f m)).symm

private def integerHomEquiv (U : Type*) [CommGroup U] :
    U ≃* (IntegerCharacters.{u} →* U) where
  toFun x := (zpowersHom U x).comp MulEquiv.ulift.toMonoidHom
  invFun f := f integerGenerator
  left_inv x := zpow_one x
  right_inv f := by
    apply MonoidHom.ext
    rintro ⟨m⟩
    exact (MonoidHom.apply_mint U (f.comp MulEquiv.ulift.symm.toMonoidHom) m).symm
  map_mul' x y := by
    ext m
    exact mul_zpow x y m.down.toAdd

private def integerPointsIso :
    characterValuedPoints k IntegerCharacters ≅ Specs.StandardGroups.multiplicativePoints k := by
  refine NatIso.ofComponents (fun _ => (integerHomEquiv _).symm.toGrpIso) ?_
  intro R S a
  apply GrpCat.ext
  intro f
  rfl

private def pointsFullyFaithful (k : Type u) [Field k] :
    ((inducedFunctor Subtype.val : AffineAlgebraicGroupCategory k ⥤ _) ⋙
      groupPointsFunctor k).FullyFaithful where
  preimage {G H} f := InducedCategory.homMk ((AffineAlgebraicGroup.groupHomEquiv G H).symm f)
  map_preimage {G H} f := (AffineAlgebraicGroup.groupHomEquiv G H).apply_symm_apply f
  preimage_map {G H} f := InducedCategory.hom_ext ((AffineAlgebraicGroup.groupHomEquiv G H).symm_apply_apply f.hom)

private instance : Group.FG IntegerCharacters.{u} :=
  let e : Multiplicative ℤ ≃* IntegerCharacters.{u} := MulEquiv.ulift.symm
  Group.fg_of_surjective (f := e.toMonoidHom) e.surjective

private def toMultiplicativeGroup (T : AffineAlgebraicGroup k)
    (t : (groupPointsFunctor k).obj T.val ≅ Specs.StandardGroups.multiplicativePoints k) :
    specGroup (groupAlgebra k IntegerCharacters) ≅ T.val :=
  let E := (groupAlgebraPointsIso k IntegerCharacters ≪≫ integerPointsIso) ≪≫ t.symm
  (inducedFunctor Subtype.val).mapIso ((pointsFullyFaithful k).preimageIso (X := diagonalGroup k IntegerCharacters) (Y := T) E)

private theorem toMultiplicativeGroup_points (T : AffineAlgebraicGroup k)
    (t : (groupPointsFunctor k).obj T.val ≅ Specs.StandardGroups.multiplicativePoints k) :
    (groupPointsFunctor k).map (toMultiplicativeGroup T t).hom ≫ t.hom =
      (groupAlgebraPointsIso k IntegerCharacters ≪≫ integerPointsIso).hom := by
  -- The point functor sends the lifted isomorphism to the comparison used to define it.
  change ((inducedFunctor Subtype.val : AffineAlgebraicGroupCategory k ⥤ _) ⋙
      groupPointsFunctor k).map ((pointsFullyFaithful k).preimage (X := diagonalGroup k IntegerCharacters) (Y := T)
      (((groupAlgebraPointsIso k IntegerCharacters ≪≫ integerPointsIso) ≪≫ t.symm).hom)) ≫
      t.hom = _
  have h := (pointsFullyFaithful k).map_preimage (X := diagonalGroup k IntegerCharacters)
    (Y := T) (((groupAlgebraPointsIso k IntegerCharacters ≪≫ integerPointsIso) ≪≫ t.symm).hom)
  refine (congrArg (fun f => f ≫ t.hom) h).trans ?_
  let b := (groupAlgebraPointsIso k IntegerCharacters ≪≫ integerPointsIso).hom
  change (b ≫ t.inv) ≫ t.hom = b
  calc
    _ = b ≫ (t.inv ≫ t.hom) := Category.assoc _ _ _
    _ = b := (congrArg (b ≫ ·) t.inv_hom_id).trans (Category.comp_id b)

private def charactersTo (T : AffineAlgebraicGroup k)
    (t : (groupPointsFunctor k).obj T.val ≅ Specs.StandardGroups.multiplicativePoints k)
    (M : Type u) [CommGroup M] :
    M ≃ (specGroup (groupAlgebra k M) ⟶ T.val) :=
  (integerHomEquiv M).toEquiv.trans <| mapDomainBialgHomEquiv.trans <|
    (show (MonoidAlgebra k IntegerCharacters →ₐc[k] MonoidAlgebra k M) ≃
        (op (groupAlgebra k M) ⟶ op (groupAlgebra k IntegerCharacters)) from
      { toFun := fun f => (CommHopfAlgCat.ofHom f).op
        invFun := fun f => f.unop.hom
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }).trans <|
    (hopfSpec.fullyFaithful (R := CommRingCat.of k)).homEquiv.trans <|
    (Iso.homCongr (Iso.refl _) (toMultiplicativeGroup T t))

private theorem charactersTo_def (T : AffineAlgebraicGroup k)
    (t : (groupPointsFunctor k).obj T.val ≅ Specs.StandardGroups.multiplicativePoints k)
    (M : Type u) [CommGroup M] (m : M) :
    charactersTo T t M m = specGroupMap (groupAlgebraMap k (integerHomEquiv M m)) ≫
      (toMultiplicativeGroup T t).hom := by
  change 𝟙 (specGroup (groupAlgebra k M)) ≫
    specGroupMap (groupAlgebraMap k (integerHomEquiv M m)) ≫ (toMultiplicativeGroup T t).hom = _
  rw [Category.id_comp]

private theorem charactersTo_natural (T : AffineAlgebraicGroup k)
    (t : (groupPointsFunctor k).obj T.val ≅ Specs.StandardGroups.multiplicativePoints k)
    {M N : Type u} [CommGroup M] [CommGroup N] (f : M →* N) (m : M) :
    specGroupMap (groupAlgebraMap k f) ≫ charactersTo T t M m =
      charactersTo T t N (f m) := by
  have hf : f.comp (integerHomEquiv M m) = integerHomEquiv N (f m) := by
    apply MonoidHom.ext
    intro z
    exact map_zpow f m z.down.toAdd
  have hmap : groupAlgebraMap k (integerHomEquiv M m) ≫ groupAlgebraMap k f =
      groupAlgebraMap k (integerHomEquiv N (f m)) := by
    apply CommHopfAlgCat.hom_ext
    change (mapDomainBialgHom k f).comp (mapDomainBialgHom k (integerHomEquiv M m)) = _
    rw [← mapDomainBialgHom_comp, hf]
    rfl
  rw [charactersTo_def, charactersTo_def, ← Category.assoc, ← specGroupMap_comp, hmap]

private theorem charactersTo_evaluation (T : AffineAlgebraicGroup k)
    (t : (groupPointsFunctor k).obj T.val ≅ Specs.StandardGroups.multiplicativePoints k)
    {M : Type u} [CommGroup M] (m : M) (R : TestAlgebra k)
    (x : ((groupPointsFunctor k).obj (specGroup (groupAlgebra k M))).obj R) :
    t.hom.app R (((groupPointsFunctor k).map (charactersTo T t M m)).app R x) =
      (show M →* Rˣ from (groupAlgebraPointsIso k M).hom.app R x) m := by
  rw [charactersTo_def, Functor.map_comp]
  have h := congrArg (fun a => a.app R) (toMultiplicativeGroup_points T t)
  have he := ConcreteCategory.congr_hom h
    (((groupPointsFunctor k).map (specGroupMap (groupAlgebraMap k (integerHomEquiv M m)))).app R x)
  exact he.trans ((pointsIso_precompose (integerHomEquiv M m) R x
    integerGenerator).trans (congrArg
    (show M →* Rˣ from (groupAlgebraPointsIso k M).hom.app R x) (zpow_one m)))

theorem characterRecovery : CharacterRecovery.{u} := by
  intro k _ T t
  refine ⟨(fun M => groupAlgebraPointsIso k M), (fun M => charactersTo T t M), ?_, ?_, ?_⟩
  · intro M _ _ R f x hx m
    have h : x = (hopfSpecPointIso (groupAlgebra k M)).hom.app R (toConv f) :=
      Over.OverMorphism.ext hx
    rw [h]
    exact pointsIso_spec M R f m
  · intro M _ _ m R x
    exact charactersTo_evaluation T t m R x
  · intro M N _ _ _ _ f m
    exact charactersTo_natural T t f m

theorem charactersAreInverse : CharactersAreInverse.{u} := by
  intro k _ T t
  let D := Specs.DiagonalizableGroups.diagonalFunctor k
  let : D.toEssImage.IsEquivalence := diagonalAntiequivalence k
  let E := D.toEssImage.asEquivalence
  let U : DiagonalizableGroup k ⥤ Specs.GroupScheme k :=
    D.essImage.ι ⋙ inducedFunctor Subtype.val
  let ε (G : DiagonalizableGroup k) :
      specGroup (groupAlgebra k (E.inverse.obj G).unop.obj) ≅ G.obj.val :=
    U.mapIso (E.counitIso.app G)
  let χ (G : DiagonalizableGroup k) :
      (E.inverse.obj G).unop.obj ≃ (G.obj.val ⟶ T.val) :=
    (charactersTo T t (E.inverse.obj G).unop.obj).trans ((ε G).homCongr (Iso.refl T.val))
  have hc (J : DiagonalizableGroup k) (x : (E.inverse.obj J).unop.obj) :
      χ J x = (ε J).inv ≫ charactersTo T t (E.inverse.obj J).unop.obj x := by
    change (ε J).inv ≫ charactersTo T t (E.inverse.obj J).unop.obj x ≫ 𝟙 T.val = _
    rw [Category.comp_id]
  refine ⟨E, rfl, χ, ?_, ?_⟩
  · intro G H f m
    let φ := (E.inverse.map f).unop.hom.hom
    have h := congrArg U.map (E.counitIso.inv.naturality f)
    simp only [Functor.map_comp] at h
    change f.hom.hom ≫ (ε H).inv = (ε G).inv ≫ specGroupMap (groupAlgebraMap k φ) at h
    change χ G (φ m) = f.hom.hom ≫ χ H m
    rw [hc, hc, ← charactersTo_natural T t φ m, ← Category.assoc, ← h, Category.assoc]
  · intro G m n R x
    let M := (E.inverse.obj G).unop.obj
    let y := ((groupPointsFunctor k).map (ε G).inv).app R x
    let ψ : M →* Rˣ := (groupAlgebraPointsIso k M).hom.app R y
    have he (z : M) : t.hom.app R (((groupPointsFunctor k).map (χ G z)).app R x) = ψ z := by
      rw [hc, Functor.map_comp]
      exact charactersTo_evaluation T t z R y
    change t.hom.app R (((groupPointsFunctor k).map (χ G (m * n))).app R x) =
      t.hom.app R (((groupPointsFunctor k).map (χ G m)).app R x) *
        t.hom.app R (((groupPointsFunctor k).map (χ G n)).app R x)
    rw [he, he, he, map_mul]
    rfl

theorem diagonalInteger : DiagonalInteger.{u} := by
  rintro k _ T ⟨t⟩
  exact ⟨toMultiplicativeGroup T t⟩

/-- The rank-one group agrees with the multiplicative group of the standard examples. -/
def multiplicativeGroupIso (k : Type u) [Field k] :
    specGroup (groupAlgebra k IntegerCharacters) ≅ (StandardGroups.multiplicativeGroup k).val :=
  toMultiplicativeGroup _ (StandardGroups.multiplicativeGroupPointsIso k)

theorem diagonalIntegerPowers : DiagonalIntegerPowers.{u} := by
  intro k ι _ _
  exact ⟨(specIso (MonoidAlgebra.toAdditiveBialgEquiv k k
    (Multiplicative (ι → ℤ)))).symm⟩

end Characters

section CyclicDecomposition

open MonoidAlgebra

private def extendRoot {R : Type*} [CommRing R] {n : ℕ} (x : rootsOfUnity n R) :
    Multiplicative (ZMod n) →* Rˣ :=
  (ZMod.lift n ⟨zmultiplesHom (Additive Rˣ) (Additive.ofMul x.val), by
    change Additive.ofMul (x.val ^ (n : ℤ)) = Additive.ofMul 1
    rw [zpow_natCast, x.property]⟩).toMultiplicative

private theorem extendRoot_one {R : Type*} [CommRing R] {n : ℕ} (x : rootsOfUnity n R) :
    extendRoot x (Multiplicative.ofAdd 1) = x.val := by
  change Additive.toMul (ZMod.lift (A := Additive Rˣ) n _ (1 : ZMod n)) = x.val
  rw [← Int.cast_one (R := ZMod n), ZMod.lift_coe]
  exact zpow_one x.val

private def cyclicHomEquiv (n : ℕ) (R : Type*) [CommRing R] :
    (Multiplicative (ZMod n) →* Rˣ) ≃* rootsOfUnity n R where
  toFun f := ⟨f (Multiplicative.ofAdd 1), by
    change f (Multiplicative.ofAdd 1) ^ n = 1
    rw [← map_pow, show (Multiplicative.ofAdd (1 : ZMod n)) ^ n = 1 from by
      apply Multiplicative.toAdd.injective
      change n • (1 : ZMod n) = 0
      simp [nsmul_eq_mul], map_one]⟩
  invFun := extendRoot
  left_inv f := by
    apply MonoidHom.ext
    intro y
    obtain ⟨m, hm⟩ := ZMod.intCast_surjective y.toAdd
    have hy : Multiplicative.ofAdd (1 : ZMod n) ^ m = y := by
      apply Multiplicative.toAdd.injective
      simpa [zsmul_eq_mul] using hm
    rw [← hy, map_zpow, map_zpow, extendRoot_one]
  right_inv x := Subtype.ext (extendRoot_one x)
  map_mul' _ _ := rfl

private def cyclicPointsIso (n : ℕ) :
    characterValuedPoints k (ULift.{u} (Multiplicative (ZMod n))) ≅ rootsOfUnityPoints k n := by
  let e (R : TestAlgebra k) :
      (ULift.{u} (Multiplicative (ZMod n)) →* Rˣ) ≃* rootsOfUnity n R :=
    { toFun := fun f => cyclicHomEquiv n R (f.comp MulEquiv.ulift.symm.toMonoidHom)
      invFun := fun x => ((cyclicHomEquiv n R).symm x).comp MulEquiv.ulift.toMonoidHom
      left_inv := by
        intro f
        dsimp only
        rw [MulEquiv.symm_apply_apply]
        rfl
      right_inv := by
        intro x
        exact (cyclicHomEquiv n R).apply_symm_apply x
      map_mul' := by
        intro f g
        apply Subtype.ext
        rfl }
  refine NatIso.ofComponents (fun R => (e R).toGrpIso) ?_
  intro R S a
  apply GrpCat.ext
  intro f
  apply Subtype.ext
  rfl

theorem diagonalCyclic : DiagonalCyclic.{u} := by
  intro k _ n _
  refine ⟨groupAlgebraPointsIso k _ ≪≫ cyclicPointsIso n, ?_⟩
  intro R f x hx
  have h : x = (hopfSpecPointIso (groupAlgebra k _)).hom.app R (toConv f) :=
    Over.OverMorphism.ext hx
  rw [h]
  exact pointsIso_spec (ULift.{u} (Multiplicative (ZMod n))) R f ⟨Multiplicative.ofAdd 1⟩

private def productHomEquiv (M N U : Type*) [Monoid M] [Monoid N] [CommMonoid U] :
    (M × N →* U) ≃* (M →* U) × (N →* U) where
  toFun f := (f.comp (MonoidHom.inl M N), f.comp (MonoidHom.inr M N))
  invFun f := f.1.coprod f.2
  left_inv := MonoidHom.coprod_unique
  right_inv _ := Prod.ext (MonoidHom.coprod_comp_inl ..) (MonoidHom.coprod_comp_inr ..)
  map_mul' _ _ := rfl

private def finiteProductHomEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : ι → Type*) [(i : ι) → Monoid (M i)] (U : Type*) [CommMonoid U] :
    ((∀ i, M i) →* U) ≃* (∀ i, M i →* U) where
  toFun f i := f.comp (MonoidHom.mulSingle M i)
  invFun f := MonoidHom.noncommPiCoprod f (fun _ _ _ _ _ => Commute.all _ _)
  left_inv f := by
    apply MonoidHom.pi_ext
    intro i x
    exact MonoidHom.noncommPiCoprod_mulSingle _ (hcomm := fun _ _ _ _ _ => Commute.all _ _) i x
  right_inv f := by
    funext i
    ext x
    exact MonoidHom.noncommPiCoprod_mulSingle _ (hcomm := fun _ _ _ _ _ => Commute.all _ _) i x
  map_mul' _ _ := rfl

private def intHomEquiv (U : Type*) [CommGroup U] :
    (Multiplicative ℤ →* U) ≃* U where
  toFun f := f (Multiplicative.ofAdd 1)
  invFun := zpowersHom U
  left_inv := (zpowersHom U).apply_symm_apply
  right_inv := (zpowersHom U).symm_apply_apply
  map_mul' _ _ := rfl

/-- The cyclic decomposition is realized by the product of the torus and roots-of-unity groups. -/
theorem diagonalCyclicDecomposition : DiagonalCyclicDecomposition.{u} := by
  classical
  intro k M _ _ _
  obtain ⟨κ, ι, _, _, p, hp, e, ⟨f⟩⟩ := CommGroup.equiv_free_prod_prod_multiplicative_zmod M
  let n j := p j ^ e j
  refine ⟨ι, κ, inferInstance, inferInstance, n, fun j => pow_pos (hp j).pos _, ⟨?_⟩⟩
  refine groupAlgebraPointsIso k M ≪≫ NatIso.ofComponents (fun R => ?_) ?_
  · let E : ((characterValuedPoints k M).obj R) ≃* ((splitProductPoints k ι κ n).obj R) :=
      (MulEquiv.ofBijective (MonoidHom.compHom' (P := Rˣ) f.symm.toMonoidHom)
        (by
          constructor
          · intro a b h
            apply MonoidHom.ext
            intro x
            have he := DFunLike.congr_fun h (f x)
            change a (f.symm (f x)) = b (f.symm (f x)) at he
            rwa [MulEquiv.symm_apply_apply] at he
          · intro a
            exact ⟨a.comp f.toMonoidHom, by ext; simp⟩)).trans <|
        (productHomEquiv _ _ Rˣ).trans <|
          MulEquiv.prodCongr
            ((finiteProductHomEquiv (fun _ : ι => Multiplicative ℤ) Rˣ).trans
              (MulEquiv.piCongrRight fun _ => intHomEquiv Rˣ))
            ((finiteProductHomEquiv (fun j : κ => Multiplicative (ZMod (n j))) Rˣ).trans
              (MulEquiv.piCongrRight fun j => cyclicHomEquiv (n j) R))
    exact E.toGrpIso
  · intro R S a
    apply GrpCat.ext
    intro f
    rfl

end CyclicDecomposition

end

end LinearAlgebraicGroups.DiagonalizableGroups
