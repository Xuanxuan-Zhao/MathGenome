import Specs.LinearAlgebraicGroups.Unipotent.Orthogonality
import LinearAlgebraicGroups.Unipotent.ExactOperations
import LinearAlgebraicGroups.Multiplicative.CharacterDescent
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Unipotent

open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup ClosedSubgroup)
open Specs.Unipotent
open Specs.CharacterDescent (IsMultiplicativeType IsDiagonalizable multiplicativeTypeSpecFunctor)

open private invariant_iff_coaction from LinearAlgebraicGroups.Unipotent.Criteria
open private presentation_of_map faithfullyFlat_of_presentation
  from LinearAlgebraicGroups.Unipotent.ExactOperations
open private groupPresentation from LinearAlgebraicGroups.Affine.SchemeImageQuotient
open private extendedGroupIso from LinearAlgebraicGroups.Affine.ClosedSubgroups

variable {k : Type u} [Field k]

private lemma multiplicativeType_iff_coordinates {G : AffineAlgebraicGroup k}
    {A : HopfAlgebraCategory k} (e : specGroup A ≅ G.val) :
    (multiplicativeTypeSpecFunctor k).essImage G ↔ IsMultiplicativeType A := by
  rw [CharacterDescent.multiplicativeTypeGroupCriterion, CharacterDescent.multiplicativeTypeOnSchemes]
  constructor
  · rintro ⟨E, _, _, _, M, ⟨d⟩⟩
    exact ⟨E, inferInstance, inferInstance, inferInstance, M,
      ⟨(groupBaseChange k E).mapIso e ≪≫ d⟩⟩
  · rintro ⟨E, _, _, _, M, ⟨d⟩⟩
    exact ⟨E, inferInstance, inferInstance, inferInstance, M,
      ⟨(groupBaseChange k E).mapIso e.symm ≪≫ d⟩⟩

private lemma diagonalizable_of_surjective {A B : HopfAlgebraCategory k} (a : A ⟶ B)
    (ha : Function.Surjective a.hom) (hA : IsDiagonalizable A) : IsDiagonalizable B := by
  obtain ⟨M, ⟨e⟩⟩ := hA
  let : Group.FG M.obj := M.property
  obtain ⟨N, ⟨d, _⟩, _⟩ :=
    (DiagonalizableGroups.hopfQuotientClassification k M.obj (e.hom ≫ a)).mp
      (ha.comp (ConcreteCategory.bijective_of_isIso e.hom).2)
  exact ⟨⟨CommGrpCat.of (M.obj ⧸ N), inferInstance⟩, ⟨CommHopfAlgCat.isoMk d⟩⟩

private lemma diagonalizable_of_injective {A B : HopfAlgebraCategory k} (a : A ⟶ B)
    (ha : Function.Injective a.hom) (hB : IsDiagonalizable B) : IsDiagonalizable A := by
  obtain ⟨M, ⟨e⟩⟩ := hB
  let : Group.FG M.obj := M.property
  obtain ⟨N, ⟨d, _⟩, _⟩ :=
    (DiagonalizableGroups.hopfSubalgebraClassification k M.obj (a ≫ e.inv)).mp
      ((ConcreteCategory.bijective_of_isIso e.inv).1.comp ha)
  let : Group.FG N := DiagonalizableGroups.subgroupFG N
  exact ⟨⟨CommGrpCat.of N, inferInstance⟩, ⟨CommHopfAlgCat.isoMk d⟩⟩

private lemma closedSubgroup_multiplicativeType {G : AffineAlgebraicGroup k}
    (N : ClosedSubgroup G.val) (hG : (multiplicativeTypeSpecFunctor k).essImage G) :
    (multiplicativeTypeSpecFunctor k).essImage (closedSubgroupAlgebraicGroup N) := by
  obtain ⟨A, B, a, eN, eG, h⟩ :=
    presentation_of_map (closedSubgroupAlgebraicGroup N) G N.inclusion
  change specGroup B ≅ N.group at eN
  change specGroupMap a ≫ eG.hom = eN.hom ≫ N.inclusion at h
  have hcomp : specGroupMap a = eN.hom ≫ N.inclusion ≫ eG.inv := by
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
      congrArg (fun f ↦ f ≫ eG.inv) h
  have hclosed : IsClosedImmersion (specGroupMap a).hom.hom.left := by
    rw [hcomp]
    let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
    change IsClosedImmersion (F.map (eN.hom ≫ N.inclusion ≫ eG.inv))
    rw [F.map_comp, F.map_comp]
    let : IsClosedImmersion (F.map N.inclusion) := N.isClosedImmersion
    let : IsIso (F.map eN.hom) := F.map_isIso eN.hom
    let : IsIso (F.map eG.inv) := F.map_isIso eG.inv
    infer_instance
  have ha := (hopfMapClosedImmersion k a).mp hclosed
  obtain ⟨E, _, _, hs, hE⟩ := (multiplicativeType_iff_coordinates eG).mp hG
  apply (multiplicativeType_iff_coordinates (G := closedSubgroupAlgebraicGroup N) eN).mpr
  refine ⟨E, inferInstance, inferInstance, hs, diagonalizable_of_surjective (extendedHopfMap E a)
    ?_ hE⟩
  exact LinearMap.lTensor_surjective E ha

private lemma quotient_multiplicativeType {G Q : AffineAlgebraicGroup k} (p : G.val ⟶ Q.val)
    (hp : Flat p.hom.hom.left) (hs : Surjective p.hom.hom.left)
    (hG : (multiplicativeTypeSpecFunctor k).essImage G) :
    (multiplicativeTypeSpecFunctor k).essImage Q := by
  obtain ⟨A, B, a, eG, eQ, h⟩ := presentation_of_map G Q p
  have ha := (faithfullyFlat_of_presentation p a eG eQ h hp hs).injective
  obtain ⟨E, _, _, hsE, hE⟩ := (multiplicativeType_iff_coordinates eG).mp hG
  apply (multiplicativeType_iff_coordinates eQ).mpr
  refine ⟨E, inferInstance, inferInstance, hsE, diagonalizable_of_injective (extendedHopfMap E a)
    ?_ hE⟩
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := E) a.hom.toLinearMap ha

private lemma groupLike_eq_one_of_invariants {A : HopfAlgebraCategory k}
    (h : HasInvariantVectors A) (a : GroupLike k A) : a.val = 1 := by
  let c : k →ₗ[k] k ⊗[k] A := (TensorProduct.mk k k A).flip a.val
  have hc (x : k) : c x = x ⊗ₜ[k] a.val := rfl
  let ρ : RightComodule k A k :=
    { coaction := c
      coassoc x := by
        rw [hc, LinearMap.rTensor_tmul, hc, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
          a.isGroupLikeElem_val.comul_eq_tmul_self]
      counit x := by
        rw [hc, LinearMap.lTensor_tmul, a.isGroupLikeElem_val.counit_eq_one,
          TensorProduct.rid_tmul, one_smul] }
  obtain ⟨x, hx, hfix⟩ := h k ρ
  have ht := (invariant_iff_coaction A ρ x).mp hfix
  change c x = _ at ht
  rw [hc] at ht
  have hy := congrArg (TensorProduct.lid k A) ht
  simp only [TensorProduct.lid_tmul] at hy
  have hxy := congrArg (fun z : A ↦ x⁻¹ • z) hy
  simpa only [smul_smul, inv_mul_cancel₀ hx, one_smul] using hxy

private lemma algebraMap_counit_of_diagonalizable {A : HopfAlgebraCategory k}
    (hD : IsDiagonalizable A) (hU : HasInvariantVectors A) (x : A) :
    algebraMap k A (Coalgebra.counit (R := k) x) = x := by
  obtain ⟨M, ⟨e⟩⟩ := hD
  let : Group.FG M.obj := M.property
  let d := CommHopfAlgCat.ofIso e
  let : Algebra.FiniteType k A := Algebra.FiniteType.equiv inferInstance d.toAlgEquiv
  have hspan := (DiagonalizableGroups.groupLikeSpanning k A).mpr
    ⟨M.obj, inferInstance, inferInstance, ⟨d⟩⟩
  have hmap : (Algebra.linearMap k A).comp (Coalgebra.counit (R := k)) = LinearMap.id := by
    apply LinearMap.ext_on hspan
    rintro _ ⟨a, rfl⟩
    change algebraMap k A (Coalgebra.counit (R := k) a.val) = a.val
    rw [a.isGroupLikeElem_val.counit_eq_one, map_one, groupLike_eq_one_of_invariants hU a]
  exact DFunLike.congr_fun hmap x

private lemma algebraMap_counit_descends (E : Type u) [Field E] [Algebra k E]
    {A : HopfAlgebraCategory k} (hD : IsDiagonalizable (extendedHopf E A))
    (hU : HasInvariantVectors (extendedHopf E A)) (x : A) :
    algebraMap k A (Coalgebra.counit (R := k) x) = x := by
  let B := extendedHopf E A
  let f : A →ₐ[k] E ⊗[k] A := Algebra.TensorProduct.includeRight
  apply Algebra.TensorProduct.includeRight_injective (A := E) (algebraMap k E).injective
  change f (algebraMap k A (Coalgebra.counit (R := k) x)) = f x
  rw [f.commutes]
  have hy := algebraMap_counit_of_diagonalizable hD hU (f x : B)
  change algebraMap E (E ⊗[k] A)
    (Coalgebra.counit (R := E) ((1 : E) ⊗ₜ[k] x)) = f x at hy
  rw [TensorProduct.counit_tmul, Bialgebra.counit_one, Algebra.smul_def, mul_one] at hy
  exact hy

private lemma isZero_spec_groundField :
    IsZero (specGroup (CommHopfAlgCat.of k k)) := by
  let T := specGroup (CommHopfAlgCat.of k k)
  let e : T.X ≅ 𝟙_ (SchemeOver k) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
      change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of k))
      rw [Spec.map_id, Category.comp_id])
  have ht := (isTerminalTensorUnit (C := SchemeOver k)).ofIso e.symm
  apply (IsZero.iff_id_eq_zero T).mpr
  exact (Grp.forget (SchemeOver k)).map_injective (ht.hom_ext _ _)

theorem unipotentMultiplicativeTypeTrivial : UnipotentMultiplicativeTypeTrivial.{u} := by
  intro k _ G hU hD
  obtain ⟨A, _, ⟨e⟩⟩ := groupPresentation G
  obtain ⟨E, _, _, _, hsplit⟩ := (multiplicativeType_iff_coordinates e).mp hD
  have eE : specGroup (extendedHopf E A) ≅ (baseChangedAlgebraicGroup E G).val :=
    extendedGroupIso E A ≪≫ (groupBaseChange k E).mapIso e
  have hUE := (unipotenceCriteria _ _ eE).1.mp ((unipotenceFieldExtension G).mpr hU)
  let d : A ≅ CommHopfAlgCat.of k k :=
    { hom := hopfCounit A
      inv := hopfUnit A
      hom_inv_id := by
        apply CommHopfAlgCat.hom_ext
        ext x
        exact algebraMap_counit_descends E hsplit hUE x
      inv_hom_id := by
        apply CommHopfAlgCat.hom_ext
        exact DFunLike.ext _ _ fun x ↦ (hopfCounit A).hom.toAlgHom.commutes x }
  exact isZero_spec_groundField.of_iso
    (e.symm ≪≫ ((hopfSpec (CommRingCat.of k)).mapIso d.op).symm)

theorem homFromUnipotentToMultiplicativeType : HomFromUnipotentToMultiplicativeType.{u} := by
  intro k _ U D f hU hD
  obtain ⟨I, p, i, ⟨rfl, hp, hs, _, _, hi⟩, _, _⟩ := schemeImageFactorization U D f
  let N : ClosedSubgroup D.val := ⟨I.val, i, hi⟩
  have hI := unipotentMultiplicativeTypeTrivial (closedSubgroupAlgebraicGroup N)
    (faithfullyFlatQuotientsUnipotent U _ p hp hs hU)
    (closedSubgroup_multiplicativeType N hD)
  change IsZero I.val at hI
  rw [hI.eq_zero_of_tgt p, zero_comp]

theorem homFromMultiplicativeTypeToUnipotent : HomFromMultiplicativeTypeToUnipotent.{u} := by
  intro k _ D U f hD hU
  obtain ⟨I, p, i, ⟨rfl, hp, hs, _, _, hi⟩, _, _⟩ := schemeImageFactorization D U f
  let N : ClosedSubgroup U.val := ⟨I.val, i, hi⟩
  have hI := unipotentMultiplicativeTypeTrivial (closedSubgroupAlgebraicGroup N)
    (closedSubgroupsUnipotent U N hU)
    (quotient_multiplicativeType p hp hs hD)
  change IsZero I.val at hI
  rw [hI.eq_zero_of_tgt p, zero_comp]

theorem unipotentMultiplicativeTypeIntersection :
    UnipotentMultiplicativeTypeIntersection.{u} := by
  intro k _ G U D P p q h hU hD
  let F := Grp.forget (SchemeOver k) ⋙ Over.forget (Spec (CommRingCat.of k))
  have hF := F.map_isPullback h
  let NU : ClosedSubgroup U.group :=
    ⟨P, p, MorphismProperty.of_isPullback (P := @IsClosedImmersion) hF.flip D.isClosedImmersion⟩
  let ND : ClosedSubgroup D.group :=
    ⟨P, q, MorphismProperty.of_isPullback (P := @IsClosedImmersion) hF U.isClosedImmersion⟩
  exact unipotentMultiplicativeTypeTrivial
    (closedSubgroupAlgebraicGroup (G := closedSubgroupAlgebraicGroup U) NU)
    (closedSubgroupsUnipotent (closedSubgroupAlgebraicGroup U) NU hU)
    (closedSubgroup_multiplicativeType ND hD)

end LinearAlgebraicGroups.Unipotent
