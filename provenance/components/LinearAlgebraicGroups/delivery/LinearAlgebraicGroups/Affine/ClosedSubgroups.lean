import Specs.LinearAlgebraicGroups.Affine.ClosedSubgroups
import LinearAlgebraicGroups.Affine.HopfAlgebras
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalCategory
open Coalgebra HopfAlgebra WithConv
open scoped TensorProduct CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups

noncomputable section

variable {k : Type u} [Field k]

abbrev ClosedSubgroup : Specs.ClosedSubgroupType.{u} := @Specs.ClosedSubgroup
abbrev IsNormalSubgroup : Specs.NormalSubgroupType.{u} := @Specs.IsNormalSubgroup
abbrev augmentationIdeal : Specs.AugmentationIdealType.{u} := @Specs.augmentationIdeal
abbrev kernelIdeal : Specs.KernelIdealType.{u} := @Specs.kernelIdeal
abbrev extendedIdeal : Specs.ExtendedIdealType.{u} := @Specs.extendedIdeal

open Specs (subgroupConjugation)

set_option maxHeartbeats 1200000

theorem textbookHopfIdeal : Specs.TextbookHopfIdeal.{u} := by
  intro k _ A I
  rw [Ideal.isHopfIdeal_iff, Submodule.isCoideal_iff_comul_mem, sup_comm]
  tauto

private theorem hopfMap_ker {A B : HopfAlgebraCategory k} (a : A ⟶ B)
    (ha : Function.Surjective a.hom) : (RingHom.ker a.hom.toAlgHom).IsHopfIdeal k := by
  let I := RingHom.ker a.hom.toAlgHom
  have hk : LinearMap.ker
      (Algebra.TensorProduct.map a.hom.toAlgHom a.hom.toAlgHom).toLinearMap =
      LinearMap.ker (TensorProduct.map (I.restrictScalars k).mkQ (I.restrictScalars k).mkQ) := by
    change (RingHom.ker (Algebra.TensorProduct.map a.hom.toAlgHom a.hom.toAlgHom)).restrictScalars k =
      (RingHom.ker (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I)
        (Ideal.Quotient.mkₐ k I))).restrictScalars k
    rw [Algebra.TensorProduct.map_ker _ _ ha ha,
      Algebra.TensorProduct.map_ker _ _ Ideal.Quotient.mk_surjective Ideal.Quotient.mk_surjective]
    have hq : RingHom.ker (Ideal.Quotient.mkₐ k I) = I := by
      ext x
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [hq]
  refine { toIsCoideal := ⟨?_, ?_⟩, antipode_mem := ?_ }
  · intro x hx
    rw [← CoalgHomClass.counit_comp_apply a.hom x, show a.hom x = 0 from hx, map_zero]
  · intro x hx
    change comul x ∈ LinearMap.ker (TensorProduct.map (I.restrictScalars k).mkQ
      (I.restrictScalars k).mkQ)
    rw [← hk]
    change TensorProduct.map a.hom.toAlgHom.toLinearMap a.hom.toAlgHom.toLinearMap (comul x) = 0
    exact (CoalgHomClass.map_comp_comul_apply a.hom x).trans (by
      rw [show a.hom x = 0 from hx, map_zero])
  · intro x hx
    change a.hom (antipode k x) = 0
    have h := DFunLike.congr_fun (hopfSpecMorphism k a).2 x
    change a.hom (antipode k x) = antipode k (a.hom x) at h
    rw [h, show a.hom x = 0 from hx, map_zero]

theorem hopfMapClosedImmersion : Specs.HopfMapClosedImmersion.{u} := by
  intro k _ A B a
  change IsClosedImmersion (Spec.map (CommRingCat.ofHom a.hom.toAlgHom.toRingHom)) ↔ _
  let r := CommRingCat.ofHom a.hom.toAlgHom.toRingHom
  change IsClosedImmersion (Spec.map r) ↔ Function.Surjective r
  refine ⟨fun h ↦ ?_, IsClosedImmersion.spec_of_surjective r⟩
  have hs := (IsClosedImmersion.isAffine_surjective_of_isAffine (Spec.map r)).2
  have he : (Scheme.ΓSpecIso _).inv ≫ (Spec.map r).appTop ≫ (Scheme.ΓSpecIso _).hom = r := by
    rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  rw [← he]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).hom).2.comp
    (hs.comp (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso _).inv).2)


private def liftHopfQuotient {A B : HopfAlgebraCategory k}
    (I : Ideal A) [I.IsHopfIdeal k] (a : A ⟶ B) (ha : ∀ x ∈ I, a.hom x = 0) :
    hopfQuotient A I ⟶ B := by
  let q := Bialgebra.Quotient.mkBialgHom (R := k) I
  let b := Ideal.Quotient.liftₐ I a.hom.toAlgHom ha
  have hb : b.comp q.toAlgHom = a.hom.toAlgHom := rfl
  refine CommHopfAlgCat.ofHom (BialgHom.ofAlgHom b ?_ ?_)
  · ext z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact (CoalgHomClass.counit_comp_apply a.hom x).trans
      (CoalgHomClass.counit_comp_apply q x).symm
  · apply AlgHom.ext
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    change (Algebra.TensorProduct.map b b) (comul (q x)) = comul (a.hom x)
    rw [← CoalgHomClass.map_comp_comul_apply q x]
    change (TensorProduct.map b.toLinearMap b.toLinearMap ∘ₗ
      TensorProduct.map q.toAlgHom.toLinearMap q.toAlgHom.toLinearMap) (comul x) = _
    rw [← TensorProduct.map_comp, ← AlgHom.comp_toLinearMap, hb]
    exact CoalgHomClass.map_comp_comul_apply a.hom x

private lemma specGroupMap_comp {A B C : HopfAlgebraCategory k} (a : A ⟶ B) (b : B ⟶ C) :
    specGroupMap (a ≫ b) = specGroupMap b ≫ specGroupMap a :=
  (hopfSpec (CommRingCat.of k)).map_comp b.op a.op

private lemma specGroupMap_injective {A B : HopfAlgebraCategory k} :
    Function.Injective (specGroupMap (A := A) (B := B)) :=
  fun _ _ h ↦ Quiver.Hom.op_inj (hopfSpec.fullyFaithful.map_injective h)

private lemma quotientIdeal_le_of_factor {A : HopfAlgebraCategory k}
    {I J : Ideal A} [I.IsHopfIdeal k] [J.IsHopfIdeal k]
    (r : specGroup (hopfQuotient A I) ⟶ specGroup (hopfQuotient A J))
    (hr : r ≫ specGroupMap (hopfQuotientMap A J) = specGroupMap (hopfQuotientMap A I)) :
    J ≤ I := by
  let m := hopfSpec.fullyFaithful.preimage r
  have hm := hopfSpec.fullyFaithful.map_preimage r
  have h : hopfQuotientMap A J ≫ m.unop = hopfQuotientMap A I := by
    apply specGroupMap_injective
    rw [specGroupMap_comp]
    exact (congrArg (· ≫ specGroupMap (hopfQuotientMap A J)) hm).trans hr
  intro x hx
  have he := ConcreteCategory.congr_hom h x
  change m.unop.hom (Ideal.Quotient.mk J x) = Ideal.Quotient.mk I x at he
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [← he, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

theorem closedSubgroupClassification : Specs.ClosedSubgroupClassification.{u} := by
  intro k _ A H i
  constructor
  · intro hi
    let : IsAffine (specGroup A).X.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
    have hH : IsAffine H.X.left :=
      (IsClosedImmersion.isAffine_surjective_of_isAffine i.hom.hom.left).1
    obtain ⟨B, ⟨e⟩⟩ := essImage_hopfSpec.mpr hH
    let f := hopfSpec.fullyFaithful.preimage (e.hom ≫ i)
    have hf := hopfSpec.fullyFaithful.map_preimage (e.hom ≫ i)
    let a := f.unop
    have ha : specGroupMap a = e.hom ≫ i := hf
    have hae : (specGroupMap a).hom.hom.left = e.hom.hom.hom.left ≫ i.hom.hom.left :=
      congrArg (fun m ↦ m.hom.hom.left) ha
    have hi' : IsClosedImmersion (specGroupMap a).hom.hom.left := by
      rw [hae]
      have : IsIso e.hom.hom.hom.left := by
        change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map e.hom)
        infer_instance
      infer_instance
    have hsur := (hopfMapClosedImmersion k a).mp hi'
    let I := RingHom.ker a.hom.toAlgHom
    have := hopfMap_ker a hsur
    let b := liftHopfQuotient I a (fun _ hx ↦ hx)
    have hb : Function.Bijective b.hom :=
      (Ideal.quotientKerAlgEquivOfSurjective (f := a.hom.toAlgHom) hsur).bijective
    let e₀ := (hopfSpec (CommRingCat.of k)).mapIso
      (CommHopfAlgCat.isoMk (BialgEquiv.ofBijective b.hom hb)).op
    let E : H ≅ specGroup (hopfQuotient A I) := e.symm ≪≫ e₀
    have hE : E.hom ≫ specGroupMap (hopfQuotientMap A I) = i := by
      change e.inv ≫ specGroupMap b ≫ specGroupMap (hopfQuotientMap A I) = i
      rw [← specGroupMap_comp]
      have hh : hopfQuotientMap A I ≫ b = a := by
        apply CommHopfAlgCat.hom_ext
        ext x
        rfl
      rw [hh, ha, Iso.inv_hom_id_assoc]
    refine ⟨I, ⟨inferInstance, E, hE⟩, ?_⟩
    rintro J ⟨hJ, F, hF⟩
    exact le_antisymm
      (quotientIdeal_le_of_factor (E.inv ≫ F.hom) (by rw [Category.assoc, hF, ← hE, Iso.inv_hom_id_assoc]))
      (quotientIdeal_le_of_factor (F.inv ≫ E.hom) (by rw [Category.assoc, hE, ← hF, Iso.inv_hom_id_assoc]))
  · rintro ⟨I, ⟨hI, e, rfl⟩, _⟩
    have : IsIso e.hom.hom.hom.left := by
      change IsIso (((Grp.forget (SchemeOver k)) ⋙ Over.forget _).map e.hom)
      infer_instance
    have : IsClosedImmersion (specGroupMap (hopfQuotientMap A I)).hom.hom.left :=
      (hopfMapClosedImmersion k _).mpr Ideal.Quotient.mk_surjective
    exact IsClosedImmersion.comp e.hom.hom.hom.left _

theorem hopfIdealSup : Specs.HopfIdealSup.{u} := by
  intro k _ A I J hI hJ
  rw [textbookHopfIdeal] at hI hJ ⊢
  have aux {M : Ideal A} (hM : M ≤ I ⊔ J) :
      LinearMap.range (LinearMap.rTensor A (M.restrictScalars k).subtype) ⊔
        LinearMap.range (LinearMap.lTensor A (M.restrictScalars k).subtype) ≤
      LinearMap.range (LinearMap.rTensor A ((I ⊔ J).restrictScalars k).subtype) ⊔
        LinearMap.range (LinearMap.lTensor A ((I ⊔ J).restrictScalars k).subtype) := by
    let g : M.restrictScalars k →ₗ[k] (I ⊔ J).restrictScalars k :=
      Submodule.inclusion hM
    apply sup_le_sup
    · rintro z ⟨y, rfl⟩
      exact ⟨LinearMap.rTensor A g y, by
        change ((LinearMap.rTensor A _).comp (LinearMap.rTensor A g)) y = _
        rw [← LinearMap.rTensor_comp]; rfl⟩
    · rintro z ⟨y, rfl⟩
      exact ⟨LinearMap.lTensor A g y, by
        change ((LinearMap.lTensor A _).comp (LinearMap.lTensor A g)) y = _
        rw [← LinearMap.lTensor_comp]; rfl⟩
  refine ⟨?_, ?_, ?_⟩ <;> intro x hx <;>
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx <;> rw [map_add]
  · exact add_mem (aux le_sup_left (hI.1 _ hy)) (aux le_sup_right (hJ.1 _ hz))
  · rw [hI.2.1 _ hy, hJ.2.1 _ hz, add_zero]
  · exact add_mem ((le_sup_left : I ≤ I ⊔ J) (hI.2.2 _ hy)) ((le_sup_right : J ≤ I ⊔ J) (hJ.2.2 _ hz))

/-- Arbitrary sums of Hopf ideals are Hopf ideals. -/
theorem hopfIdeal_iSup : Specs.HopfIdeal_iSup.{u, v} := by
  intro k _ A Index I hI
  let J : Ideal A := ⨆ i, I i
  let q := Ideal.Quotient.mkₐ k J
  have hε : J ≤ RingHom.ker (Bialgebra.counitAlgHom k A) :=
    iSup_le fun i _ hx ↦ Submodule.IsCoideal.counit_eq_zero (I := (I i).restrictScalars k) hx
  have hΔ : J ≤ RingHom.ker ((Algebra.TensorProduct.map q q).comp
      (Bialgebra.comulAlgHom k A)) := by
    refine iSup_le fun i x hx ↦ ?_
    let qi := Ideal.Quotient.mkₐ k (I i)
    let d := Ideal.Quotient.factorₐ k (le_iSup I i)
    have hd : d.comp qi = q := rfl
    have hzero : Algebra.TensorProduct.map qi qi (comul x) = 0 :=
      Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := (I i).restrictScalars k) hx
    change Algebra.TensorProduct.map q q (comul x) = 0
    rw [← hd, Algebra.TensorProduct.map_comp, AlgHom.comp_apply, hzero, map_zero]
  have hS : J ≤ Ideal.comap (antipodeAlgHom k A) J :=
    iSup_le fun i _ hx ↦ le_iSup I i (Ideal.IsHopfIdeal.antipode_mem (R := k) hx)
  exact
    { toIsCoideal := ⟨fun _ hx ↦ hε hx, fun _ hx ↦ hΔ hx⟩
      antipode_mem := fun _ hx ↦ hS hx }


private theorem hopfIdeal_map {A B : HopfAlgebraCategory k} (a : A ⟶ B)
    (I : Ideal A) [I.IsHopfIdeal k] : (I.map a.hom.toAlgHom).IsHopfIdeal k := by
  let J : Ideal B := I.map a.hom.toAlgHom
  let q := Ideal.Quotient.mkₐ k J
  have hz : ∀ x ∈ I, (q.comp a.hom.toAlgHom) x = 0 :=
    fun x hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx)
  let d := Ideal.Quotient.liftₐ I (q.comp a.hom.toAlgHom) hz
  have hd : d.comp (Ideal.Quotient.mkₐ k I) = q.comp a.hom.toAlgHom := rfl
  have hΔ : ∀ x ∈ I, (Algebra.TensorProduct.map q q) (comul (a.hom x)) = 0 := by
    intro x hx
    change (TensorProduct.map q.toLinearMap q.toLinearMap) (comul (a.hom x)) = 0
    rw [← CoalgHomClass.map_comp_comul_apply a.hom x]
    change (TensorProduct.map q.toLinearMap q.toLinearMap ∘ₗ
      TensorProduct.map a.hom.toAlgHom.toLinearMap a.hom.toAlgHom.toLinearMap) (comul x) = 0
    rw [← TensorProduct.map_comp, ← AlgHom.comp_toLinearMap, ← hd,
      AlgHom.comp_toLinearMap, TensorProduct.map_comp]
    change (TensorProduct.map d.toLinearMap d.toLinearMap)
      (TensorProduct.map (I.restrictScalars k).mkQ (I.restrictScalars k).mkQ (comul x)) = 0
    have hzero : (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I)
        (Ideal.Quotient.mkₐ k I)) (comul x) = 0 :=
      Submodule.IsCoideal.map_mkQ_comul_eq_zero (I := I.restrictScalars k) hx
    change (TensorProduct.map d.toLinearMap d.toLinearMap)
      ((Algebra.TensorProduct.map (Ideal.Quotient.mkₐ k I) (Ideal.Quotient.mkₐ k I)) (comul x)) = 0
    rw [hzero, map_zero]
  refine { toIsCoideal := ⟨?_, ?_⟩, antipode_mem := ?_ }
  · have h : J ≤ RingHom.ker (Bialgebra.counitAlgHom k B) := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      change counit (R := k) (a.hom x) = 0
      rw [CoalgHomClass.counit_comp_apply a.hom x]
      exact Submodule.IsCoideal.counit_eq_zero (I := I.restrictScalars k) hx
    exact fun _ hx ↦ h hx
  · have h : J ≤ RingHom.ker ((Algebra.TensorProduct.map q q).comp
        (Bialgebra.comulAlgHom k B)) :=
      Ideal.map_le_iff_le_comap.mpr (fun x hx ↦ hΔ x hx)
    exact fun _ hx ↦ h hx
  · have h : J ≤ Ideal.comap (antipodeAlgHom k B) J := by
      apply Ideal.map_le_iff_le_comap.mpr
      intro x hx
      change antipode k (a.hom x) ∈ J
      have hs := DFunLike.congr_fun (hopfSpecMorphism k a).2 x
      change a.hom (antipode k x) = antipode k (a.hom x) at hs
      rw [← hs]
      exact Ideal.mem_map_of_mem _ (Ideal.IsHopfIdeal.antipode_mem (R := k) hx)
    exact fun _ hx ↦ h hx

private theorem counit_surjective (B : HopfAlgebraCategory k) :
    Function.Surjective (Bialgebra.counitAlgHom k B) := by
  intro x
  exact ⟨algebraMap k B x, (Bialgebra.counitAlgHom k B).commutes x⟩

theorem hopfKernelIdeal : Specs.HopfKernelIdeal.{u} := by
  intro k _ A B a
  let e : B ⟶ CommHopfAlgCat.of k k := CommHopfAlgCat.ofHom (Bialgebra.counitBialgHom k B)
  have : (augmentationIdeal B).IsHopfIdeal k := hopfMap_ker e (counit_surjective B)
  exact hopfIdeal_map a (augmentationIdeal B)


/-- Base change of a surjective algebra map is a quotient by the extended kernel. -/
private lemma quotient_pushout {A B C : Type u}
    [CommRing A] [CommRing B] [CommRing C] [Algebra k A] [Algebra k B] [Algebra k C]
    (f : A →ₐ[k] B) (g : A →ₐ[k] C) (hf : Function.Surjective f)
    (J : Ideal C) (hJ : J = (RingHom.ker f).map g)
    (d : B →ₐ[k] C ⧸ J) (h : d.comp f = (Ideal.Quotient.mkₐ k J).comp g) :
    IsPushout (CommAlgCat.ofHom f) (CommAlgCat.ofHom g) (CommAlgCat.ofHom d)
      (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k J)) := by
  refine IsPushout.mk' (CommAlgCat.hom_ext h) ?_ ?_
  · intro T a b _ he
    apply CommAlgCat.hom_ext
    exact Ideal.Quotient.algHom_ext k (congrArg CommAlgCat.Hom.hom he)
  · intro T a b he
    have hz : J ≤ RingHom.ker b.hom := by
      rw [hJ, Ideal.map_le_iff_le_comap]
      intro x hx
      have hh := ConcreteCategory.congr_hom he x
      change a.hom (f x) = b.hom (g x) at hh
      change b.hom (g x) = 0
      rw [← hh, show f x = 0 from hx, map_zero]
    let l := Ideal.Quotient.liftₐ J b.hom (fun _ hx ↦ hz hx)
    refine ⟨CommAlgCat.ofHom l, CommAlgCat.hom_ext (AlgHom.ext ?_), rfl⟩
    intro x
    obtain ⟨y, rfl⟩ := hf x
    change l (d (f y)) = a.hom (f y)
    change l ((d.comp f) y) = _
    rw [h]
    exact (ConcreteCategory.congr_hom he y).symm

private lemma specGroup_isPullback {A B C D : HopfAlgebraCategory k}
    (f : A ⟶ B) (g : A ⟶ C) (b : B ⟶ D) (c : C ⟶ D)
    (h : IsPushout (CommAlgCat.ofHom f.hom.toAlgHom) (CommAlgCat.ofHom g.hom.toAlgHom)
      (CommAlgCat.ofHom b.hom.toAlgHom) (CommAlgCat.ofHom c.hom.toAlgHom)) :
    IsPullback (specGroupMap c) (specGroupMap b) (specGroupMap g) (specGroupMap f) := by
  apply IsPullback.of_map_of_faithful (Grp.forget (SchemeOver k))
  have hp := h.op
  let F := algSpec (CommRingCat.of k)
  have hF : PreservesLimitsOfSize.{u,u} F := by
    exact AlgebraicGeometry.preservesLimitsOfSize_algSpec (R := CommRingCat.of k)
  exact F.map_isPullback hp

theorem schemeKernel : Specs.SchemeKernel.{u} := by
  intro k _ A B a hi
  let J := kernelIdeal a
  let Q := hopfQuotient A J
  let q := hopfQuotientMap A J
  have hh : (hopfUnit Q).hom.toAlgHom.comp (hopfCounit B).hom.toAlgHom =
      q.hom.toAlgHom.comp a.hom.toAlgHom := by
    apply AlgHom.ext
    intro x
    have hx : x - algebraMap k B (counit x) ∈ augmentationIdeal B := by
      change Bialgebra.counitAlgHom k B (x - algebraMap k B (counit x)) = 0
      simp only [map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply,
        Bialgebra.counitAlgHom_apply, sub_self]
    have he := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem a.hom.toAlgHom hx)
    change q.hom (a.hom (x - algebraMap k B (counit x))) = 0 at he
    rw [map_sub, map_sub, AlgHomClass.commutes, AlgHomClass.commutes, sub_eq_zero] at he
    exact he.symm
  have h := specGroup_isPullback (hopfCounit B) a (hopfUnit Q) q
    (quotient_pushout (hopfCounit B).hom.toAlgHom a.hom.toAlgHom (counit_surjective B)
      J rfl (hopfUnit Q).hom.toAlgHom hh)
  refine ⟨h, ?_⟩
  have h' := (Grp.forget (SchemeOver k)).map_isPullback h
  change IsPullback (specGroupMap q).hom.hom (specGroupMap (hopfUnit Q)).hom.hom
    (specGroupMap a).hom.hom (specGroupMap (hopfCounit B)).hom.hom at h'
  let e : (specGroup (CommHopfAlgCat.of k k)).X ≅ 𝟙_ (SchemeOver k) :=
    Over.isoMk (Iso.refl (Spec (CommRingCat.of k))) (by
      change (𝟙 _) ≫ (𝟙 _) = Spec.map (𝟙 (CommRingCat.of k))
      rw [Spec.map_id, Category.comp_id])
  have ht := (isTerminalTensorUnit (C := SchemeOver k)).ofIso e.symm
  have hw : (specGroupMap q).hom.hom ≫ (specGroupMap a).hom.hom = 1 := by
    rw [h'.w, ht.hom_ext (specGroupMap (hopfUnit Q)).hom.hom 1, MonObj.one_comp]
  unfold Specs.IsNormalSubgroup
  have he : subgroupConjugation (specGroupMap q) ≫ (specGroupMap a).hom.hom =
      1 ≫ (specGroupMap (hopfCounit B)).hom.hom := by
    simp only [subgroupConjugation, MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hw,
      MonObj.comp_one, mul_one, mul_inv_cancel, MonObj.one_comp]
  exact ⟨h'.lift _ 1 he, h'.lift_fst _ _ _⟩

theorem subgroupIntersection : Specs.SubgroupIntersection.{u} := by
  intro k _ A I J hI hJ hij
  let q := hopfQuotientMap A (I ⊔ J)
  let pI := liftHopfQuotient I q (fun x hx ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr ((le_sup_left : I ≤ I ⊔ J) hx))
  let pJ := liftHopfQuotient J q (fun x hx ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr ((le_sup_right : J ≤ I ⊔ J) hx))
  refine ⟨specGroupMap pI, specGroupMap pJ, ?_, ?_⟩
  · apply specGroup_isPullback (hopfQuotientMap A J) (hopfQuotientMap A I) pJ pI
    refine IsPushout.mk' rfl ?_ ?_
    · intro T a b h _
      apply CommAlgCat.hom_ext
      apply Ideal.Quotient.algHom_ext k
      exact congrArg CommAlgCat.Hom.hom
        (congrArg (CommAlgCat.ofHom (Ideal.Quotient.mkₐ k J) ≫ ·) h)
    · intro T a b he
      let c := b.hom.comp (Ideal.Quotient.mkₐ k I)
      have hz : I ⊔ J ≤ RingHom.ker c := by
        refine sup_le (fun x hx ↦ ?_) (fun x hx ↦ ?_)
        · change b.hom (Ideal.Quotient.mk I x) = 0
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
        · have h := ConcreteCategory.congr_hom he x
          change a.hom (Ideal.Quotient.mk J x) = c x at h
          change c x = 0
          rw [← h, Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
      let l := Ideal.Quotient.liftₐ (I ⊔ J) c (fun x hx ↦ hz hx)
      refine ⟨CommAlgCat.ofHom l, ?_, ?_⟩ <;>
        apply CommAlgCat.hom_ext <;> apply Ideal.Quotient.algHom_ext k
      · exact (congrArg CommAlgCat.Hom.hom he).symm
      · rfl
  · rw [← specGroupMap_comp]
    rfl

private lemma monoQuotientInclusion {A : HopfAlgebraCategory k} (I : Ideal A)
    [I.IsHopfIdeal k] : Mono (specGroupMap (hopfQuotientMap A I)).hom.hom := by
  have : IsClosedImmersion (specGroupMap (hopfQuotientMap A I)).hom.hom.left :=
    (hopfMapClosedImmersion k _).mpr Ideal.Quotient.mk_surjective
  exact Over.mono_of_mono_left _

private def groupSchemeIsLimit {Index : Type v} [Category Index]
    {F : Index ⥤ Specs.GroupScheme k} {c : Cone F}
    (h : IsLimit ((Grp.forget (SchemeOver k)).mapCone c)) : IsLimit c :=
  isLimitOfReflects (Grp.forget₂Mon (SchemeOver k))
    (isLimitOfReflects (Mon.forget (SchemeOver k)) h)

theorem subgroupFamilyIntersection : Specs.SubgroupFamilyIntersection.{u, v} := by
  intro k _ A Index I hI
  classical
  let J : Ideal A := ⨆ i, I i
  have hJ : J.IsHopfIdeal k := hopfIdeal_iSup k A I
  let q := hopfQuotientMap A J
  let qᵢ (i : Index) := hopfQuotientMap A (I i)
  let p (i : Index) := specGroupMap (liftHopfQuotient (I i) q fun _ hx ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr (le_iSup I i hx))
  have hp (i : Index) : p i ≫ specGroupMap (qᵢ i) = specGroupMap q := by
    rw [← specGroupMap_comp]
    rfl
  let U := Grp.forget (SchemeOver k)
  let F := WidePullbackShape.wideCospan (specGroup A)
    (fun i ↦ specGroup (hopfQuotient A (I i))) (fun i ↦ specGroupMap (qᵢ i))
  let c : Cone F := WidePullbackCone.mk (specGroupMap q) p hp
  let s := U.mapCone c
  let adj := algΓAlgSpecAdjunction (CommRingCat.of k)
  let coordinates (X : SchemeOver k) (B : HopfAlgebraCategory k) (f : X ⟶ (specGroup B).X) :
      CommAlgCat.of k B ⟶ ((algΓ (CommRingCat.of k)).obj X).unop :=
    ((adj.homEquiv X (op (CommAlgCat.of k B))).symm f).unop
  have coordinates_comp {X : SchemeOver k} {B C : HopfAlgebraCategory k}
      (a : B ⟶ C) (f : X ⟶ (specGroup C).X) :
      coordinates X B (f ≫ (specGroupMap a).hom.hom) =
        CommAlgCat.ofHom a.hom.toAlgHom ≫ coordinates X C f :=
    congrArg Quiver.Hom.unop (adj.homEquiv_naturality_right_symm f
      (CommAlgCat.ofHom a.hom.toAlgHom).op)
  have liftBase (t : Cone (F ⋙ U)) : ∃ f : t.pt ⟶ s.pt, f ≫ s.π.app none = t.π.app none := by
    let a := coordinates t.pt A (t.π.app none)
    have ha : J ≤ RingHom.ker a.hom := by
      refine iSup_le fun i x hx ↦ ?_
      have hw : t.π.app (some i) ≫ (specGroupMap (qᵢ i)).hom.hom = t.π.app none :=
        t.w (WidePullbackShape.Hom.term i)
      have he := (congrArg (coordinates t.pt A) hw.symm).trans
        (coordinates_comp (qᵢ i) (t.π.app (some i)))
      change a.hom x = 0
      rw [show a = _ from he]
      change (coordinates t.pt (hopfQuotient A (I i)) (t.π.app (some i))).hom
        (Ideal.Quotient.mk (I i) x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
    let b : CommAlgCat.of k (hopfQuotient A J) ⟶ ((algΓ (CommRingCat.of k)).obj t.pt).unop :=
      ConcreteCategory.ofHom (C := CommAlgCat k) (Ideal.Quotient.liftₐ J a.hom fun _ hx ↦ ha hx)
    let f : t.pt ⟶ (specGroup (hopfQuotient A J)).X := (adj.homEquiv _ _) b.op
    refine ⟨f, ?_⟩
    have hinj : Function.Injective (coordinates t.pt A) := fun _ _ e ↦
      (adj.homEquiv t.pt (op (CommAlgCat.of k A))).symm.injective (Quiver.Hom.unop_inj e)
    apply hinj
    change coordinates t.pt A (f ≫ (specGroupMap q).hom.hom) = a
    rw [coordinates_comp q f, show coordinates t.pt (hopfQuotient A J) f = b from
      congrArg Quiver.Hom.unop (Equiv.symm_apply_apply _ _)]
    rfl
  have hs : IsLimit s := by
    refine ⟨fun t ↦ (liftBase t).choose, ?_, ?_⟩
    · intro t j
      cases j with
      | none => exact (liftBase t).choose_spec
      | some i =>
        let leg := WidePullbackShape.Hom.term i
        have : Mono ((F ⋙ U).map leg) := monoQuotientInclusion (I i)
        apply (cancel_mono ((F ⋙ U).map leg)).mp
        rw [Category.assoc, s.w leg, t.w leg, (liftBase t).choose_spec]
    · intro t f hf
      have : Mono (s.π.app none) := monoQuotientInclusion J
      exact (cancel_mono (s.π.app none)).mp
        ((hf none).trans (liftBase t).choose_spec.symm)
  exact ⟨hJ, p, hp, ⟨groupSchemeIsLimit hs⟩, ⟨hs⟩⟩

private lemma tensorQuotient_ker {A K : Type u} [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] (I : Ideal A) :
    RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k K) (Ideal.Quotient.mkₐ k I)) =
      I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) := by
  rw [Algebra.TensorProduct.lTensor_ker _ Ideal.Quotient.mk_surjective]
  congr 1
  ext x
  exact Ideal.Quotient.eq_zero_iff_mem

private lemma tensorMap_surjective {A B K : Type u} [Field K] [Algebra k K]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] (f : A →ₐ[k] B)
    (hf : Function.Surjective f) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id k K) f) :=
  Algebra.TensorProduct.map_surjective _ _ Function.surjective_id hf

private lemma extendedQuotientMap_ker (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (I : Ideal A) [I.IsHopfIdeal k] :
    RingHom.ker (extendedHopfMap K (hopfQuotientMap A I)).hom.toAlgHom = extendedIdeal K I := by
  change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id k K) (Ideal.Quotient.mkₐ k I)) =
    I.map (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A)
  exact tensorQuotient_ker (k := k) (K := K) I

private lemma extendedQuotientMap_surjective (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (I : Ideal A) [I.IsHopfIdeal k] :
    Function.Surjective (extendedHopfMap K (hopfQuotientMap A I)).hom :=
  tensorMap_surjective (K := K) (Ideal.Quotient.mkₐ k I) Ideal.Quotient.mk_surjective

theorem extendedHopfIdeal : Specs.ExtendedHopfIdeal.{u} := by
  intro k K _ _ _ A I hI
  change (extendedIdeal K I).IsHopfIdeal K
  exact extendedQuotientMap_ker K A I ▸
    hopfMap_ker _ (extendedQuotientMap_surjective K A I)

theorem extendedHopfQuotient : Specs.ExtendedHopfQuotient.{u} := by
  intro k K _ _ _ A I hI hI'
  let f := extendedHopfMap K (hopfQuotientMap A I)
  let J := extendedIdeal K I
  have hker : RingHom.ker f.hom.toAlgHom = J := extendedQuotientMap_ker K A I
  let b := liftHopfQuotient J f (fun x hx ↦ by
    change x ∈ RingHom.ker f.hom.toAlgHom
    exact hker.symm ▸ hx)
  have hb : Function.Bijective b.hom := by
    constructor
    · intro x y he
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      apply sub_eq_zero.mp
      rw [← map_sub]
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← hker, RingHom.mem_ker]
      change f.hom (x - y) = 0
      change f.hom x = f.hom y at he
      rw [map_sub, he, sub_self]
    · intro y
      obtain ⟨x, hx⟩ := extendedQuotientMap_surjective K A I y
      exact ⟨Ideal.Quotient.mk J x, hx⟩
  refine ⟨CommHopfAlgCat.isoMk (BialgEquiv.ofBijective b.hom hb), ?_⟩
  apply CommHopfAlgCat.hom_ext
  ext x
  rfl

private lemma augmentationIdeal_extension (K : Type u) [Field K] [Algebra k K]
    (B : HopfAlgebraCategory k) :
    extendedIdeal K (augmentationIdeal B) = augmentationIdeal (extendedHopf K B) := by
  have hc := Algebra.TensorProduct.lTensor_ker (A := K) (Bialgebra.counitAlgHom k B)
    (counit_surjective B)
  change (augmentationIdeal B).map (Algebra.TensorProduct.includeRight :
    B →ₐ[k] K ⊗[k] B) = RingHom.ker (Bialgebra.counitAlgHom K (K ⊗[k] B))
  rw [Bialgebra.TensorProduct.counitAlgHom_def]
  change (RingHom.ker (Bialgebra.counitAlgHom k B)).map
    (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B) =
    RingHom.ker ((Algebra.TensorProduct.rid k K K).toAlgHom.comp
    (Algebra.TensorProduct.map (AlgHom.id K K) (Bialgebra.counitAlgHom k B)))
  rw [← hc]
  ext x
  change (Algebra.TensorProduct.map (AlgHom.id k K) (Bialgebra.counitAlgHom k B)) x = 0 ↔
    (Algebra.TensorProduct.rid k K K)
      ((Algebra.TensorProduct.map (AlgHom.id K K) (Bialgebra.counitAlgHom k B)) x) = 0
  exact ⟨fun h ↦ h ▸ map_zero _, fun h ↦
    (Algebra.TensorProduct.rid k K K).injective (h.trans (map_zero _).symm)⟩

theorem extendedKernelIdeal : Specs.ExtendedKernelIdeal.{u} := by
  intro k K _ _ _ A B a
  let ιA : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  let ιB : B →ₐ[k] K ⊗[k] B := Algebra.TensorProduct.includeRight
  let f := Algebra.TensorProduct.map (AlgHom.id K K) a.hom.toAlgHom
  change ((augmentationIdeal B).map a.hom.toAlgHom).map ιA =
    (augmentationIdeal (extendedHopf K B)).map f
  rw [← augmentationIdeal_extension K B]
  change ((augmentationIdeal B).map a.hom.toAlgHom).map ιA =
    ((augmentationIdeal B).map ιB).map (f.restrictScalars k)
  rw [Ideal.map_mapₐ, Ideal.map_mapₐ]
  exact congrArg (fun g : B →ₐ[k] K ⊗[k] A ↦ (augmentationIdeal B).map g)
    (Algebra.TensorProduct.map_restrictScalars_comp_includeRight _ _).symm

theorem extendedIdealSup : Specs.ExtendedIdealSup.{u} := by
  intro k K _ _ _ A I J
  exact Ideal.map_sup (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) I J

theorem extendedIdeal_iSup : Specs.ExtendedIdeal_iSup.{u, v} := by
  intro k K _ _ _ A Index I
  exact Ideal.map_iSup (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A) I

theorem baseChangeSubgroupPullback : Specs.BaseChangeSubgroupPullback.{u} := by
  intro k K _ _ _ G H L P i j f g h
  apply IsPullback.of_map_of_faithful (Grp.forget (SchemeOver K))
  exact (baseChange k K).map_isPullback ((Grp.forget (SchemeOver k)).map_isPullback h)

theorem baseChangeSubgroupFamilyIntersection : Specs.BaseChangeSubgroupFamilyIntersection.{u, v} := by
  intro k K _ _ _ Index F c h
  obtain ⟨hc⟩ := h
  let U := Grp.forget (SchemeOver K)
  have hK : IsLimit (U.mapCone ((groupBaseChange k K).mapCone c)) :=
    isLimitOfPreserves (baseChange k K) hc
  exact ⟨⟨groupSchemeIsLimit hK⟩, ⟨hK⟩⟩

theorem baseChangeClosedSubgroup : Specs.BaseChangeClosedSubgroup.{u} := by
  intro k K _ _ _ G H i hi
  have hH : IsPullback (pullback.fst H.X.hom (fieldSpecMap k K))
      (pullback.snd H.X.hom (fieldSpecMap k K)) (i.hom.hom.left ≫ G.X.hom)
      (fieldSpecMap k K) := by
    rw [Over.w i.hom.hom]
    exact IsPullback.of_hasPullback _ _
  have hG := IsPullback.of_hasPullback G.X.hom (fieldSpecMap k K)
  let b := ((baseChange k K).map i.hom.hom).left
  have h₁ : b ≫ pullback.fst G.X.hom (fieldSpecMap k K) =
      pullback.fst H.X.hom (fieldSpecMap k K) ≫ i.hom.hom.left :=
    pullback.lift_fst _ _ _
  have h₂ : b ≫ pullback.snd G.X.hom (fieldSpecMap k K) =
      pullback.snd H.X.hom (fieldSpecMap k K) := pullback.lift_snd _ _ _
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion)
    (IsPullback.of_bot (h₂.symm ▸ hH) h₁.symm hG) hi


private lemma baseChange_conjugation (K : Type u) [Field K] [Algebra k K]
    {G H : Specs.GroupScheme k} (i : H ⟶ G) :
    let F := baseChange k K
    (prodComparisonIso F G.X H.X).inv ≫ F.map (subgroupConjugation i) =
      subgroupConjugation ((groupBaseChange k K).map i) := by
  let F := baseChange k K
  let e := prodComparisonIso F G.X H.X
  change e.inv ≫ F.map (subgroupConjugation i) = _
  have he₁ : e.inv ≫ F.map (fst G.X H.X) = fst (F.obj G.X) (F.obj H.X) := by
    rw [← CartesianMonoidalCategory.prodComparison_fst, ← prodComparisonIso_hom,
      Iso.inv_hom_id_assoc]
  have he₂ : e.inv ≫ F.map (snd G.X H.X) = snd (F.obj G.X) (F.obj H.X) := by
    rw [← CartesianMonoidalCategory.prodComparison_snd, ← prodComparisonIso_hom,
      Iso.inv_hom_id_assoc]
  unfold Specs.subgroupConjugation
  simp only [F.map_mul, F.map_inv', F.map_comp, MonObj.comp_mul, GrpObj.comp_inv,
    ← Category.assoc, he₁, he₂]
  rfl

theorem baseChangeNormalSubgroup : Specs.BaseChangeNormalSubgroup.{u} := by
  intro k K _ _ _ G H i hi
  obtain ⟨c, hc⟩ := hi
  let F := baseChange k K
  let e := prodComparisonIso F G.X H.X
  refine ⟨e.inv ≫ F.map c, ?_⟩
  change (e.inv ≫ F.map c) ≫ F.map i.hom.hom = _
  rw [Category.assoc, ← F.map_comp, hc]
  exact baseChange_conjugation K i

private lemma baseChangeProjection_effectiveEpi (K : Type u) [Field K] [Algebra k K]
    (X : SchemeOver k) : EffectiveEpi (pullback.fst X.hom (fieldSpecMap k K)) := by
  have hff : (algebraMap k K).FaithfullyFlat :=
    RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance
  obtain ⟨h₁, h₂⟩ := (flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom (algebraMap k K))).mpr hff
  have hFlat : Flat (pullback.fst X.hom (fieldSpecMap k K)) :=
    MorphismProperty.of_isPullback (P := @Flat)
      (IsPullback.of_hasPullback X.hom (fieldSpecMap k K)).flip h₁
  have hSurj : Surjective (pullback.fst X.hom (fieldSpecMap k K)) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback X.hom (fieldSpecMap k K)).flip h₂
  have hQC : QuasiCompact (fieldSpecMap k K) := by
    change QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    infer_instance
  have : QuasiCompact (pullback.fst X.hom (fieldSpecMap k K)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (IsPullback.of_hasPullback X.hom (fieldSpecMap k K)).flip hQC
  infer_instance

private lemma baseChangeProjection_naturality (K : Type u) [Field K] [Algebra k K]
    {X Y : SchemeOver k} (f : X ⟶ Y) :
    ((baseChange k K).map f).left ≫ pullback.fst Y.hom (fieldSpecMap k K) =
      pullback.fst X.hom (fieldSpecMap k K) ≫ f.left :=
  pullback.lift_fst _ _ _

private lemma factor_of_baseChange (K : Type u) [Field K] [Algebra k K]
    {X Y Z : SchemeOver k} (f : X ⟶ Z) (i : Y ⟶ Z) [Mono i.left]
    (c : (baseChange k K).obj X ⟶ (baseChange k K).obj Y)
    (hc : c ≫ (baseChange k K).map i = (baseChange k K).map f) :
    ∃ d : X ⟶ Y, d ≫ i = f := by
  let p := pullback.fst X.hom (fieldSpecMap k K)
  let b := c.left ≫ pullback.fst Y.hom (fieldSpecMap k K)
  have hp : EffectiveEpi p := baseChangeProjection_effectiveEpi K X
  have hb : b ≫ i.left = p ≫ f.left := by
    rw [Category.assoc, ← baseChangeProjection_naturality K i, ← Category.assoc]
    change (c ≫ (baseChange k K).map i).left ≫ _ = _
    rw [hc, baseChangeProjection_naturality]
  have hb' {W : Scheme.{u}} (g₁ g₂ : W ⟶ _) (he : g₁ ≫ p = g₂ ≫ p) :
      g₁ ≫ b = g₂ ≫ b := by
    apply (cancel_mono i.left).mp
    calc
      (g₁ ≫ b) ≫ i.left = (g₁ ≫ p) ≫ f.left := by rw [Category.assoc, hb, Category.assoc]
      _ = (g₂ ≫ p) ≫ f.left := by rw [he]
      _ = (g₂ ≫ b) ≫ i.left := (Category.assoc _ _ _).trans
        ((congrArg (g₂ ≫ ·) hb.symm).trans (Category.assoc _ _ _).symm)
  let d := EffectiveEpi.desc p b hb'
  have hd : d ≫ i.left = f.left := by
    rw [← cancel_epi p, ← Category.assoc, EffectiveEpi.fac]
    exact hb
  refine ⟨Over.homMk d ?_, Over.OverMorphism.ext hd⟩
  rw [← Over.w i, ← Category.assoc, hd, Over.w f]

set_option backward.isDefEq.respectTransparency false in
theorem baseChangeNormalSubgroupIff : Specs.BaseChangeNormalSubgroupIff.{u} := by
  intro k K _ _ _ G H i hi
  refine ⟨?_, baseChangeNormalSubgroup k K i⟩
  rintro ⟨c, hc⟩
  let F := baseChange k K
  let e := prodComparisonIso F G.X H.X
  let X := G.X ⊗ H.X
  have hm : Mono i.hom.hom.left := inferInstance
  let d : F.obj X ⟶ F.obj H.X := e.hom ≫ c
  refine factor_of_baseChange K (X := X) (subgroupConjugation i) i.hom.hom d ?_
  calc
    (e.hom ≫ c) ≫ F.map i.hom.hom = e.hom ≫ (c ≫ F.map i.hom.hom) := Category.assoc _ _ _
    _ = e.hom ≫ subgroupConjugation ((groupBaseChange k K).map i) :=
      congrArg (fun g : F.obj G.X ⊗ F.obj H.X ⟶ F.obj G.X ↦ e.hom ≫ g) hc
    _ = e.hom ≫ e.inv ≫ F.map (subgroupConjugation i) :=
      congrArg (e.hom ≫ ·) (baseChange_conjugation K i).symm
    _ = F.map (subgroupConjugation i) := Iso.hom_inv_id_assoc e _

set_option backward.isDefEq.respectTransparency false in
private def extendedSpecIso (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) :
    (specGroup (extendedHopf K A)).X ≅ ((groupBaseChange k K).obj (specGroup A)).X := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let b := fieldSpecMap k K
  let e := (pullbackSpecIso k K A).symm ≪≫ pullbackSymmetry b a
  refine Over.isoMk e ?_
  change ((pullbackSpecIso k K A).inv ≫ (pullbackSymmetry b a).hom) ≫
    pullback.snd a b = Spec.map (CommRingCat.ofHom (algebraMap K (K ⊗[k] A)))
  rw [Category.assoc, pullbackSymmetry_hom_comp_snd]
  exact pullbackSpecIso_inv_fst' k K A

set_option backward.isDefEq.respectTransparency false in
private lemma extendedSpecIso_hom_fst (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) :
    (extendedSpecIso K A).hom.left ≫ pullback.fst (specGroup A).X.hom (fieldSpecMap k K) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : A →ₐ[k] K ⊗[k] A).toRingHom) := by
  let a := Spec.map (CommRingCat.ofHom (algebraMap k A))
  let b := fieldSpecMap k K
  change ((pullbackSpecIso k K A).inv ≫ (pullbackSymmetry b a).hom) ≫
    pullback.fst a b = _
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
  exact pullbackSpecIso_inv_snd k K A

section ConvolutionRestriction

variable {k K A T : Type u} [Field k] [Field K] [Algebra k K]
  [CommRing A] [HopfAlgebra k A] [CommRing T] [Algebra K T] [Algebra k T] [IsScalarTower k K T]

private def restrictConvolution (f : WithConv ((K ⊗[k] A) →ₐ[K] T)) : WithConv (A →ₐ[k] T) :=
  toConv ((f.ofConv.restrictScalars k).comp Algebra.TensorProduct.includeRight)

private theorem restrictConvolution_mul (f g : WithConv ((K ⊗[k] A) →ₐ[K] T)) :
    restrictConvolution (f * g) = restrictConvolution f * restrictConvolution g := by
  apply ofConv_injective
  apply AlgHom.ext
  intro x
  let i : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
  let i' := i.toRingHom
  have hi : i'.comp (algebraMap k A) = (algebraMap K (K ⊗[k] A)).comp (algebraMap k K) := by
    ext x
    rw [← IsScalarTower.algebraMap_eq]
    exact i.commutes x
  let M := Algebra.TensorProduct.mapRingHom (algebraMap k K) i' i' hi hi
  have hΔ : comul (R := K) (i x) = M (comul (R := k) x) :=
    DFunLike.congr_fun (Bialgebra.comul_includeRight (R := k) (A := K) (B := A)) x
  have hl : ∀ z : A ⊗[k] A,
      Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ ↦ .all ..) (M z) =
      Algebra.TensorProduct.lift (restrictConvolution f).ofConv (restrictConvolution g).ofConv
        (fun _ _ ↦ .all ..) z := by
    intro z
    induction z with
    | tmul a b =>
      rw [show M (a ⊗ₜ[k] b) = i a ⊗ₜ[K] i b from Algebra.TensorProduct.mapRingHom_tmul ..]
      simp only [Algebra.TensorProduct.lift_tmul]
      rfl
    | add a b ha hb => simp only [map_add, ha, hb]
  change (f * g) (i x) = (restrictConvolution f * restrictConvolution g) x
  simp only [AlgHom.convMul_apply, hΔ]
  exact hl _

end ConvolutionRestriction

set_option backward.isDefEq.respectTransparency false in
private theorem extendedSpecIso_preservesMul (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) (R : TestAlgebra K)
    (p q : Points (specGroup (extendedHopf K A)).X R) :
    (p * q) ≫ (extendedSpecIso K A).hom =
      ((p ≫ (extendedSpecIso K A).hom) *
        (q ≫ (extendedSpecIso K A).hom) : Points ((groupBaseChange k K).obj (specGroup A)).X R) := by
  let G := specGroup A
  let E := specGroup (extendedHopf K A)
  let S := (restrictTestAlgebra k K).obj R
  let : Algebra k R := ((algebraMap K R).comp (algebraMap k K)).toAlgebra
  let : IsScalarTower k K R := IsScalarTower.of_algebraMap_eq' rfl
  let e₁ : WithConv ((K ⊗[k] A) →ₐ[K] R) ≃* Points E.X R :=
    Spec.mapMulEquiv (R := K) (S := K ⊗[k] A) (T := R)
  let e₂ : WithConv (A →ₐ[k] R) ≃* Points G.X S :=
    Spec.mapMulEquiv (R := k) (S := A) (T := R)
  let e₃ := baseChangePointGroupEquiv K G R
  have he (f : WithConv ((K ⊗[k] A) →ₐ[K] R)) :
      e₃ (e₁ f ≫ (extendedSpecIso K A).hom) = e₂ (restrictConvolution f) := by
    apply Over.OverMorphism.ext
    let i : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
    change (Spec.map (CommRingCat.ofHom f.ofConv.toRingHom) ≫
      (extendedSpecIso K A).hom.left) ≫ pullback.fst G.X.hom (fieldSpecMap k K) =
      Spec.map (CommRingCat.ofHom (f.ofConv.toRingHom.comp i.toRingHom))
    rw [Category.assoc, extendedSpecIso_hom_fst]
    exact (Spec.map_comp (CommRingCat.ofHom i.toRingHom)
      (CommRingCat.ofHom f.ofConv.toRingHom)).symm
  obtain ⟨f, rfl⟩ := e₁.surjective p
  obtain ⟨g, rfl⟩ := e₁.surjective q
  apply e₃.injective
  rw [← e₁.map_mul, e₃.map_mul, he, he, he, restrictConvolution_mul, e₂.map_mul]

open private hom_ext_of_points from LinearAlgebraicGroups.Affine.GroupSchemes in
private theorem isMonHom_of_affinePoints {E G : Specs.GroupScheme k} (f : E.X ⟶ G.X)
    (hE : IsAffine E.X.left)
    (hm : ∀ (R : TestAlgebra k) (p q : Points E.X R),
      (p * q) ≫ f = (p ≫ f) * (q ≫ f)) : IsMonHom f := by
  constructor
  · apply hom_ext_of_points (X := 𝟙_ (SchemeOver k)) (by
      change IsAffine (Spec (CommRingCat.of k))
      infer_instance)
    intro R p
    rw [show p = toUnit ((testSpec k).obj (op R)) from toUnit_unique _ _]
    change (1 : Points E.X R) ≫ f = (1 : Points G.X R)
    have h := hm R 1 1
    rw [one_mul] at h
    exact mul_eq_left.mp h.symm
  · apply hom_ext_of_points (X := E.X ⊗ E.X) (by
      change IsAffine (pullback E.X.hom E.X.hom)
      infer_instance)
    intro R p
    let x := p ≫ fst E.X E.X
    let y := p ≫ snd E.X E.X
    calc
      p ≫ μ[E.X] ≫ f = (x * y) ≫ f := by simp [x, y, CategoryTheory.Hom.mul_def]
      _ = (x ≫ f) * (y ≫ f) := hm R x y
      _ = p ≫ (f ⊗ₘ f) ≫ μ[G.X] := by
        have hl : lift (x ≫ f) (y ≫ f) = p ≫ (f ⊗ₘ f) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp [x, y]
        simp only [CategoryTheory.Hom.mul_def, hl, Category.assoc]

private theorem extendedSpecIso_isMonHom (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) : IsMonHom (extendedSpecIso K A).hom :=
  isMonHom_of_affinePoints (E := specGroup (extendedHopf K A))
    (G := (groupBaseChange k K).obj (specGroup A)) (extendedSpecIso K A).hom
    (inferInstanceAs (IsAffine (Spec (CommRingCat.of (K ⊗[k] A)))))
    (extendedSpecIso_preservesMul K A)

set_option backward.isDefEq.respectTransparency false in
private lemma extendedSpecIso_natural (K : Type u) [Field K] [Algebra k K]
    {A B : HopfAlgebraCategory k} (a : A ⟶ B) :
    (specGroupMap (extendedHopfMap K a)).hom.hom ≫ (extendedSpecIso K A).hom =
      (extendedSpecIso K B).hom ≫ (baseChange k K).map (specGroupMap a).hom.hom := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ pullback.fst _ _ = (_ ≫ _) ≫ pullback.fst _ _
    rw [Category.assoc, Category.assoc, baseChangeProjection_naturality,
      extendedSpecIso_hom_fst, ← Category.assoc, extendedSpecIso_hom_fst]
    let iA : A →ₐ[k] K ⊗[k] A := Algebra.TensorProduct.includeRight
    let iB : B →ₐ[k] K ⊗[k] B := Algebra.TensorProduct.includeRight
    let f := Algebra.TensorProduct.map (AlgHom.id K K) a.hom.toAlgHom
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫ Spec.map (CommRingCat.ofHom iA.toRingHom) =
      Spec.map (CommRingCat.ofHom iB.toRingHom) ≫ Spec.map (CommRingCat.ofHom a.hom.toAlgHom.toRingHom)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  · exact (Over.w _).trans (Over.w _).symm


private def extendedGroupIso (K : Type u) [Field K] [Algebra k K]
    (A : HopfAlgebraCategory k) :
    specGroup (extendedHopf K A) ≅ (groupBaseChange k K).obj (specGroup A) :=
  letI := extendedSpecIso_isMonHom K A
  Grp.mkIso' (extendedSpecIso K A)

set_option backward.isDefEq.respectTransparency false in
theorem baseChangeQuotientInclusion : Specs.BaseChangeQuotientInclusion.{u} := by
  intro k K _ _ _ A I hI hJ
  obtain ⟨e, he⟩ := extendedHopfQuotient k K A I
  let e' := (hopfSpec (CommRingCat.of K)).mapIso e.op
  refine ⟨extendedGroupIso K A, e'.symm ≪≫ extendedGroupIso K (hopfQuotient A I), ?_⟩
  apply Grp.hom_ext
  have h := congrArg (fun f ↦ (specGroupMap f).hom.hom) he
  rw [specGroupMap_comp] at h
  have hn := extendedSpecIso_natural K (hopfQuotientMap A I)
  change _ ≫ (extendedSpecIso K A).hom =
    e'.inv.hom.hom ≫ (extendedSpecIso K (hopfQuotient A I)).hom ≫
      (baseChange k K).map (specGroupMap (hopfQuotientMap A I)).hom.hom
  rw [← hn]
  change _ ≫ _ = e'.inv.hom.hom ≫ _
  change e'.hom.hom.hom ≫
    (specGroupMap (hopfQuotientMap (extendedHopf K A) (extendedIdeal K I))).hom.hom =
    (specGroupMap (extendedHopfMap K (hopfQuotientMap A I))).hom.hom at h
  rw [← h, Category.assoc]
  exact (Iso.inv_hom_id_assoc ((Grp.forget (SchemeOver K)).mapIso e') _).symm

end
end LinearAlgebraicGroups
