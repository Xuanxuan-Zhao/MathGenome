import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.KoszulRelativeDual
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.KoszulCochainResolution
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CoinductionComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ModelQuasiIsoInvariance
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.KInjectiveReplacement
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedCoinduction
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.RedundantGenerators
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.SelfDuality
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Koszul.NullHomotopy
import Mathlib.Algebra.Homology.Embedding.ExtendHomotopy
import Batteries.Tactic.OpenPrivate

/-! The relative dual of a regular quotient. -/

noncomputable section

namespace DerivedFormalization.KoszulRelativeDual

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open CochainComplex.HomComplex
open ComplexShape (embeddingDownNat)
open AdvCommAlg.Koszul
open Specs.DerivedFormalization.KoszulRelativeDual hiding relativeDual
open Specs.DerivedFormalization.KoszulCochainResolution (cochainValue termIsoValue augmentationValue)
open Specs.DerivedFormalization.Cochains (compValue stalkValue shiftValue cohomologyShiftIsoValue qValue
  derivedValue derivedCohomologyValue cohomologyFactorsValue derivedStalkValue)
open Specs.DerivedFormalization.CochainModels
  (internalHomValue internalHomMapValue isKInjectiveValue)
open Specs.DerivedFormalization.CoinductionComplex (restrictedRegular coinduceValue evaluationValue)
open Specs.DerivedFormalization.DerivedCoinduction (Coinduction comparison)
open Specs.DerivedFormalization.DerivedRestriction
  (restrictScalarsComplexValue restrictScalarsValue restrictScalarsCohomologyIsoValue
    derivedRestrictScalarsValue derivedRestrictScalarsFactorsValue)
open scoped TensorProduct

universe u v

attribute [local instance] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency false
open private koszulCochain_d_apply from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.KoszulCochainResolution
open private localizedHomEquiv localizedHomEquiv_map from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedCoinduction

variable {A : Type u} [CommRing A]

private def quotientCoordinates (J : Ideal A) (a : List A) :
    (Fin a.length → A) →ₗ[A] (Fin a.length → A ⧸ J) :=
  LinearMap.pi fun j => J.mkQ.comp (LinearMap.proj j)

private lemma quotientCoordinates_surj (J : Ideal A) (a : List A) :
    Function.Surjective (quotientCoordinates J a) := by
  intro z
  choose x hx using fun j => Ideal.Quotient.mk_surjective (z j)
  exact ⟨x, funext hx⟩

private lemma reduceVector_basis (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (i : Fin a.length) :
    reduceVector J a h (Pi.basisFun A (Fin a.length) i) = generator J a h i := by
  apply congrArg J.toCotangent
  apply Subtype.ext
  exact listForm_basis a i

private lemma conormalMap_quotientCoordinates (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (x : Fin a.length → A) :
    conormalMap J a h (quotientCoordinates J a x) = reduceVector J a h x := by
  have eq : ((conormalMap J a h).restrictScalars A).comp (quotientCoordinates J a) =
      reduceVector J a h := by
    apply (Pi.basisFun A (Fin a.length)).ext
    intro i
    have hp : quotientCoordinates J a (Pi.basisFun A (Fin a.length) i) =
        Pi.basisFun (A ⧸ J) (Fin a.length) i := by
      ext j
      change Ideal.Quotient.mk J ((Pi.basisFun A (Fin a.length) i) j) =
        (Pi.basisFun (A ⧸ J) (Fin a.length) i) j
      by_cases hij : j = i <;> simp [Pi.basisFun_apply, hij]
    change conormalMap J a h (quotientCoordinates J a (Pi.basisFun A (Fin a.length) i)) =
      reduceVector J a h (Pi.basisFun A (Fin a.length) i)
    rw [hp, conormalMap, Module.Basis.constr_basis, reduceVector_basis]
  exact LinearMap.congr_fun eq x

private lemma degreeOneBoundaries_vanish_in_quotient (J : Ideal A) (a : List A)
    (ha : listIdeal a = J) (w : ⋀[A]^2 (Fin a.length → A)) :
    quotientCoordinates J a (exteriorPower.oneEquiv A _ (differential (listForm a) 1 w)) = 0 := by
  have he : (quotientCoordinates J a).comp ((exteriorPower.oneEquiv A _).toLinearMap.comp
      (differential (listForm a) 1)) = 0 := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, differential_ιMulti,
      map_sum, map_smul, LinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro j _
    let z := quotientCoordinates J a
      ((exteriorPower.oneEquiv A (Fin a.length → A)) (exteriorPower.ιMulti A 1 (v ∘ j.succAbove)))
    change (-1 : A)^j.val • (listForm a (v j) • z) = 0
    suffices hn : listForm a (v j) • z = 0 by rw [hn, smul_zero]
    have hj : Ideal.Quotient.mk J (listForm a (v j)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (ha ▸ listForm_mem a (v j))
    funext k
    change listForm a (v j) • z k = (0 : A ⧸ J)
    rw [← algebraMap_smul (A ⧸ J)]
    change Ideal.Quotient.mk J (listForm a (v j)) • z k = (0 : A ⧸ J)
    rw [hj, zero_smul]
  exact LinearMap.congr_fun he w

private lemma exactRelation_vanishes_in_quotient (J : Ideal A) (a : List A)
    (h : listIdeal a = J) (ha : RingTheory.Sequence.IsRegular A a)
    (x : Fin a.length → A) (hx : listForm a x = 0) : quotientCoordinates J a x = 0 := by
  let K := cochainValue a
  let T := (stalkValue A).obj (ModuleCat.of A (A ⧸ listIdeal a))
  let e₁ := termIsoValue a 1
  let e₀ := termIsoValue a 0
  let o := exteriorPower.oneEquiv A (Fin a.length → A)
  let y := e₁.inv (o.symm x)
  have : QuasiIso (augmentationValue a) := (koszulCochain_finiteFree_resolution a ha).1
  have hT : T.ExactAt (-1 : ℤ) :=
    ExactAt.of_isZero (isZero_single_obj_X (.up ℤ) 0 _ (-1) (by decide))
  have hex : K.ExactAt (-1 : ℤ) :=
    (quasiIsoAt_iff_exactAt' (augmentationValue a) (-1 : ℤ) hT).mp inferInstance
  rw [exactAt_iff' K (-2 : ℤ) (-1 : ℤ) (0 : ℤ) (by simp) (by simp)] at hex
  have hy : K.d (-1) 0 y = 0 := by
    apply e₀.toLinearEquiv.injective
    apply (exteriorPower.zeroEquiv A (Fin a.length → A)).injective
    have hd : e₀.hom (K.d (-1) 0 y) = differential (listForm a) 0 (o.symm x) :=
      koszulCochain_d_apply a 0 (o.symm x)
    change exteriorPower.zeroEquiv A _ (e₀.hom (K.d (-1) 0 y)) =
      exteriorPower.zeroEquiv A _ (e₀.hom 0)
    rw [hd, differential_one, LinearEquiv.apply_symm_apply, hx, map_zero, map_zero]
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).mp hex y hy
  change K.d (-2) (-1) w = y at hw
  let w' := (termIsoValue a 2).hom w
  have hd : differential (listForm a) 1 w' = o.symm x := by
    have hf : e₁.hom (K.d (-2) (-1) ((termIsoValue a 2).inv w')) =
      differential (listForm a) 1 w' := koszulCochain_d_apply a 1 w'
    rwa [ModuleCat.inv_hom_apply, hw, ModuleCat.hom_inv_apply, eq_comm] at hf
  have hzero := degreeOneBoundaries_vanish_in_quotient J a h w'
  rw [hd, LinearEquiv.apply_symm_apply] at hzero
  exact hzero

private lemma conormalMap_bijective (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (ha : RingTheory.Sequence.IsRegular A a) : Function.Bijective (conormalMap J a h) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro z hz
    obtain ⟨x, rfl⟩ := quotientCoordinates_surj J a z
    rw [conormalMap_quotientCoordinates] at hz
    have hx : listForm a x ∈ J ^ 2 :=
      (J.toCotangent_eq_zero ⟨listForm a x, h ▸ listForm_mem a x⟩).mp hz
    have hm : (J • (⊤ : Submodule A (Fin a.length → A))).map (listForm a) =
        (J ^ 2 : Ideal A) := by
      rw [Submodule.map_smul'', Submodule.map_top, listForm_range, h, Ideal.smul_eq_mul, pow_two]
    have hmem : listForm a x ∈ (J • (⊤ : Submodule A (Fin a.length → A))).map (listForm a) := by
      rw [hm]
      exact hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hmem
    have hy0 : quotientCoordinates J a y = 0 := by
      funext j
      have hm := Submodule.smul_top_le_comap_smul_top J
        (LinearMap.proj j : (Fin a.length → A) →ₗ[A] A) hy
      have hyj : y j ∈ (J • (⊤ : Submodule A A)) := hm
      rw [Ideal.smul_eq_mul, Ideal.mul_top] at hyj
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hyj
    have hxy : listForm a (x - y) = 0 := by
      rw [map_sub, hyx, sub_self]
    have hzero := exactRelation_vanishes_in_quotient J a h ha (x - y) hxy
    rw [map_sub, hy0, sub_zero] at hzero
    exact hzero
  · intro z
    obtain ⟨q, rfl⟩ := J.toCotangent_surjective z
    have hq : (q : A) ∈ LinearMap.range (listForm a) := by
      rw [listForm_range, h]
      exact q.property
    obtain ⟨x, hx⟩ := hq
    refine ⟨quotientCoordinates J a x, (conormalMap_quotientCoordinates J a h x).trans ?_⟩
    exact congrArg J.toCotangent (Subtype.ext hx)

/-- The named generators induce a basis of the actual conormal module. -/
theorem conormalBasis : conormalBasisType.{u} := by
  intro A _ _ J a h ha
  exact conormalMap_bijective J a h ha

private def conormalBasisOfRegular (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (ha : RingTheory.Sequence.IsRegular A a) :
    { b : Module.Basis (Fin a.length) (A ⧸ J) J.Cotangent // ∀ i, b i = generator J a h i } := by
  refine ⟨(Pi.basisFun (A ⧸ J) (Fin a.length)).map
    (LinearEquiv.ofBijective (conormalMap J a h) (conormalMap_bijective J a h ha)), ?_⟩
  intro i
  change conormalMap J a h (Pi.basisFun (A ⧸ J) (Fin a.length) i) = generator J a h i
  exact Module.Basis.constr_basis _ _ _ _

private def changeKoszul {a b : List A}
    (m : (Fin b.length → A) →ₗ[A] (Fin a.length → A))
    (hm : (listForm a).comp m = listForm b) : cochainValue b ⟶ cochainValue a :=
  extendMap (chainMap (listForm b) (listForm a) m hm) embeddingDownNat

private lemma changeKoszul_f {a b : List A}
    (m : (Fin b.length → A) →ₗ[A] (Fin a.length → A))
    (hm : (listForm a).comp m = listForm b) (n : ℕ) :
    (termIsoValue b n).inv ≫ (changeKoszul m hm).f (-(n : ℤ)) ≫ (termIsoValue a n).hom =
      ModuleCat.ofHom (exteriorPower.map n m) := by
  change (termIsoValue b n).inv ≫
      (extendMap (chainMap (listForm b) (listForm a) m hm) embeddingDownNat).f
        (embeddingDownNat.f n) ≫ (termIsoValue a n).hom = _
  rw [extendMap_f _ _ (i := n) rfl]
  change (termIsoValue b n).inv ≫
      ((termIsoValue b n).hom ≫ _ ≫ (termIsoValue a n).inv) ≫ (termIsoValue a n).hom = _
  simp [chainMap]

private lemma augmentation_zero_in_quotient (l : List A) (J : Ideal A) (hl : listIdeal l = J) :
    (augmentationValue l ≫ (stalkValue A).map
      ((Submodule.quotEquivOfEq (listIdeal l) J hl).toModuleIso.hom)).f 0 ≫
      (singleObjXSelf (.up ℤ) 0 (ModuleCat.of A (A ⧸ J))).hom =
        (termIsoValue l 0).hom ≫ ModuleCat.ofHom
          (J.mkQ.comp (exteriorPower.zeroEquiv A (Fin l.length → A)).toLinearMap) := by
  subst J
  have hq : (Submodule.quotEquivOfEq (listIdeal l) (listIdeal l) rfl).toModuleIso.hom =
      𝟙 (ModuleCat.of A (A ⧸ listIdeal l)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    refine Quotient.inductionOn' x ?_
    intro r
    rfl
  have hmap : (stalkValue A).map
      ((Submodule.quotEquivOfEq (listIdeal l) (listIdeal l) rfl).toModuleIso.hom) = 𝟙 _ :=
    (congrArg (stalkValue A).map hq).trans ((stalkValue A).map_id _)
  rw [hmap, Category.comp_id]
  exact koszulCochainAugmentation_f_zero l

private lemma changeKoszul_augmentation (J : Ideal A) {a b : List A}
    (ha : listIdeal a = J) (hb : listIdeal b = J)
    (m : (Fin b.length → A) →ₗ[A] (Fin a.length → A))
    (hm : (listForm a).comp m = listForm b) :
    changeKoszul m hm ≫ augmentationValue a ≫ (stalkValue A).map
        ((Submodule.quotEquivOfEq (listIdeal a) J ha).toModuleIso.hom) =
      augmentationValue b ≫ (stalkValue A).map
        ((Submodule.quotEquivOfEq (listIdeal b) J hb).toModuleIso.hom) := by
  apply HomologicalComplex.to_single_hom_ext
  apply (cancel_mono (singleObjXSelf (.up ℤ) 0 (ModuleCat.of A (A ⧸ J))).hom).mp
  rw [HomologicalComplex.comp_f (changeKoszul m hm), Category.assoc,
    augmentation_zero_in_quotient a J ha, augmentation_zero_in_quotient b J hb,
    ← Category.assoc ((changeKoszul m hm).f 0)]
  have hk := changeKoszul_f m hm 0
  change (termIsoValue b 0).inv ≫ (changeKoszul m hm).f 0 ≫ (termIsoValue a 0).hom = _ at hk
  rw [Iso.inv_comp_eq] at hk
  rw [hk, Category.assoc]
  apply ModuleCat.hom_ext
  ext x : 1
  exact congrArg J.mkQ (LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality m)
    ((termIsoValue b 0).hom x))

private lemma reduceWedge_change (J : Ideal A) {a b : List A}
    (ha : listIdeal a = J) (hb : listIdeal b = J)
    (m : (Fin b.length → A) →ₗ[A] (Fin a.length → A))
    (hm : (listForm a).comp m = listForm b) (n : ℕ) :
    (reduceWedge J a ha n).comp (exteriorPower.map n m) = reduceWedge J b hb n := by
  apply exteriorPower.linearMap_ext
  ext x : 1
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, reduceWedge, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  have hv (x : Fin b.length → A) : reduceVector J a ha (m x) = reduceVector J b hb x :=
    congrArg J.toCotangent (Subtype.ext (LinearMap.congr_fun hm x))
  congr 1
  funext i
  exact hv (x i)

theorem generatorChange : generatorChangeType.{u} := by
  intro A _ _ J a b ha hb hra hrb
  have hJ : J ≠ ⊤ := by
    intro he
    apply hra.top_ne_smul
    change (⊤ : Submodule A A) = listIdeal a • ⊤
    rw [ha, he, Ideal.smul_eq_mul, Ideal.top_mul]
  let : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJ
  have rank_a : Module.finrank (A ⧸ J) J.Cotangent = a.length := by
    simpa using Module.finrank_eq_card_basis (conormalBasisOfRegular J a ha hra).val
  have rank_b : Module.finrank (A ⧸ J) J.Cotangent = b.length := by
    simpa using Module.finrank_eq_card_basis (conormalBasisOfRegular J b hb hrb).val
  refine ⟨rank_a.symm.trans rank_b, redundant_lift a b ?_, ?_⟩
  · intro r hr
    exact ha.symm ▸ hb ▸ Ideal.subset_span hr
  · intro m hm
    exact ⟨changeKoszul m hm, changeKoszul_augmentation J ha hb m hm,
      changeKoszul_f m hm, reduceWedge_change J ha hb m hm⟩

private def wedgeHomotopy (a : List A) (e : Fin a.length → A) :
    Homotopy (listForm a e • 𝟙 (listComplex a)) 0 := by
  apply chainHomotopyOfComponents (listComplex a) _
    (fun n => ModuleCat.ofHom (leftWedge e n))
  · simp only [listComplex, complex]
    apply ModuleCat.hom_ext
    exact (wedge_identity_zero (listForm a) e).symm
  · intro n
    have hd (k : ℕ) : (listComplex a).d (k+1) k =
        ModuleCat.ofHom (differential (listForm a) k) :=
      ChainComplex.of_d (fun n => ModuleCat.of A (⋀[A]^n (Fin a.length → A)))
        (fun n => ModuleCat.ofHom (differential (listForm a) n)) k
    rw [hd n, hd (n+1)]
    apply ModuleCat.hom_ext
    change listForm a e • LinearMap.id =
      (leftWedge e n).comp (differential (listForm a) n) +
        (differential (listForm a) (n+1)).comp (leftWedge e (n+1))
    exact (wedge_identity_succ (listForm a) e n).symm.trans (add_comm _ _)

theorem idealMultiplication : idealMultiplicationType.{u} := by
  intro A _ a r hr
  obtain ⟨x, rfl⟩ : r ∈ LinearMap.range (listForm a) := by rwa [listForm_range]
  have h := (wedgeHomotopy a x).extend embeddingDownNat
  have he : extendMap (listForm a x • 𝟙 (listComplex a)) embeddingDownNat =
      listForm a x • 𝟙 (cochainValue a) := by
    ext i : 1
    by_cases hi : ∃ j, embeddingDownNat.f j = i
    · obtain ⟨j, rfl⟩ := hi
      rw [extendMap_f _ _ (i := j) rfl]
      simp [Linear.smul_comp, Linear.comp_smul]
      rfl
    · exact ((listComplex a).isZero_extend_X embeddingDownNat i
        (fun j hj => hi ⟨j, hj⟩)).eq_of_src _ _
  rw [he, show extendMap (0 : listComplex a ⟶ listComplex a) embeddingDownNat = 0 from
    (embeddingDownNat.extendFunctor (ModuleCat A)).map_zero _ _] at h
  exact ⟨h⟩

private abbrev quotientStalk (J : Ideal A) : compValue.{max u v} A :=
  (stalkValue A).obj (restrictedRegular.{v, u, u} (Ideal.Quotient.mk J))

private def quotientAugmentation (a : List A) : liftedKoszul.{u, v} a ⟶
    quotientStalk.{u, v} (listIdeal a) :=
  (CochainCoefficientLift.lift.{v, u} A).map (augmentationValue a) ≫
    (singleMapHomologicalComplex (ModuleCat.uliftFunctor.{v, u} A) (.up ℤ) 0).hom.app
      (ModuleCat.of A (A ⧸ listIdeal a))

private lemma quotientAugmentation_quasiIso (a : List A) (ha : RingTheory.Sequence.IsRegular A a) :
    QuasiIso (quotientAugmentation.{u, v} a) := by
  have : QuasiIso ((CochainCoefficientLift.lift.{v, u} A).map (augmentationValue a)) :=
    (CochainCoefficientLift.quasiIso_iff (augmentationValue a)).mpr
      (koszulCochain_finiteFree_resolution a ha).1
  unfold quotientAugmentation
  infer_instance

private lemma quotientAugmentation_zero (a : List A) (x : (liftedKoszul.{u, v} a).X 0) :
    (singleObjXSelf (.up ℤ) 0 (restrictedRegular.{v, u, u} (Ideal.Quotient.mk (listIdeal a)))).hom
      ((quotientAugmentation.{u, v} a).f 0 x) =
        ULift.up (augmentationAtZero (listIdeal a) a x) := by
  let F := ModuleCat.uliftFunctor.{v, u} A
  let B := ModuleCat.of A (A ⧸ listIdeal a)
  let e := singleMapHomologicalComplex F (.up ℤ) 0
  have hh : (quotientAugmentation.{u, v} a).f 0 ≫
      (singleObjXSelf (.up ℤ) 0 (F.obj B)).hom =
      F.map ((augmentationValue a).f 0 ≫ (singleObjXSelf (.up ℤ) 0 B).hom) := by
    change (F.map ((augmentationValue a).f 0) ≫ (e.hom.app B).f 0) ≫ _ = _
    rw [singleMapHomologicalComplex_hom_app_self, Functor.map_comp]
    simp
  have h := congrArg (fun (g : (liftedKoszul.{u, v} a).X 0 ⟶ F.obj B) => g x) hh
  change _ = _ at h
  rw [show (augmentationValue a).f 0 ≫ (singleObjXSelf (.up ℤ) 0 B).hom =
    (termIsoValue a 0).hom ≫ ModuleCat.ofHom ((listIdeal a).mkQ.comp
      (exteriorPower.zeroEquiv A (Fin a.length → A)).toLinearMap) from
      koszulCochainAugmentation_f_zero a] at h
  exact h

private lemma liftedKoszul_isKProjective (a : List A) (ha : RingTheory.Sequence.IsRegular A a) :
    CochainComplex.IsKProjective (liftedKoszul.{u, v} a) := by
  have hres := koszulCochain_finiteFree_resolution a ha
  have : (liftedKoszul.{u, v} a).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact Functor.map_isZero (ModuleCat.uliftFunctor.{v, u} A) (hres.2.2.2 n (fun h => (not_lt_of_ge h.2) hn))
  have (n : ℤ) : CategoryTheory.Projective ((liftedKoszul.{u, v} a).X n) := by
    have : Module.Free A ((cochainValue a).X n) := (hres.2.2.1 n).1
    have : CategoryTheory.Projective ((cochainValue a).X n) :=
      ModuleCat.projective_of_free (Module.Free.chooseBasis A ((cochainValue a).X n))
    exact Functor.projective_obj (ModuleCat.uliftFunctor.{v, u} A) _
  exact CochainComplex.isKProjective_of_projective _ 0

theorem modelComparison : modelComparisonType.{u, v} := by
  intro A _ _ J a h ha I i hi hI
  subst J
  let J := listIdeal a
  let f := Ideal.Quotient.mk J
  let ε := quotientAugmentation.{u, v} a
  obtain ⟨e, he⟩ := Coinduction.stalkComparison.{v, u, u} f I
  let p := internalHomMapValue ε (𝟙 I)
  refine ⟨⟨e.inv ≫ p, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have : QuasiIso p := internalHomMap_quasiIso_of_isKInjective I hI ε
        (quotientAugmentation_quasiIso a ha)
    infer_instance
  · exact internalHomMap_quasiIso_of_isKProjective _ (liftedKoszul_isKProjective a ha) i hi
  · intro n z x
    let S := restrictedRegular.{v, u, u} f
    let e₀ := singleObjXSelf (.up ℤ) 0 S
    have hz : e.hom.f n (e.inv.f n z) = z :=
      ModuleCat.hom_inv_apply ((HomologicalComplex.eval (ModuleCat A) (.up ℤ) n).mapIso e) z
    have hε : ε.f 0 x = e₀.inv (ULift.up (augmentationAtZero J a x)) := by
      apply e₀.toLinearEquiv.injective
      change e₀.hom (ε.f 0 x) = e₀.hom (e₀.inv _)
      rw [ModuleCat.hom_inv_apply]
      exact quotientAugmentation_zero a x
    change ((internalHomMap ε (𝟙 I)).f n (e.inv.f n z)).v 0 n (zero_add n) x =
      (ModuleCat.CoextendScalars.equiv f (I.X n) z) (augmentationAtZero J a x)
    rw [internalHomMap_apply, hε]
    have hEval := he n (e.inv.f n z) (augmentationAtZero J a x)
    change (ModuleCat.CoextendScalars.equiv f (I.X n) (e.hom.f n (e.inv.f n z)))
        (augmentationAtZero J a x) =
      ((e.inv.f n z).v 0 n (zero_add n)) (e₀.inv (ULift.up (augmentationAtZero J a x))) at hEval
    rw [hz] at hEval
    exact hEval.symm
  · intro n j k h hj z
    have hZ : IsZero ((quotientStalk.{u, v} J).X j) :=
      isZero_single_obj_X _ _ _ _ hj
    have h0 := hZ.eq_of_tgt (ε.f j) 0
    apply ModuleCat.hom_ext
    ext x : 1
    change ((internalHomMap ε (𝟙 I)).f n (e.inv.f n z)).v j k h x = 0
    rw [internalHomMap_apply, h0]
    simp
  · intro n r z j k h
    have hz : f r • z = r •
        (show ((restrictScalarsComplexValue f).obj (coinduced J I)).X n from z) := rfl
    rw [hz]
    change (((e.inv ≫ p).f n) (r • _)).v j k h = _
    rw [map_smul, Cochain.smul_v, Linear.smul_comp, Category.id_comp]

private abbrev nativeDual (a : List A) : compValue.{u} A :=
  internalHomValue (cochainValue a) ((stalkValue A).obj (ModuleCat.of A A))

private def wedgePairingEquiv (a : List A) (p q : ℕ) (h : p + q = a.length) :
    ((⋀[A]^p (Fin a.length → A)) ⊗[A] Module.Dual A (freeDeterminant a)) ≃ₗ[A]
      ((⋀[A]^q (Fin a.length → A)) →ₗ[A] A) :=
  (TensorProduct.congr (LinearEquiv.refl A _)
    (SelfDuality.determinantDualOrientation a)).trans
    ((TensorProduct.rid A _).trans (SelfDuality.scalarWedge a p q h).toPerfPair)

private lemma wedgePairingEquiv_tmul (a : List A) (p q : ℕ) (h : p + q = a.length)
    (z : ⋀[A]^p (Fin a.length → A)) (x : ⋀[A]^q (Fin a.length → A))
    (φ : Module.Dual A (freeDeterminant a)) :
    wedgePairingEquiv a p q h (z ⊗ₜ[A] φ) x = φ (topWedge a p q h z x) := by
  change (SelfDuality.scalarWedge a p q h)
    (SelfDuality.determinantDualOrientation a φ • z) x = φ (topWedge a p q h z x)
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, mul_comm]
  exact (SelfDuality.determinant_eval a φ _).symm

private lemma koszulTerm_isZero (a : List A) (i : ℤ)
    (hi : i ∉ Set.Icc (-(a.length : ℤ)) 0) : IsZero ((cochainValue a).X i) := by
  by_cases h : 0 < i
  · exact (listComplex a).isZero_extend_X embeddingDownNat i (by
      intro n hn
      change -(n : ℤ) = i at hn
      omega)
  · let n := (-i).toNat
    have hi' : -(n : ℤ) = i := by dsimp [n]; omega
    have hn : a.length < n := by
      have hni : ¬ (-(a.length : ℤ) ≤ i ∧ i ≤ 0) := hi
      omega
    exact (ModuleCat.isZero_iff_subsingleton.mpr (listComplex_vanish a n hn)).of_iso
      (((cochainValue a).XIsoOfEq hi').symm ≪≫ termIsoValue a n)

private def nativeDualEvaluation (a : List A) (i : ℤ) :
    (nativeDual a).X i ≃ₗ[A] (((cochainValue a).X (-i)) →ₗ[A] A) :=
  (Cochain.toSingleLinearEquiv (K := cochainValue a) (X := ModuleCat.of A A)
    (neg_add_cancel i)).trans ModuleCat.homLinearEquiv

private def sourceExteriorIso (a : List A) (i : ℤ) (p : ℕ)
    (h : i + -(a.length : ℤ) = -(p : ℤ)) :
    ((cochainValue a).X (i + -(a.length : ℤ))) ≅ ModuleCat.of A (⋀[A]^p (Fin a.length → A)) :=
  (cochainValue a).XIsoOfEq h ≪≫ termIsoValue a p

private def shiftedTensorIso (a : List A) (i : ℤ) (p : ℕ)
    (h : i + -(a.length : ℤ) = -(p : ℤ)) :
    (shiftedKoszul a).X i ≃ₗ[A] ((⋀[A]^p (Fin a.length → A)) ⊗[A] Module.Dual A (freeDeterminant a)) :=
  TensorProduct.congr (sourceExteriorIso a i p h).toLinearEquiv (LinearEquiv.refl A _)

private lemma shiftedTensorIso_wedge (a : List A) (p q : ℕ) (h : p + q = a.length)
    (z : ⋀[A]^p (Fin a.length → A)) (φ : Module.Dual A (freeDeterminant a)) :
    shiftedTensorIso a (q : ℤ) p (by omega) (wedgeIntoShift a p q h z φ) = z ⊗ₜ[A] φ := by
  have hq : (q : ℤ) + -(a.length : ℤ) = -(p : ℤ) := by omega
  change ((sourceExteriorIso a (q : ℤ) p hq).hom ((sourceExteriorIso a (q : ℤ) p hq).inv z))
    ⊗ₜ[A] φ = _
  rw [ModuleCat.hom_inv_apply]

private def interiorPairing (a : List A) (p q : ℕ) (h : p + q = a.length) :
    (shiftedKoszul a).X (q : ℤ) ≅ (nativeDual a).X (q : ℤ) :=
  ((shiftedTensorIso a (q : ℤ) p (by omega)).trans
    ((wedgePairingEquiv a p q h).trans
      ((LinearEquiv.arrowCongr (termIsoValue a q).toLinearEquiv.symm (LinearEquiv.refl A A)).trans
        (nativeDualEvaluation a (q : ℤ)).symm))).toModuleIso

private lemma interiorPairing_eval (a : List A) (p q : ℕ) (h : p + q = a.length)
    (z : ⋀[A]^p (Fin a.length → A)) (x : ⋀[A]^q (Fin a.length → A))
    (φ : Module.Dual A (freeDeterminant a)) :
    nativeDualEvaluation a (q : ℤ) ((interiorPairing a p q h).hom (wedgeIntoShift a p q h z φ))
      ((termIsoValue a q).inv x) = φ (topWedge a p q h z x) := by
  change (nativeDualEvaluation a (q : ℤ))
    ((nativeDualEvaluation a (q : ℤ)).symm
      ((LinearEquiv.arrowCongr (termIsoValue a q).toLinearEquiv.symm (LinearEquiv.refl A A))
        (wedgePairingEquiv a p q h (shiftedTensorIso a (q : ℤ) p _ (wedgeIntoShift a p q h z φ)))))
    ((termIsoValue a q).inv x) = _
  rw [LinearEquiv.apply_symm_apply, shiftedTensorIso_wedge]
  change wedgePairingEquiv a p q h (z ⊗ₜ[A] φ)
      ((termIsoValue a q).hom ((termIsoValue a q).inv x)) = _
  rw [ModuleCat.hom_inv_apply, wedgePairingEquiv_tmul]

private lemma shiftedKoszul_isZero (a : List A) (i : ℤ)
    (hi : i ∉ Set.Icc 0 (a.length : ℤ)) : IsZero ((shiftedKoszul a).X i) := by
  let D := ModuleCat.of A (Module.Dual A (freeDeterminant a))
  have h := koszulTerm_isZero a (i + -(a.length : ℤ)) (by
    intro h
    apply hi
    change 0 ≤ i ∧ i ≤ (a.length : ℤ)
    change -(a.length : ℤ) ≤ i + -(a.length : ℤ) ∧ i + -(a.length : ℤ) ≤ 0 at h
    omega)
  exact Functor.map_isZero (tensorRight D) h

private lemma nativeDual_isZero (a : List A) (i : ℤ)
    (hi : i ∉ Set.Icc 0 (a.length : ℤ)) : IsZero ((nativeDual a).X i) := by
  have hk := koszulTerm_isZero a (-i) (by
    intro h
    apply hi
    change 0 ≤ i ∧ i ≤ (a.length : ℤ)
    change -(a.length : ℤ) ≤ -i ∧ -i ≤ 0 at h
    omega)
  have := ModuleCat.isZero_iff_subsingleton.mp hk
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact (nativeDualEvaluation a i).injective.subsingleton

private def exteriorPairingTerm (a : List A) (i : ℤ) :
    (shiftedKoszul a).X i ≅ (nativeDual a).X i :=
  if h : i ∈ Set.Icc 0 (a.length : ℤ) then
    have hq : (i.toNat : ℤ) = i := Int.toNat_of_nonneg h.1
    have hp : a.length - i.toNat + i.toNat = a.length := by
      have := h.2
      omega
    ((shiftedKoszul a).XIsoOfEq hq.symm) ≪≫
      interiorPairing a (a.length - i.toNat) i.toNat hp ≪≫
        (nativeDual a).XIsoOfEq hq
  else (shiftedKoszul_isZero a i h).iso (nativeDual_isZero a i h)

private lemma exteriorPairingTerm_nat (a : List A) (p q : ℕ) (h : p + q = a.length) :
    exteriorPairingTerm a (q : ℤ) = interiorPairing a p q h := by
  rw [exteriorPairingTerm, dite_eq_left (show (q : ℤ) ∈ Set.Icc 0 (a.length : ℤ) by
      change 0 ≤ (q : ℤ) ∧ (q : ℤ) ≤ (a.length : ℤ)
      omega)]
  simp only [Int.toNat_natCast]
  have he : a.length - q = p := by omega
  subst p
  simp [HomologicalComplex.XIsoOfEq]

private lemma sourceExterior_diff (a : List A) (i j : ℤ) (p : ℕ)
    (hi : i + -(a.length : ℤ) = -((p + 1 : ℕ) : ℤ))
    (hj : j + -(a.length : ℤ) = -(p : ℤ))
    (z : ⋀[A]^(p+1) (Fin a.length → A)) :
    (cochainValue a).d (i + -(a.length : ℤ)) (j + -(a.length : ℤ))
      ((sourceExteriorIso a i (p+1) hi).inv z) =
    (sourceExteriorIso a j p hj).inv (differential (listForm a) p z) := by
  apply (sourceExteriorIso a j p hj).toLinearEquiv.injective
  have hd : (sourceExteriorIso a i (p+1) hi).inv ≫
    (cochainValue a).d (i + -(a.length : ℤ)) (j + -(a.length : ℤ)) ≫
      (sourceExteriorIso a j p hj).hom =
        (termIsoValue a (p+1)).inv ≫ (cochainValue a).d (-((p+1 : ℕ) : ℤ)) (-(p : ℤ)) ≫
          (termIsoValue a p).hom := by
    simp [sourceExteriorIso]
  change ((sourceExteriorIso a i (p+1) hi).inv ≫ _ ≫ (sourceExteriorIso a j p hj).hom) z =
    (sourceExteriorIso a j p hj).hom ((sourceExteriorIso a j p hj).inv _)
  rw [hd, ModuleCat.hom_inv_apply]
  exact koszulCochain_d_apply a p z

private lemma shiftedKoszul_d_wedge (a : List A) (p q : ℕ) (h : p + (q+1) = a.length)
    (z : ⋀[A]^(p+1) (Fin a.length → A)) (φ : Module.Dual A (freeDeterminant a)) :
    (shiftedKoszul a).d (q : ℤ) ((q+1 : ℕ) : ℤ) (wedgeIntoShift a (p+1) q (by omega) z φ) =
      (-1 : A)^a.length • wedgeIntoShift a p (q+1) h (differential (listForm a) p z) φ := by
  have hi : (q : ℤ) + -(a.length : ℤ) = -((p+1 : ℕ) : ℤ) := by omega
  have hj : ((q+1 : ℕ) : ℤ) + -(a.length : ℤ) = -(p : ℤ) := by omega
  let D := ModuleCat.of A (Module.Dual A (freeDeterminant a))
  let K := cochainValue a
  change ((((-(a.length : ℤ)).negOnePow •
    K.d ((q : ℤ) + -(a.length : ℤ)) (((q+1 : ℕ) : ℤ) + -(a.length : ℤ))) ▷ D)
      (((sourceExteriorIso a (q : ℤ) (p+1) hi).inv z) ⊗ₜ[A] φ)) = _
  rw [ModuleCat.MonoidalCategory.whiskerRight_apply]
  change (((-(a.length : ℤ)).negOnePow •
    (cochainValue a).d ((q : ℤ) + -(a.length : ℤ)) (((q+1 : ℕ) : ℤ) + -(a.length : ℤ))
      ((sourceExteriorIso a (q : ℤ) (p+1) hi).inv z)) ⊗ₜ[A] φ) = _
  rw [sourceExterior_diff a (q : ℤ) ((q+1 : ℕ) : ℤ) p hi hj]
  simp only [Units.smul_def, Int.negOnePow_neg, ← Int.cast_smul_eq_zsmul A,
    Int.cast_negOnePow_natCast]
  rfl

private lemma nativeDualEvaluation_d (a : List A) (i j : ℤ) (z : (nativeDual a).X i)
    (x : (cochainValue a).X (-j)) :
    nativeDualEvaluation a j ((nativeDual a).d i j z) x =
      (j.negOnePow : A) • nativeDualEvaluation a i z ((cochainValue a).d (-j) (-i) x) := by
  obtain ⟨g, rfl⟩ := Cochain.toSingleMk_surjective z (-i) (neg_add_cancel i)
  change (Cochain.toSingleEquiv (neg_add_cancel j)
    (δ i j (Cochain.toSingleMk g (neg_add_cancel i)))) x =
      (j.negOnePow : A) • (Cochain.toSingleEquiv (neg_add_cancel i)
        (Cochain.toSingleMk g (neg_add_cancel i))) ((cochainValue a).d (-j) (-i) x)
  rw [Cochain.toSingleEquiv_toSingleMk g (neg_add_cancel i)]
  rw [Cochain.δ_toSingleMk _ _ j (-j) (neg_add_cancel j), Units.smul_def, map_zsmul,
    Cochain.toSingleEquiv_toSingleMk]
  change (j.negOnePow : ℤ) • g ((cochainValue a).d (-j) (-i) x) =
    (j.negOnePow : A) • g ((cochainValue a).d (-j) (-i) x)
  exact (Int.cast_smul_eq_zsmul A (j.negOnePow : ℤ)
    (show A from g ((cochainValue a).d (-j) (-i) x))).symm

private lemma wedgePairing_d (a : List A) (p q : ℕ) (h : p+(q+1) = a.length)
    (z : ⋀[A]^(p+1) (Fin a.length → A)) (x : ⋀[A]^(q+1) (Fin a.length → A))
    (φ : Module.Dual A (freeDeterminant a)) :
    (-1 : A)^(q+1) • φ (topWedge a (p+1) q (by omega) z (differential (listForm a) q x)) =
      (-1 : A)^a.length • φ (topWedge a p (q+1) h (differential (listForm a) p z) x) := by
  have hd := SelfDuality.topWedge_differential a p q h z x
  change topWedge a p (q+1) h (differential (listForm a) p z) x =
    (-1 : A)^p • topWedge a (p+1) q (by omega) z (differential (listForm a) q x) at hd
  rw [hd, map_smul, smul_smul, ← pow_add]
  rw [show a.length + p = (q+1) + 2 * p by omega,
    pow_add (a := (-1 : A)) (q+1) (2*p), pow_mul]
  simp

private lemma interiorPairing_comm (a : List A) (p q : ℕ) (h : p+(q+1) = a.length) :
    (interiorPairing a (p+1) q (by omega)).hom ≫ (nativeDual a).d (q : ℤ) ((q+1 : ℕ) : ℤ) =
      (shiftedKoszul a).d (q : ℤ) ((q+1 : ℕ) : ℤ) ≫ (interiorPairing a p (q+1) h).hom := by
  apply ModuleCat.hom_ext
  let E := shiftedTensorIso a (q : ℤ) (p+1) (by omega)
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ := E.symm.surjective y
  induction w using TensorProduct.inductionOn with
  | add w w' hw hw' => simpa only [map_add] using congrArg₂ (· + ·) hw hw'
  | tmul z φ =>
    have he : E.symm (z ⊗ₜ[A] φ) = wedgeIntoShift a (p+1) q (by omega) z φ :=
      E.symm_apply_eq.mpr (shiftedTensorIso_wedge a (p+1) q (by omega) z φ).symm
    rw [he]
    apply (nativeDualEvaluation a ((q+1 : ℕ) : ℤ)).injective
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := (termIsoValue a (q+1)).toLinearEquiv.symm.surjective y
    change nativeDualEvaluation a ((q+1 : ℕ) : ℤ)
      ((nativeDual a).d (q : ℤ) ((q+1 : ℕ) : ℤ)
        ((interiorPairing a (p+1) q (by omega)).hom (wedgeIntoShift a (p+1) q (by omega) z φ)))
      ((termIsoValue a (q+1)).inv x) =
        nativeDualEvaluation a ((q+1 : ℕ) : ℤ)
          ((interiorPairing a p (q+1) h).hom ((shiftedKoszul a).d (q : ℤ) ((q+1 : ℕ) : ℤ)
            (wedgeIntoShift a (p+1) q (by omega) z φ))) ((termIsoValue a (q+1)).inv x)
    rw [nativeDualEvaluation_d, shiftedKoszul_d_wedge a p q h]
    have hdiff : (cochainValue a).d (-((q+1 : ℕ) : ℤ)) (-(q : ℤ)) ((termIsoValue a (q+1)).inv x) =
        (termIsoValue a q).inv (differential (listForm a) q x) :=
      (termIsoValue a q).toLinearEquiv.injective
        ((koszulCochain_d_apply a q x).trans
          (ModuleCat.hom_inv_apply (termIsoValue a q) _).symm)
    rw [hdiff, interiorPairing_eval, map_smul, map_smul, LinearMap.smul_apply,
      interiorPairing_eval, Int.cast_negOnePow_natCast]
    exact wedgePairing_d a p q h z x φ

private def exteriorPairing (a : List A) : shiftedKoszul a ≅ nativeDual a :=
  HomologicalComplex.Hom.isoOfComponents (exteriorPairingTerm a) (by
    intro i j hij
    by_cases hi : i ∈ Set.Icc 0 (a.length : ℤ)
    · by_cases hj : j ∈ Set.Icc 0 (a.length : ℤ)
      · have hij' : i + 1 = j := hij
        subst j
        have hi' : (i.toNat : ℤ) = i := Int.toNat_of_nonneg hi.1
        let q := i.toNat
        have hq : (q : ℤ) = i := hi'
        have hc : q + 1 ≤ a.length := by have := hj.2; omega
        have hp : a.length - (q+1) + (q+1) = a.length := Nat.sub_add_cancel hc
        have he := interiorPairing_comm a (a.length - (q+1)) q hp
        rw [← exteriorPairingTerm_nat, ← exteriorPairingTerm_nat] at he
        have hq' : ((q+1 : ℕ) : ℤ) = i + 1 := by omega
        rw [hq, hq'] at he
        exact he
      · exact (nativeDual_isZero a j hj).eq_of_tgt _ _
    · exact (shiftedKoszul_isZero a i hi).eq_of_src _ _)

theorem signedPairing : signedPairingType.{u} := by
  intro A _ a
  refine ⟨exteriorPairing a, ?_⟩
  intro p q h z x φ
  change nativeDualEvaluation a (q : ℤ) ((exteriorPairingTerm a (q : ℤ)).hom
    (wedgeIntoShift a p q h z φ)) ((termIsoValue a q).inv x) = _
  rw [exteriorPairingTerm_nat a p q h]
  exact interiorPairing_eval a p q h z x φ

private def liftCochainEquiv (K L : compValue.{u} A) (n : ℤ) :
    ((CochainCoefficientLift.lift.{v} A).obj (internalHomValue K L)).X n ≃ₗ[A]
      (internalHomValue ((CochainCoefficientLift.lift.{v} A).obj K)
        ((CochainCoefficientLift.lift.{v} A).obj L)).X n := by
  let F := ModuleCat.uliftFunctor.{v, u} A
  exact ULift.moduleEquiv.trans
    { toFun := fun z => z.map F
      invFun := fun z => Cochain.mk (fun i j h => F.preimage (z.v i j h))
      left_inv := by
        intro z
        apply Cochain.ext
        intro i j h
        exact F.preimage_map (z.v i j h)
      right_inv := by
        intro z
        apply Cochain.ext
        intro i j h
        exact F.map_preimage (z.v i j h)
      map_add' := fun x y => Cochain.map_add x y F
      map_smul' := by
        intro r z
        apply Cochain.ext
        intro i j h
        exact F.map_smul r (z.v i j h) }

private def liftInternalHomIso (K L : compValue.{u} A) :
    (CochainCoefficientLift.lift.{v} A).obj (internalHomValue K L) ≅
      internalHomValue ((CochainCoefficientLift.lift.{v} A).obj K)
        ((CochainCoefficientLift.lift.{v} A).obj L) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (liftCochainEquiv.{u,v} K L n).toModuleIso) (by
      intro n m _
      apply ModuleCat.hom_ext
      ext z : 1
      exact δ_map n m z.down (ModuleCat.uliftFunctor.{v,u} A))

private def internalHomPostIso {K L M : compValue.{max u v} A} (e : L ≅ M) :
    internalHomValue K L ≅ internalHomValue K M where
  hom := internalHomMap (𝟙 K) e.hom
  inv := internalHomMap (𝟙 K) e.inv
  hom_inv_id := by rw [internalHomMap_comp, Category.id_comp, Iso.hom_inv_id, internalHomMap_id]
  inv_hom_id := by rw [internalHomMap_comp, Category.id_comp, Iso.inv_hom_id, internalHomMap_id]

private def liftedDualIso (a : List A) :
    (CochainCoefficientLift.lift.{v} A).obj (nativeDual a) ≅ dualKoszul.{u,v} a :=
  liftInternalHomIso.{u,v} (cochainValue a) ((stalkValue A).obj (ModuleCat.of A A)) ≪≫
    internalHomPostIso ((singleMapHomologicalComplex
      (ModuleCat.uliftFunctor.{v,u} A) (.up ℤ) 0).app (ModuleCat.of A A))

private def untensorShiftedKoszul (a : List A) : shiftedKoszul a ≅
    (shiftValue A (-(a.length : ℤ))).obj (cochainValue a) :=
  let D := (SelfDuality.determinantDualOrientation a).toModuleIso
  let e := ((curriedTensor (ModuleCat.{u} A)).flip.mapIso D) ≪≫ rightUnitorNatIso (ModuleCat.{u} A)
  ((NatIso.mapHomologicalComplex e (.up ℤ)) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat.{u} A) (.up ℤ)).app
      ((shiftValue A (-(a.length : ℤ))).obj (cochainValue a))

private lemma koszulCohomology_isZero (a : List A) (ha : RingTheory.Sequence.IsRegular A a)
    (n : ℤ) (hn : n ≠ 0) : IsZero ((cochainValue a).homology n) := by
  let : QuasiIso (augmentationValue a) := (koszulCochain_finiteFree_resolution a ha).1
  have h := (ExactAt.of_isZero
    (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of A (A ⧸ listIdeal a)) n hn)).isZero_homology
  exact h.of_iso (asIso (homologyMap (augmentationValue a) n))

private lemma dualKoszulCohomology_isZero (a : List A) (ha : RingTheory.Sequence.IsRegular A a)
    (n : ℤ) (hn : n ≠ (a.length : ℤ)) : IsZero ((dualKoszul.{u,v} a).homology n) := by
  let H := homologyFunctor (ModuleCat.{u} A) (.up ℤ) n
  have he : (nativeDual a).homology n ≅ (cochainValue a).homology (n + -(a.length : ℤ)) :=
    H.mapIso ((exteriorPairing a).symm ≪≫ untensorShiftedKoszul a) ≪≫
      (cohomologyShiftIsoValue A (-(a.length : ℤ)) n).app (cochainValue a)
  have h := (koszulCohomology_isZero a ha _ (by omega)).of_iso he
  have hh := Functor.map_isZero (ModuleCat.uliftFunctor.{v,u} A) h
  exact hh.of_iso
    ((homologyFunctor _ (.up ℤ) n).mapIso (liftedDualIso.{u,v} a).symm ≪≫
      (CochainCoefficientLift.cohomologyIso.{v,u} A n).app (nativeDual a))

theorem coinducedVanishing (J : Ideal A) [IsNoetherianRing A]
    (a : List A) (h : listIdeal a = J) (ha : RingTheory.Sequence.IsRegular A a)
    {I : compValue.{max u v} A} (i : scalarStalk.{u, v} (A := A) ⟶ I)
    (hi : QuasiIso i) (hI : isKInjectiveValue I)
    (n : ℤ) (hn : n ≠ (a.length : ℤ)) : IsZero ((coinduced J I).homology n) := by
  obtain ⟨C⟩ := modelComparison.{u,v} J a h ha I i hi hI
  have hz := (dualKoszulCohomology_isZero.{u,v} a ha n hn).of_iso
    (modelHomologyIso J C n).symm
  rw [ModuleCat.isZero_iff_subsingleton] at hz ⊢
  exact hz

private def quotientRestrictIso (J : Ideal A) {X Y : ModuleCat.{max u v} (A ⧸ J)}
    (e : (restrictScalarsValue (Ideal.Quotient.mk J)).obj X ≅
      (restrictScalarsValue (Ideal.Quotient.mk J)).obj Y) : X ≅ Y :=
  let E : X ≃ₗ[A ⧸ J] Y :=
    { toAddEquiv := e.toLinearEquiv.toAddEquiv
      map_smul' := by
        intro b x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
        exact e.hom.hom.map_smul r x }
  E.toModuleIso

private def conormalOrientation (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (ha : RingTheory.Sequence.IsRegular A a) :
    (⋀[A ⧸ J]^a.length J.Cotangent) ≃ₗ[A ⧸ J] (A ⧸ J) :=
  letI := SelfDuality.topSubsetsUnique a
  ((conormalBasisOfRegular J a h ha).val.exteriorPower a.length).equivFun.trans
    (LinearEquiv.funUnique _ _ _)

private def determinantDualCoordinate (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (ha : RingTheory.Sequence.IsRegular A a) :
    determinantDual J a.length ≃ₗ[A ⧸ J] (A ⧸ J) :=
  (conormalOrientation J a h ha).symm.dualMap.trans (LinearMap.ringLmapEquivSelf _ _ _)

private def nativeTopWindow (a : List A) :
    (nativeDual a).sc (a.length : ℤ) ≅ (cochainValue a).sc 0 :=
  (shortComplexFunctor (ModuleCat A) (.up ℤ) (a.length : ℤ)).mapIso
    ((exteriorPairing a).symm ≪≫ untensorShiftedKoszul a) ≪≫
      (CochainComplex.shiftShortComplexFunctorIso (ModuleCat A) (-(a.length : ℤ))
        (a.length : ℤ) 0 (neg_add_cancel _)).app (cochainValue a)

private def nativeTopCohomologyIso (a : List A) (ha : RingTheory.Sequence.IsRegular A a) :
    (nativeDual a).homology (a.length : ℤ) ≅ ModuleCat.of A (A ⧸ listIdeal a) :=
  let _haug : QuasiIso (augmentationValue a) := (koszulCochain_finiteFree_resolution a ha).1
  (ShortComplex.homologyFunctor (ModuleCat A)).mapIso (nativeTopWindow a) ≪≫
    asIso (homologyMap (augmentationValue a) 0) ≪≫
    singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of A (A ⧸ listIdeal a))

private lemma nativeTopCohomologyIso_π (a : List A) (ha : RingTheory.Sequence.IsRegular A a) :
    (nativeDual a).homologyπ (a.length : ℤ) ≫ (nativeTopCohomologyIso a ha).hom =
      (nativeDual a).iCycles (a.length : ℤ) ≫ (nativeTopWindow a).hom.τ₂ ≫
        (termIsoValue a 0).hom ≫ ModuleCat.ofHom
          ((listIdeal a).mkQ.comp (exteriorPower.zeroEquiv A (Fin a.length → A)).toLinearMap) := by
  let c : ℤ := a.length
  let e := nativeTopWindow a
  let T := (stalkValue A).obj (ModuleCat.of A (A ⧸ listIdeal a))
  let f := (shortComplexFunctor (ModuleCat A) (.up ℤ) 0).map (augmentationValue a)
  change (nativeDual a).homologyπ c ≫
      (ShortComplex.homologyMap e.hom ≫ ShortComplex.homologyMap f ≫
        (singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of A (A ⧸ listIdeal a))).hom) = _
  change ((nativeDual a).sc c).homologyπ ≫ _ = _
  rw [ShortComplex.homologyπ_naturality_assoc, ShortComplex.homologyπ_naturality_assoc]
  have hs : (T.sc 0).homologyπ ≫
      (singleObjHomologySelfIso (.up ℤ) 0 (ModuleCat.of A (A ⧸ listIdeal a))).hom =
      (T.sc 0).iCycles ≫ (singleObjXSelf (.up ℤ) 0 (ModuleCat.of A (A ⧸ listIdeal a))).hom := by
    exact (homologyπ_singleObjHomologySelfIso_hom (.up ℤ) 0 _).trans
      (singleObjCyclesSelfIso_hom (.up ℤ) 0 _)
  rw [hs, ShortComplex.cyclesMap_i_assoc, ShortComplex.cyclesMap_i_assoc]
  change _ ≫ _ ≫
    ((augmentationValue a).f 0 ≫ (singleObjXSelf (.up ℤ) 0 (ModuleCat.of A (A ⧸ listIdeal a))).hom) = _
  have hzero : (augmentationValue a).f 0 ≫
      (singleObjXSelf (.up ℤ) 0 (ModuleCat.of A (A ⧸ listIdeal a))).hom =
    (termIsoValue a 0).hom ≫ ModuleCat.ofHom
      ((listIdeal a).mkQ.comp (exteriorPower.zeroEquiv A (Fin a.length → A)).toLinearMap) :=
    koszulCochainAugmentation_f_zero a
  rw [hzero]
  rfl

private def dualKoszulTopIso (a : List A) (ha : RingTheory.Sequence.IsRegular A a) :
    (dualKoszul.{u,v} a).homology (a.length : ℤ) ≅
      restrictedRegular.{v,u,u} (Ideal.Quotient.mk (listIdeal a)) :=
  (homologyFunctor _ (.up ℤ) _).mapIso (liftedDualIso.{u,v} a).symm ≪≫
    (CochainCoefficientLift.cohomologyIso.{v,u} A (a.length : ℤ)).app (nativeDual a) ≪≫
    (ModuleCat.uliftFunctor.{v,u} A).mapIso (nativeTopCohomologyIso a ha)

private def coinducedTopIso (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (ha : RingTheory.Sequence.IsRegular A a)
    {I : compValue.{max u v} A} {i : scalarStalk.{u,v} (A := A) ⟶ I}
    (C : ModelComparison J a h i) :
    (coinduced J I).homology (a.length : ℤ) ≅ determinantModule.{u,v} J a.length := by
  subst J
  let e := quotientRestrictIso (listIdeal a)
    ((modelHomologyIso (listIdeal a) C (a.length : ℤ)).symm ≪≫ dualKoszulTopIso.{u,v} a ha)
  let det := (ModuleCat.uliftFunctor.{v,u} (A ⧸ listIdeal a)).mapIso
    (determinantDualCoordinate (listIdeal a) a rfl ha).toModuleIso
  exact e ≪≫ det.symm

private lemma changeKoszul_eval {a b : List A}
    (m : (Fin b.length → A) →ₗ[A] (Fin a.length → A))
    (hm : (listForm a).comp m = listForm b) (n : ℕ) (x : (cochainValue b).X (-(n : ℤ))) :
    (termIsoValue a n).hom ((changeKoszul m hm).f (-(n : ℤ)) x) =
      exteriorPower.map n m ((termIsoValue b n).hom x) := by
  have h := changeKoszul_f m hm n
  rw [Iso.inv_comp_eq] at h
  exact congrArg (fun g => g x) h

private lemma augmentationAtZero_change (J : Ideal A) {a b : List A}
    (m : (Fin b.length → A) →ₗ[A] (Fin a.length → A))
    (hm : (listForm a).comp m = listForm b) (x : (liftedKoszul.{u,v} b).X 0) :
    augmentationAtZero J a (((CochainCoefficientLift.lift.{v} A).map (changeKoszul m hm)).f 0 x) =
      augmentationAtZero J b x := by
  obtain ⟨x₀, rfl⟩ := (CochainCoefficientLift.termEquiv.{v} (cochainValue b) 0).surjective x
  rw [CochainCoefficientLift.lift_f]
  change Ideal.Quotient.mk J
      (exteriorPower.zeroEquiv A _ ((termIsoValue a 0).hom ((changeKoszul m hm).f 0 x₀))) =
    Ideal.Quotient.mk J (exteriorPower.zeroEquiv A _ ((termIsoValue b 0).hom x₀))
  have h := changeKoszul_eval m hm 0 x₀
  change (termIsoValue a 0).hom ((changeKoszul m hm).f 0 x₀) = _ at h
  rw [h]
  congr 1
  exact LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality m) _

private lemma lift_change_wedge {a b : List A}
    (m : (Fin b.length → A) →ₗ[A] (Fin a.length → A))
    (hm : (listForm a).comp m = listForm b) (n : ℕ)
    (x : ⋀[A]^n (Fin b.length → A)) :
    ((CochainCoefficientLift.lift.{v} A).map (changeKoszul m hm)).f (-(n : ℤ))
        (liftedWedge.{u,v} b n x) =
      liftedWedge.{u,v} a n (exteriorPower.map n m x) := by
  change ULift.up ((changeKoszul m hm).f (-(n : ℤ)) ((termIsoValue b n).inv x)) =
    ULift.up ((termIsoValue a n).inv ((exteriorPower.map n m) x))
  congr 1
  apply (termIsoValue a n).toLinearEquiv.injective
  change (termIsoValue a n).hom _ = (termIsoValue a n).hom ((termIsoValue a n).inv _)
  rw [changeKoszul_eval, ModuleCat.hom_inv_apply, ModuleCat.hom_inv_apply]

private lemma coinduction_pre_change (J : Ideal A) {a b : List A}
    {ha : listIdeal a = J} {hb : listIdeal b = J}
    {I : compValue.{max u v} A} {i : scalarStalk.{u,v} (A := A) ⟶ I}
    (Ca : ModelComparison J a ha i) (Cb : ModelComparison J b hb i)
    (m : (Fin b.length → A) →ₗ[A] (Fin a.length → A))
    (hm : (listForm a).comp m = listForm b) :
    Ca.pre ≫ internalHomMap ((CochainCoefficientLift.lift.{v} A).map (changeKoszul m hm)) (𝟙 I) =
      Cb.pre := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro j k h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let t := (CochainCoefficientLift.lift.{v} A).map (changeKoszul m hm)
  change ((internalHomMap t (𝟙 I)).f n (Ca.pre.f n z)).v j k h x =
    (Cb.pre.f n z).v j k h x
  rw [internalHomMap_apply]
  by_cases hj : j = 0
  · subst j
    have hk : n = k := by omega
    cases hk
    simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
    change (Ca.pre.f n z).v 0 n (zero_add n) (t.f 0 x) =
      (Cb.pre.f n z).v 0 n (zero_add n) x
    rw [Ca.pre_at_zero, Cb.pre_at_zero]
    exact congrArg _ (augmentationAtZero_change J m hm x)
  · rw [Ca.pre_away_zero n j k h hj, Cb.pre_away_zero n j k h hj]
    simp

private lemma modelHomologyIso_change (J : Ideal A) {a b : List A}
    {ha : listIdeal a = J} {hb : listIdeal b = J}
    {I : compValue.{max u v} A} {i : scalarStalk.{u,v} (A := A) ⟶ I}
    (Ca : ModelComparison J a ha i) (Cb : ModelComparison J b hb i)
    (m : (Fin b.length → A) →ₗ[A] (Fin a.length → A))
    (hm : (listForm a).comp m = listForm b) (n : ℤ) :
    homologyMap (internalHomMap ((CochainCoefficientLift.lift.{v} A).map (changeKoszul m hm))
        (𝟙 scalarStalk)) n ≫ (modelHomologyIso J Cb n).hom =
      (modelHomologyIso J Ca n).hom := by
  let t := (CochainCoefficientLift.lift.{v} A).map (changeKoszul m hm)
  have hpre := coinduction_pre_change J Ca Cb m hm
  have hpost :
      internalHomMap t (𝟙 scalarStalk) ≫ internalHomMap (𝟙 (liftedKoszul.{u,v} b)) i =
        internalHomMap (𝟙 (liftedKoszul.{u,v} a)) i ≫ internalHomMap t (𝟙 I) := by
    rw [internalHomMap_comp, internalHomMap_comp, Category.id_comp, Category.id_comp,
      Category.comp_id, Category.comp_id]
  let := Ca.pre_quasiIso
  let := Cb.pre_quasiIso
  change homologyMap (internalHomMap t (𝟙 scalarStalk)) n ≫ _ = _
  simp only [modelHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  change homologyMap (internalHomMap t (𝟙 scalarStalk)) n ≫
    homologyMap (internalHomMap (𝟙 (liftedKoszul.{u,v} b)) i) n ≫ _ =
      homologyMap (internalHomMap (𝟙 (liftedKoszul.{u,v} a)) i) n ≫ _
  rw [← Category.assoc (homologyMap (internalHomMap t (𝟙 scalarStalk)) n),
    ← homologyMap_comp, hpost, homologyMap_comp, Category.assoc]
  congr 1
  change homologyMap (internalHomMap t (𝟙 I)) n ≫
    (asIso (homologyMap Cb.pre n)).inv ≫ _ =
      (asIso (homologyMap Ca.pre n)).inv ≫ _
  have hh := congrArg (fun p => homologyMap p n) hpre
  rw [homologyMap_comp] at hh
  have eq : homologyMap (internalHomMap t (𝟙 I)) n ≫ (asIso (homologyMap Cb.pre n)).inv =
      (asIso (homologyMap Ca.pre n)).inv := by
    apply (cancel_epi (asIso (homologyMap Ca.pre n)).hom).mp
    rw [Iso.hom_inv_id]
    change homologyMap Ca.pre n ≫ _ = _
    rw [← Category.assoc]
    rw [show homologyMap Ca.pre n ≫ homologyMap (internalHomMap t (𝟙 I)) n =
      homologyMap Cb.pre n from hh]
    exact (asIso (homologyMap Cb.pre n)).hom_inv_id
  rw [← Category.assoc, eq]

private lemma reduceWedge_ιMulti (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (n : ℕ) (x : Fin n → (Fin a.length → A)) :
    reduceWedge J a h n (exteriorPower.ιMulti A n x) =
      exteriorPower.ιMulti (A ⧸ J) n (reduceVector J a h ∘ x) := by
  unfold reduceWedge
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

private lemma reduceWedge_determinant_basis (J : Ideal A) (a : List A)
    (h : listIdeal a = J) (ha : RingTheory.Sequence.IsRegular A a) :
    reduceWedge J a h a.length (listBasis a a.length (SelfDuality.topSubset a)) =
      ((conormalBasisOfRegular J a h ha).val.exteriorPower a.length) (SelfDuality.topSubset a) := by
  rw [listBasis_apply, exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  rw [reduceWedge_ιMulti]
  congr 1
  funext j
  exact (reduceVector_basis J a h _).trans ((conormalBasisOfRegular J a h ha).property _).symm

private lemma conormalOrientation_top (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (ha : RingTheory.Sequence.IsRegular A a) :
    conormalOrientation J a h ha
      (((conormalBasisOfRegular J a h ha).val.exteriorPower a.length) (SelfDuality.topSubset a)) = 1 := by
  dsimp only [conormalOrientation, LinearEquiv.trans_apply, LinearEquiv.funUnique_apply]
  simp only [Module.Basis.equivFun_self]
  rw [ite_eq_left (Subsingleton.elim _ _)]

private lemma orientation_reduceWedge (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (ha : RingTheory.Sequence.IsRegular A a) (x : freeDeterminant a) :
    conormalOrientation J a h ha (reduceWedge J a h a.length x) =
      Ideal.Quotient.mk J (SelfDuality.orientation a x) := by
  let t := listBasis a a.length (SelfDuality.topSubset a)
  have ht : SelfDuality.orientation a t = 1 := SelfDuality.orientation_top_basis a
  have hx : x = SelfDuality.orientation a x • t := by
    apply (SelfDuality.orientation a).injective
    rw [map_smul, ht, smul_eq_mul, mul_one]
  conv_lhs => rw [hx]
  rw [map_smul]
  have hsmul (r : A) (y : ⋀[A ⧸ J]^a.length J.Cotangent) :
      r • y = Ideal.Quotient.mk J r • y := by
    rw [← algebraMap_smul (A ⧸ J) r y]
    rfl
  rw [hsmul, map_smul, reduceWedge_determinant_basis J a h ha,
    conormalOrientation_top J a h ha, smul_eq_mul, mul_one]

private lemma reduceWedge_surj (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (ha : RingTheory.Sequence.IsRegular A a) :
    Function.Surjective (reduceWedge J a h a.length) := by
  intro y
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (conormalOrientation J a h ha y)
  refine ⟨(SelfDuality.orientation a).symm r, (conormalOrientation J a h ha).injective ?_⟩
  rw [orientation_reduceWedge J a h ha, LinearEquiv.apply_symm_apply, hr]

private lemma topIdentification_unique (J : Ideal A) {a : List A} {h : listIdeal a = J}
    (ha : RingTheory.Sequence.IsRegular A a)
    {I : compValue.{max u v} A} {i : scalarStalk.{u,v} (A := A) ⟶ I}
    (C : ModelComparison J a h i)
    {e₁ e₂ : (coinduced J I).homology (a.length : ℤ) ≅ determinantModule.{u,v} J a.length}
    (h₁ : TopIdentification J C e₁) (h₂ : TopIdentification J C e₂) : e₁ = e₂ := by
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  let E := modelHomologyIso J C (a.length : ℤ)
  obtain ⟨y, hy⟩ := E.toLinearEquiv.surjective z
  have hs := (ModuleCat.epi_iff_surjective ((dualKoszul.{u,v} a).homologyπ (a.length : ℤ))).mp
    (inferInstance : Epi ((dualKoszul.{u,v} a).homologyπ (a.length : ℤ)))
  obtain ⟨c, rfl⟩ := hs y
  apply ULift.ext
  apply LinearMap.ext
  intro x
  obtain ⟨x₀, rfl⟩ := reduceWedge_surj J a h ha x
  change (e₁.hom z).down (reduceWedge J a h _ x₀) =
    (e₂.hom z).down (reduceWedge J a h _ x₀)
  rw [← hy]
  exact (h₁ c x₀).trans (h₂ c x₀).symm

private abbrev freeVolume (a : List A) : freeDeterminant a := (SelfDuality.orientation a).symm 1

private lemma topWedge_zero_left (a : List A) (z : ⋀[A]^0 (Fin a.length → A))
    (x : freeDeterminant a) :
    topWedge a 0 a.length (Nat.zero_add _) z x =
      (exteriorPower.zeroEquiv A (Fin a.length → A) z) • x := by
  let r := exteriorPower.zeroEquiv A (Fin a.length → A) z
  have hw : topWedge a 0 a.length (Nat.zero_add _)
      (exteriorPower.ιMulti A 0 (fun i => Fin.elim0 i)) x = x := by
    apply Subtype.ext
    change (SelfDuality.topWedge a 0 a.length (Nat.zero_add _) _ x : ExteriorAlgebra A (Fin a.length → A)) = x
    rw [SelfDuality.topWedge_coe]
    simp [ExteriorAlgebra.ιMulti_zero_apply]
  have hz : z = r • exteriorPower.ιMulti A 0 (fun i => Fin.elim0 i) := by
    apply (exteriorPower.zeroEquiv A (Fin a.length → A)).injective
    rw [map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one]
  change topWedge a 0 a.length (Nat.zero_add _) z x = r • x
  rw [hz]
  change SelfDuality.topWedge a 0 a.length (Nat.zero_add _) (r • _) x = _
  rw [map_smul, LinearMap.smul_apply]
  exact congrArg (r • ·) hw

private lemma nativeTopWindow_tmul (a : List A) (z : ⋀[A]^0 (Fin a.length → A))
    (φ : Module.Dual A (freeDeterminant a)) :
    (termIsoValue a 0).hom
        ((nativeTopWindow a).hom.τ₂
          ((exteriorPairing a).hom.f (a.length : ℤ)
            (wedgeIntoShift a 0 a.length (Nat.zero_add _) z φ))) =
      SelfDuality.determinantDualOrientation a φ • z := by
  let c : ℤ := a.length
  let τ := (CochainComplex.shiftEval (ModuleCat A) (-c) c 0 (neg_add_cancel c)).app (cochainValue a)
  let E := (exteriorPairing a).hom.f c
  let E' := (exteriorPairing a).inv.f c
  let w := wedgeIntoShift a 0 a.length (Nat.zero_add _) z φ
  have hcancel : E' (E w) = w := by
    exact ModuleCat.inv_hom_apply ((eval _ (.up ℤ) c).mapIso (exteriorPairing a)) w
  change (termIsoValue a 0).hom (τ.hom ((untensorShiftedKoszul a).hom.f c (E' (E w)))) = _
  rw [hcancel]
  have hτ : ((untensorShiftedKoszul a).hom.f c) w =
      SelfDuality.determinantDualOrientation a φ •
        τ.inv ((termIsoValue a 0).inv z) := rfl
  rw [hτ, map_smul, ModuleCat.hom_inv_apply, map_smul, ModuleCat.hom_inv_apply]

private lemma nativeTopWindow_eval (a : List A) (y : (nativeDual a).X (a.length : ℤ)) :
    exteriorPower.zeroEquiv A (Fin a.length → A)
        ((termIsoValue a 0).hom ((nativeTopWindow a).hom.τ₂ y)) =
      nativeDualEvaluation a (a.length : ℤ) y ((termIsoValue a a.length).inv (freeVolume a)) := by
  let c : ℤ := a.length
  let e := ((eval _ (.up ℤ) c).mapIso (exteriorPairing a)).toLinearEquiv
  let s := shiftedTensorIso a c 0 (by simp [c])
  obtain ⟨w, rfl⟩ := (s.symm.trans e).surjective y
  induction w using TensorProduct.inductionOn with
  | add w₁ w₂ ih₁ ih₂ =>
    simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ih₁ ih₂
  | tmul z φ =>
    have hw : s.symm (z ⊗ₜ[A] φ) = wedgeIntoShift a 0 a.length (Nat.zero_add _) z φ :=
      s.symm_apply_eq.mpr (shiftedTensorIso_wedge a 0 a.length (Nat.zero_add _) z φ).symm
    change exteriorPower.zeroEquiv A (Fin a.length → A)
        ((termIsoValue a 0).hom
          ((nativeTopWindow a).hom.τ₂ ((exteriorPairing a).hom.f c (s.symm (z ⊗ₜ[A] φ))))) =
      nativeDualEvaluation a c ((exteriorPairing a).hom.f c (s.symm (z ⊗ₜ[A] φ)))
        ((termIsoValue a a.length).inv (freeVolume a))
    rw [hw, nativeTopWindow_tmul]
    change _ = nativeDualEvaluation a (a.length : ℤ)
      ((exteriorPairingTerm a (a.length : ℤ)).hom
        (wedgeIntoShift a 0 a.length (Nat.zero_add _) z φ))
        ((termIsoValue a a.length).inv (freeVolume a))
    rw [exteriorPairingTerm_nat _ 0 _ (Nat.zero_add _), interiorPairing_eval, topWedge_zero_left,
      map_smul, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
    rfl

private lemma nativeTopCohomologyIso_eval (a : List A) (ha : RingTheory.Sequence.IsRegular A a)
    (z : (nativeDual a).cycles (a.length : ℤ)) :
    (nativeTopCohomologyIso a ha).hom ((nativeDual a).homologyπ _ z) =
      Ideal.Quotient.mk (listIdeal a)
        (nativeDualEvaluation a (a.length : ℤ) ((nativeDual a).iCycles _ z)
          ((termIsoValue a a.length).inv (freeVolume a))) := by
  have h := congrArg (fun g => g z) (nativeTopCohomologyIso_π a ha)
  change _ = (listIdeal a).mkQ (exteriorPower.zeroEquiv A (Fin a.length → A)
    ((termIsoValue a 0).hom ((nativeTopWindow a).hom.τ₂ ((nativeDual a).iCycles _ z)))) at h
  rw [nativeTopWindow_eval] at h
  exact h

private def liftedDualEvaluation (a : List A) (n : ℕ) (y : (dualKoszul.{u,v} a).X (n : ℤ))
    (x : ⋀[A]^n (Fin a.length → A)) : A :=
  ((singleObjXSelf (.up ℤ) 0 (ModuleCat.of A (ULift.{v} A))).hom
    (y.v (-(n : ℤ)) 0 (neg_add_cancel (n : ℤ)) (liftedWedge.{u,v} a n x))).down

private lemma liftedDualIso_eval (a : List A) (n : ℕ) (y : (nativeDual a).X (n : ℤ))
    (x : ⋀[A]^n (Fin a.length → A)) :
    liftedDualEvaluation.{u,v} a n ((liftedDualIso.{u,v} a).hom.f (n : ℤ) (ULift.up y)) x =
      nativeDualEvaluation a (n : ℤ) y ((termIsoValue a n).inv x) := by
  let F := ModuleCat.uliftFunctor.{v,u} A
  let M := ModuleCat.of A A
  let T := (stalkValue A).obj M
  let e := (singleMapHomologicalComplex F (.up ℤ) 0).app M
  let C := singleObjXSelf (.up ℤ) 0 (F.obj M)
  unfold liftedDualEvaluation
  change (C.hom (((internalHomMap (𝟙 (liftedKoszul.{u,v} a)) e.hom).f (n : ℤ)
    (y.map F)).v (-(n : ℤ)) 0 (neg_add_cancel (n : ℤ)) (liftedWedge.{u,v} a n x))).down = _
  rw [internalHomMap_apply]
  change (C.hom (e.hom.f 0 (ULift.up (y.v (-(n : ℤ)) 0 (neg_add_cancel (n : ℤ))
    ((termIsoValue a n).inv x))))).down = _
  have h : e.hom.f 0 ≫ C.hom = F.map (singleObjXSelf (.up ℤ) 0 M).hom := by
    change ((singleMapHomologicalComplex F (.up ℤ) 0).hom.app M).f 0 ≫ C.hom = _
    rw [singleMapHomologicalComplex_hom_app_self]
    simp [C]
  exact congrArg (fun (g : (F.obj (T.X 0)) ⟶ F.obj M) =>
    (g (ULift.up (y.v (-(n : ℤ)) 0 (neg_add_cancel (n : ℤ))
      ((termIsoValue a n).inv x)))).down) h

private lemma dualKoszulTopIso_eval (a : List A) (ha : RingTheory.Sequence.IsRegular A a)
    (z : (dualKoszul.{u,v} a).cycles (a.length : ℤ)) (x : freeDeterminant a) :
    Ideal.Quotient.mk (listIdeal a) (SelfDuality.orientation a x) *
        ((dualKoszulTopIso.{u,v} a ha).hom ((dualKoszul.{u,v} a).homologyπ _ z)).down =
      Ideal.Quotient.mk (listIdeal a)
        (liftedDualEvaluation.{u,v} a a.length ((dualKoszul.{u,v} a).iCycles _ z) x) := by
  let c : ℤ := a.length
  let e := liftedDualIso.{u,v} a
  let t := CochainCoefficientLift.fromOriginalCycles.{v} e.hom c
  have ht : Function.Surjective t := by
    exact ((cyclesFunctor (ModuleCat.{max u v} A) (.up ℤ) c).mapIso e).toLinearEquiv.surjective.comp
      (CochainCoefficientLift.cyclesEquiv.{v} (nativeDual a) c).surjective
  obtain ⟨z₀, rfl⟩ := ht z
  have hπ := CochainCoefficientLift.fromOriginalCohomology_homologyπ.{v} e.hom c z₀
  have hz : ((dualKoszulTopIso.{u,v} a ha).hom ((dualKoszul.{u,v} a).homologyπ _ (t z₀))).down =
      (nativeTopCohomologyIso a ha).hom ((nativeDual a).homologyπ _ z₀) := by
    rw [← hπ]
    let H := homologyFunctor (ModuleCat.{max u v} A) (.up ℤ) c
    let L := (CochainCoefficientLift.cohomologyIso.{v,u} A c).app (nativeDual a)
    let z' := (CochainCoefficientLift.cohomologyEquiv.{v} (nativeDual a) c)
      ((nativeDual a).homologyπ c z₀)
    change (nativeTopCohomologyIso a ha).hom ((L.hom ((H.mapIso e).inv ((H.mapIso e).hom z'))).down) = _
    rw [ModuleCat.inv_hom_apply]
    change (nativeTopCohomologyIso a ha).hom
      ((L.hom (L.inv (ULift.up ((nativeDual a).homologyπ c z₀)))).down) = _
    rw [ModuleCat.hom_inv_apply]
  have hc := CochainCoefficientLift.fromOriginalCycles_iCycles.{v} e.hom c z₀
  change (dualKoszul.{u,v} a).iCycles c (t z₀) =
    e.hom.f c (ULift.up ((nativeDual a).iCycles c z₀)) at hc
  rw [hz, hc, liftedDualIso_eval, nativeTopCohomologyIso_eval]
  let r := SelfDuality.orientation a x
  have hx : x = r • freeVolume a := by
    apply (SelfDuality.orientation a).injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  conv_rhs => rw [hx]
  rw [map_smul, map_smul, smul_eq_mul, map_mul]

private lemma coinducedTopIso_identification (J : Ideal A) (a : List A) (h : listIdeal a = J)
    (ha : RingTheory.Sequence.IsRegular A a)
    {I : compValue.{max u v} A} {i : scalarStalk.{u,v} (A := A) ⟶ I}
    (C : ModelComparison J a h i) : TopIdentification J C (coinducedTopIso J a h ha C) := by
  subst J
  let J := listIdeal a
  let d := determinantDualCoordinate J a rfl ha
  let E := modelHomologyIso J C (a.length : ℤ)
  intro z x
  let y := (dualKoszul.{u,v} a).homologyπ _ z
  let K := dualKoszulTopIso.{u,v} a ha
  change (d.symm ((K.hom (E.inv (E.hom y))).down)) (reduceWedge J a rfl _ x) =
    Ideal.Quotient.mk J (liftedDualEvaluation.{u,v} a a.length ((dualKoszul.{u,v} a).iCycles _ z) x)
  rw [ModuleCat.inv_hom_apply]
  let φ := d.symm (K.hom y).down
  let o := conormalOrientation J a rfl ha
  have hs : reduceWedge J a rfl _ x = (Ideal.Quotient.mk J (SelfDuality.orientation a x)) • o.symm 1 := by
    apply o.injective
    rw [map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    exact orientation_reduceWedge J a rfl ha x
  rw [hs, map_smul, smul_eq_mul]
  have hd : φ (o.symm 1) = (K.hom y).down := d.apply_symm_apply _
  change Ideal.Quotient.mk J (SelfDuality.orientation a x) * φ (o.symm 1) = _
  rw [hd]
  exact dualKoszulTopIso_eval a ha z x

private def EvaluationRule (J : Ideal A) {a : List A} {h : listIdeal a = J}
    {I : compValue.{max u v} A} {i : scalarStalk.{u,v} (A := A) ⟶ I}
    (C : ModelComparison J a h i) (n : ℕ)
    (e : (coinduced J I).homology (n : ℤ) ≅ determinantModule.{u,v} J n) : Prop :=
  ∀ (z : (dualKoszul.{u,v} a).cycles (n : ℤ)) (x : ⋀[A]^n (Fin a.length → A)),
    (e.hom ((modelHomologyIso J C (n : ℤ)).hom
      ((dualKoszul.{u,v} a).homologyπ _ z))).down (reduceWedge J a h n x) =
      Ideal.Quotient.mk J (liftedDualEvaluation.{u,v} a n ((dualKoszul.{u,v} a).iCycles _ z) x)

private lemma evaluationRule_iff (J : Ideal A) {a : List A} {h : listIdeal a = J}
    {I : compValue.{max u v} A} {i : scalarStalk.{u,v} (A := A) ⟶ I}
    (C : ModelComparison J a h i) {n : ℕ} (hn : a.length = n)
    (e : (coinduced J I).homology (n : ℤ) ≅ determinantModule.{u,v} J n) :
    EvaluationRule J C n e ↔ TopIdentification J C (hn ▸ e) := by
  subst n
  rfl

private lemma evaluationRule_compare (J : Ideal A) {a b : List A}
    {ha : listIdeal a = J} {hb : listIdeal b = J}
    {I : compValue.{max u v} A} {i : scalarStalk.{u,v} (A := A) ⟶ I}
    (Ca : ModelComparison J a ha i) (Cb : ModelComparison J b hb i)
    (m : (Fin b.length → A) →ₗ[A] (Fin a.length → A))
    (hm : (listForm a).comp m = listForm b) (n : ℕ)
    (hs : Function.Surjective (reduceWedge J b hb n))
    {e₁ e₂ : (coinduced J I).homology (n : ℤ) ≅ determinantModule.{u,v} J n}
    (h₁ : EvaluationRule J Ca n e₁) (h₂ : EvaluationRule J Cb n e₂) : e₁ = e₂ := by
  let c : ℤ := n
  let t := (CochainCoefficientLift.lift.{v} A).map (changeKoszul m hm)
  let T := internalHomMap t (𝟙 (scalarStalk.{u,v} (A := A)))
  let Ea := modelHomologyIso J Ca c
  let Eb := modelHomologyIso J Cb c
  have hcomp := modelHomologyIso_change J Ca Cb m hm c
  apply Iso.ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  obtain ⟨q, hq⟩ := Ea.toLinearEquiv.surjective z
  have hπ := (ModuleCat.epi_iff_surjective ((dualKoszul.{u,v} a).homologyπ c)).mp
    (inferInstance : Epi ((dualKoszul.{u,v} a).homologyπ c))
  obtain ⟨r, rfl⟩ := hπ q
  apply ULift.ext
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hs y
  let r' := cyclesMap T c r
  have hy : Eb.hom ((dualKoszul.{u,v} b).homologyπ c r') = z := by
    have hx := congrArg (fun g => g r) (homologyπ_naturality T c)
    change homologyMap T c ((dualKoszul.{u,v} a).homologyπ c r) =
      (dualKoszul.{u,v} b).homologyπ c r' at hx
    rw [← hx]
    exact (congrArg (fun g => g ((dualKoszul.{u,v} a).homologyπ c r)) hcomp).trans hq
  have hw : reduceWedge J a ha n (exteriorPower.map n m x) = reduceWedge J b hb n x :=
    LinearMap.congr_fun (reduceWedge_change J ha hb m hm n) x
  have hf := congrArg (fun g => g r) (cyclesMap_i T c)
  change (dualKoszul.{u,v} b).iCycles c r' =
    T.f c ((dualKoszul.{u,v} a).iCycles c r) at hf
  have hd : liftedDualEvaluation.{u,v} b n ((dualKoszul.{u,v} b).iCycles c r') x =
      liftedDualEvaluation.{u,v} a n ((dualKoszul.{u,v} a).iCycles c r)
        (exteriorPower.map n m x) := by
    rw [hf]
    unfold liftedDualEvaluation
    rw [internalHomMap_apply, lift_change_wedge]
    rfl
  have hA := h₁ r (exteriorPower.map n m x)
  have hB := h₂ r' x
  change Ea.hom ((dualKoszul.{u,v} a).homologyπ c r) = z at hq
  change (e₁.hom (Ea.hom ((dualKoszul.{u,v} a).homologyπ c r))).down
      (reduceWedge J a ha n (exteriorPower.map n m x)) = _ at hA
  change (e₂.hom (Eb.hom ((dualKoszul.{u,v} b).homologyπ c r'))).down
      (reduceWedge J b hb n x) = _ at hB
  rw [hq, hw] at hA
  rw [hy, hd] at hB
  exact hA.trans hB.symm

theorem coinducedCohomology : coinducedCohomologyType.{u,v} := by
  intro A _ _ J a ha hra I i hi hI
  obtain ⟨Ca⟩ := modelComparison.{u,v} J a ha hra I i hi hI
  let e := coinducedTopIso J a ha hra Ca
  have he := coinducedTopIso_identification J a ha hra Ca
  refine ⟨coinducedVanishing J a ha hra i hi hI, e, ?_, ?_⟩
  · intro b hb hn hrb Cb
    let e' := coinducedTopIso J b hb hrb Cb
    have he' := coinducedTopIso_identification J b hb hrb Cb
    obtain ⟨m, hm⟩ := redundant_lift a b (fun r hr => ha.symm ▸ hb ▸ Ideal.subset_span hr)
    have hsurj (k : ℕ) (hk : b.length = k) : Function.Surjective (reduceWedge J b hb k) := by
      subst k
      exact reduceWedge_surj J b hb hrb
    have castRule (k : ℕ) (hk : b.length = k) : EvaluationRule J Cb k (hk ▸ e') := by
      subst k
      exact he'
    have eq := evaluationRule_compare J Ca Cb m hm a.length (hsurj _ hn)
      (show EvaluationRule J Ca a.length e from he) (castRule _ hn)
    apply (evaluationRule_iff J Cb hn e).1
    rw [eq]
    exact castRule _ hn
  · intro e' he'
    apply topIdentification_unique J hra Ca
    · exact he' a ha rfl hra Ca
    · exact he

private lemma coinduction_pre_natural (J : Ideal A) {a : List A} {ha : listIdeal a = J}
    {I I' : compValue.{max u v} A} {i : scalarStalk.{u,v} (A := A) ⟶ I}
    {i' : scalarStalk.{u,v} (A := A) ⟶ I'}
    (C : ModelComparison J a ha i) (C' : ModelComparison J a ha i') (t : I ⟶ I') :
    (restrictScalarsComplexValue (Ideal.Quotient.mk J)).map
      ((coinduceValue.{v} (Ideal.Quotient.mk J)).map t) ≫ C'.pre =
        C.pre ≫ internalHomMap (𝟙 (liftedKoszul.{u,v} a)) t := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro j k h
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let t' := (coinduceValue.{v} (Ideal.Quotient.mk J)).map t
  change ((C'.pre.f n (t'.f n z)).v j k h) x =
    ((internalHomMap (𝟙 (liftedKoszul.{u,v} a)) t).f n (C.pre.f n z)).v j k h x
  rw [internalHomMap_apply]
  simp only [HomologicalComplex.id_f, ModuleCat.id_apply]
  by_cases hj : j = 0
  · subst j
    have hk : n = k := by omega
    cases hk
    rw [C'.pre_at_zero, C.pre_at_zero]
    rfl
  · rw [C'.pre_away_zero n j k h hj, C.pre_away_zero n j k h hj]
    simp

private lemma modelHomologyIso_natural (J : Ideal A) {a : List A} {ha : listIdeal a = J}
    {I I' : compValue.{max u v} A} {i : scalarStalk.{u,v} (A := A) ⟶ I}
    {i' : scalarStalk.{u,v} (A := A) ⟶ I'}
    (C : ModelComparison J a ha i) (C' : ModelComparison J a ha i') {t : I ⟶ I'}
    (ht : Homotopy (i ≫ t) i') (n : ℤ) :
    (modelHomologyIso J C n).hom ≫ (restrictScalarsValue (Ideal.Quotient.mk J)).map
      (homologyMap ((coinduceValue.{v} (Ideal.Quotient.mk J)).map t) n) =
        (modelHomologyIso J C' n).hom := by
  let f := Ideal.Quotient.mk J
  let t' := (coinduceValue.{v} f).map t
  let R := restrictScalarsComplexValue f
  let K := liftedKoszul.{u,v} a
  let T := internalHomMap (𝟙 K) t
  let _ := C.pre_quasiIso
  let _ := C'.pre_quasiIso
  let E := asIso (homologyMap C.pre n)
  let E' := asIso (homologyMap C'.pre n)
  let H := restrictScalarsCohomologyIsoValue f n
  have hr : homologyMap (R.map t') n ≫ H.hom.app (coinduced J I') =
      H.hom.app (coinduced J I) ≫ (restrictScalarsValue f).map (homologyMap t' n) :=
    H.hom.naturality t'
  have hpre : homologyMap (R.map t') n ≫ E'.hom = E.hom ≫ homologyMap T n := by
    have h := congrArg (fun g => homologyMap g n) (coinduction_pre_natural J C C' t)
    rw [homologyMap_comp, homologyMap_comp] at h
    exact h
  have hpre' : E.inv ≫ homologyMap (R.map t') n = homologyMap T n ≫ E'.inv := by
    apply (cancel_epi E.hom).mp
    apply (cancel_mono E'.hom).mp
    simpa [Category.assoc] using hpre
  have hpost : homologyMap (internalHomMap (𝟙 K) i) n ≫ homologyMap T n =
      homologyMap (internalHomMap (𝟙 K) i') n := by
    rw [← homologyMap_comp, internalHomMap_comp, Category.id_comp]
    exact (internalHomMapHomotopy (Homotopy.refl (𝟙 K)) ht).homologyMap_eq n
  change (homologyMap (internalHomMap (𝟙 K) i) n ≫ E.inv ≫ H.hom.app (coinduced J I)) ≫
    (restrictScalarsValue f).map (homologyMap t' n) =
      homologyMap (internalHomMap (𝟙 K) i') n ≫ E'.inv ≫ H.hom.app (coinduced J I')
  rw [Category.assoc, Category.assoc, ← hr, ← Category.assoc E.inv, hpre',
    Category.assoc, ← Category.assoc (homologyMap (internalHomMap (𝟙 K) i) n), hpost]

private lemma replacementComparison {X I I' : compValue.{max u v} A}
    (i : X ⟶ I) (i' : X ⟶ I') (hi : QuasiIso i) (hI' : isKInjectiveValue I') :
    ∃ t : I ⟶ I', (qValue A).map i ≫ (qValue A).map t = (qValue A).map i' ∧
      Nonempty (Homotopy (i ≫ t) i') := by
  let _ := hI'
  let _ : IsIso ((qValue A).map i) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) i).2 hi
  let p := inv ((qValue A).map i) ≫ (qValue A).map i'
  obtain ⟨h, hh⟩ := (localizedHomEquiv I I').surjective p
  obtain ⟨t, rfl⟩ := (HomotopyCategory.quotient (ModuleCat.{max u v} A) (.up ℤ)).map_surjective h
  rw [localizedHomEquiv_map] at hh
  have ht : (qValue A).map i ≫ (qValue A).map t = (qValue A).map i' := by
    rw [hh]
    simp [p]
  refine ⟨t, ht, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (localizedHomEquiv X I').injective
  rw [localizedHomEquiv_map, localizedHomEquiv_map, Functor.map_comp]
  exact ht

private lemma evaluation_natural (J : Ideal A) {I I' : compValue.{max u v} A} (t : I ⟶ I') :
    (restrictScalarsComplexValue (Ideal.Quotient.mk J)).map
      ((coinduceValue.{v} (Ideal.Quotient.mk J)).map t) ≫ evaluationValue.{v} (Ideal.Quotient.mk J) I' =
      evaluationValue.{v} (Ideal.Quotient.mk J) I ≫ t := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

private lemma coinducedDerivedComparison_natural (J : Ideal A)
    (G : Coinduction.{max u v} (Ideal.Quotient.mk J))
    {I I' : compValue.{max u v} A} (t : I ⟶ I') :
    (qValue (A ⧸ J)).map ((coinduceValue.{v} (Ideal.Quotient.mk J)).map t) ≫
      comparison (Ideal.Quotient.mk J) G.adjunction I' =
        comparison (Ideal.Quotient.mk J) G.adjunction I ≫ G.functor.map ((qValue A).map t) := by
  let f := Ideal.Quotient.mk J
  let t' := (coinduceValue.{v} f).map t
  let F := derivedRestrictScalarsValue f
  let R := restrictScalarsComplexValue f
  let E := derivedRestrictScalarsFactorsValue f
  let QA := qValue.{max u v} A
  let QB := qValue.{max u v} (A ⧸ J)
  apply (G.adjunction.homEquiv _ _).symm.injective
  rw [G.adjunction.homEquiv_naturality_left_symm, G.adjunction.homEquiv_naturality_right_symm]
  simp only [comparison, Equiv.symm_apply_apply]
  change F.map (QB.map t') ≫
      (E.hom.app (coinduced J I') ≫ QA.map (evaluationValue.{v} f I')) =
    (E.hom.app (coinduced J I) ≫ QA.map (evaluationValue.{v} f I)) ≫ QA.map t
  have hE : F.map (QB.map t') ≫ E.hom.app (coinduced J I') =
      E.hom.app (coinduced J I) ≫ QA.map (R.map t') := E.hom.naturality t'
  rw [← Category.assoc, hE, Category.assoc, Category.assoc, ← QA.map_comp, ← QA.map_comp,
    evaluation_natural J t]

private def replacementModelIso (J : Ideal A) (G : Coinduction.{max u v} (Ideal.Quotient.mk J))
    {X I : compValue.{max u v} A} (i : X ⟶ I) (hi : QuasiIso i) (hI : isKInjectiveValue I) :
    G.functor.obj ((qValue A).obj X) ≅ (qValue (A ⧸ J)).obj (coinduced J I) :=
  G.modelIso (Ideal.Quotient.mk J) I
    (@asIso _ _ _ _ ((qValue A).map i)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) i).2 hi)) hI

private lemma replacementModelIso_natural (J : Ideal A)
    (G : Coinduction.{max u v} (Ideal.Quotient.mk J))
    {X I I' : compValue.{max u v} A} (i : X ⟶ I) (i' : X ⟶ I')
    (hi : QuasiIso i) (hi' : QuasiIso i') (hI : isKInjectiveValue I) (hI' : isKInjectiveValue I')
    (t : I ⟶ I') (ht : (qValue A).map i ≫ (qValue A).map t = (qValue A).map i') :
    (replacementModelIso J G i hi hI).hom ≫
      (qValue (A ⧸ J)).map ((coinduceValue.{v} (Ideal.Quotient.mk J)).map t) =
        (replacementModelIso J G i' hi' hI').hom := by
  let f := Ideal.Quotient.mk J
  let _ := G.comparison_isIso I hI
  let _ := G.comparison_isIso I' hI'
  let E := asIso (comparison f G.adjunction I)
  let E' := asIso (comparison f G.adjunction I')
  let t' := (qValue (A ⧸ J)).map ((coinduceValue.{v} f).map t)
  have h : E.inv ≫ t' = G.functor.map ((qValue A).map t) ≫ E'.inv := by
    have hnat : t' ≫ E'.hom = E.hom ≫ G.functor.map ((qValue A).map t) :=
      coinducedDerivedComparison_natural J G t
    apply (cancel_epi E.hom).mp
    apply (cancel_mono E'.hom).mp
    simpa [Category.assoc] using hnat
  change (G.functor.map ((qValue A).map i) ≫ E.inv) ≫ t' =
    G.functor.map ((qValue A).map i') ≫ E'.inv
  rw [Category.assoc, h, ← G.functor.map_comp_assoc, ht]

private lemma replacementTop_natural (J : Ideal A) {a : List A}
    {ha : listIdeal a = J} (hra : RingTheory.Sequence.IsRegular A a)
    {I I' : compValue.{max u v} A} {i : scalarStalk.{u,v} (A := A) ⟶ I}
    {i' : scalarStalk.{u,v} (A := A) ⟶ I'}
    (C : ModelComparison J a ha i) (C' : ModelComparison J a ha i')
    {t : I ⟶ I'} (ht : Homotopy (i ≫ t) i')
    {e : (coinduced J I).homology (a.length : ℤ) ≅ determinantModule.{u,v} J a.length}
    {e' : (coinduced J I').homology (a.length : ℤ) ≅ determinantModule.{u,v} J a.length}
    (he : TopIdentification J C e) (he' : TopIdentification J C' e') :
    homologyMap ((coinduceValue.{v} (Ideal.Quotient.mk J)).map t) (a.length : ℤ) ≫ e'.hom =
      e.hom := by
  let c : ℤ := a.length
  let K := dualKoszul.{u,v} a
  let E := modelHomologyIso J C c
  let E' := modelHomologyIso J C' c
  let h := homologyMap ((coinduceValue.{v} (Ideal.Quotient.mk J)).map t) c
  have heq := modelHomologyIso_natural J C C' ht c
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hπ : Function.Surjective (K.homologyπ c) :=
    (ModuleCat.epi_iff_surjective (K.homologyπ c)).mp inferInstance
  obtain ⟨r, hr⟩ := (E.toLinearEquiv.surjective.comp hπ) z
  change E.hom (K.homologyπ c r) = z at hr
  have hr' : h z = E'.hom (K.homologyπ c r) := by
    have hx := congrArg (fun f => f (K.homologyπ c r)) heq
    change h (E.hom (K.homologyπ c r)) = _ at hx
    rw [hr] at hx
    exact hx
  apply ULift.ext
  apply LinearMap.ext
  intro x
  obtain ⟨w, rfl⟩ := reduceWedge_surj J a ha hra x
  change (e'.hom (h z)).down (reduceWedge J a ha _ w) =
    (e.hom z).down (reduceWedge J a ha _ w)
  rw [hr', ← hr]
  exact (he' r w).trans (he r w).symm

private abbrev relativeObject (J : Ideal A) (G : Coinduction.{max u v} (Ideal.Quotient.mk J)) :=
  Specs.DerivedFormalization.KoszulRelativeDual.relativeDual J G

private def modelCohomologyIso (J : Ideal A) (G : Coinduction.{max u v} (Ideal.Quotient.mk J))
    {I : compValue.{max u v} A} (i : scalarStalk.{u,v} (A := A) ⟶ I)
    (hi : QuasiIso i) (hI : isKInjectiveValue I) (n : ℤ) :
    (derivedCohomologyValue (A ⧸ J) n).obj (relativeObject J G) ≅ (coinduced J I).homology n :=
  (derivedCohomologyValue (A ⧸ J) n).mapIso (replacementModelIso J G i hi hI) ≪≫
    (cohomologyFactorsValue (A ⧸ J) n).app (coinduced J I)

private lemma modelCohomologyIso_natural (J : Ideal A)
    (G : Coinduction.{max u v} (Ideal.Quotient.mk J))
    {I I' : compValue.{max u v} A} (i : scalarStalk.{u,v} (A := A) ⟶ I)
    (i' : scalarStalk.{u,v} (A := A) ⟶ I')
    (hi : QuasiIso i) (hi' : QuasiIso i') (hI : isKInjectiveValue I) (hI' : isKInjectiveValue I')
    (t : I ⟶ I') (ht : (qValue A).map i ≫ (qValue A).map t = (qValue A).map i') (n : ℤ) :
    (modelCohomologyIso J G i hi hI n).hom ≫
        homologyMap ((coinduceValue.{v} (Ideal.Quotient.mk J)).map t) n =
      (modelCohomologyIso J G i' hi' hI' n).hom := by
  let f := Ideal.Quotient.mk J
  let H := derivedCohomologyValue (A ⧸ J) n
  let Q := qValue (A ⧸ J)
  let E := cohomologyFactorsValue (A ⧸ J) n
  let s := (coinduceValue.{v} f).map t
  have hE : H.map (Q.map s) ≫ E.hom.app (coinduced J I') =
      E.hom.app (coinduced J I) ≫ homologyMap s n := E.hom.naturality s
  change (H.map (replacementModelIso J G i hi hI).hom ≫ E.hom.app (coinduced J I)) ≫
    homologyMap s n = H.map (replacementModelIso J G i' hi' hI').hom ≫ E.hom.app (coinduced J I')
  rw [Category.assoc, ← hE, ← H.map_comp_assoc, replacementModelIso_natural J G i i' hi hi' hI hI' t ht]

private lemma normalizedCohomology_independent (J : Ideal A)
    (G : Coinduction.{max u v} (Ideal.Quotient.mk J)) {a : List A}
    {ha : listIdeal a = J} (hra : RingTheory.Sequence.IsRegular A a)
    {I I' : compValue.{max u v} A} (i : scalarStalk.{u,v} (A := A) ⟶ I)
    (i' : scalarStalk.{u,v} (A := A) ⟶ I')
    (hi : QuasiIso i) (hi' : QuasiIso i') (hI : isKInjectiveValue I) (hI' : isKInjectiveValue I')
    (C : ModelComparison J a ha i) (C' : ModelComparison J a ha i')
    {e : (coinduced J I).homology (a.length : ℤ) ≅ determinantModule.{u,v} J a.length}
    {e' : (coinduced J I').homology (a.length : ℤ) ≅ determinantModule.{u,v} J a.length}
    (he : TopIdentification J C e) (he' : TopIdentification J C' e') :
    modelCohomologyIso J G i hi hI (a.length : ℤ) ≪≫ e =
      modelCohomologyIso J G i' hi' hI' (a.length : ℤ) ≪≫ e' := by
  obtain ⟨t, ht, ⟨hh⟩⟩ := replacementComparison i i' hi hI'
  have h := replacementTop_natural J hra C C' hh he he'
  have h' := modelCohomologyIso_natural J G i i' hi hi' hI hI' t ht (a.length : ℤ)
  apply Iso.ext
  simp only [Iso.trans_hom]
  rw [← h, ← Category.assoc, h']

private abbrev shiftedStalk (J : Ideal A) (c : ℕ) (M : ModuleCat.{max u v} (A ⧸ J)) :=
  ((derivedStalkValue (A ⧸ J)).obj M)⟦-(c : ℤ)⟧

private def normalizedTop (J : Ideal A) (c : ℕ) {X : derivedValue.{max u v} (A ⧸ J)}
    {M : ModuleCat.{max u v} (A ⧸ J)} (e : X ≅ shiftedStalk J c M) :
    (derivedCohomologyValue (A ⧸ J) (c : ℤ)).obj X ≅ M :=
  (derivedCohomologyValue (A ⧸ J) (c : ℤ)).mapIso (e ≪≫ ((singleShift J c).app M).symm) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} (A ⧸ J)) (c : ℤ)).app M

/-- Truncating to a single degree yields the unique isomorphism inducing the
given identification on cohomology. -/
private lemma normalizedTruncation (J : Ideal A) (c : ℕ)
    {X : derivedValue.{max u v} (A ⧸ J)} {M : ModuleCat.{max u v} (A ⧸ J)}
    (hX : ∀ n : ℤ, n ≠ (c : ℤ) → IsZero ((derivedCohomologyValue (A ⧸ J) n).obj X))
    (ω : (derivedCohomologyValue (A ⧸ J) (c : ℤ)).obj X ≅ M) :
    ∃! e : X ≅ shiftedStalk J c M, normalizedTop J c e = ω := by
  let H := derivedCohomologyValue (A ⧸ J) (c : ℤ)
  let S := DerivedCategory.singleFunctor (ModuleCat.{max u v} (A ⧸ J)) (c : ℤ)
  let α := DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} (A ⧸ J)) (c : ℤ)
  let σ := (singleShift J c).app M
  have : X.IsGE (c : ℤ) := (DerivedCategory.isGE_iff X _).2
    (fun n hn => hX n (ne_of_lt hn))
  have : X.IsLE (c : ℤ) := (DerivedCategory.isLE_iff X _).2
    (fun n hn => hX n (ne_of_gt hn))
  obtain ⟨V, ⟨eV⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X (c : ℤ)
  let η := (α.app V).symm ≪≫ (H.mapIso eV).symm ≪≫ ω
  let e := eV ≪≫ S.mapIso η ≪≫ σ
  have hnat : H.map (S.map η.hom) ≫ (α.app M).hom = (α.app V).hom ≫ η.hom :=
    α.hom.naturality η.hom
  have he : normalizedTop J c e = ω := by
    apply Iso.ext
    change H.map (e.hom ≫ σ.inv) ≫ (α.app M).hom = ω.hom
    have he' : e.hom ≫ σ.inv = eV.hom ≫ S.map η.hom := by
      dsimp only [e, Iso.trans_hom, Functor.mapIso_hom]
      simp
    rw [he', H.map_comp_assoc, hnat]
    simp [η]
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (cancel_mono σ.inv).mp
  apply (cancel_epi eV.inv).mp
  have H_inj : Function.Injective (H.map : (S.obj V ⟶ S.obj M) → _) := by
    intro f g h
    have _ : (S ⋙ H).Faithful := Functor.Faithful.of_iso α.symm
    obtain ⟨f', rfl⟩ := S.map_surjective f
    obtain ⟨g', rfl⟩ := S.map_surjective g
    exact congrArg S.map ((S ⋙ H).map_injective h)
  apply H_inj
  have h := congrArg Iso.hom (he'.trans he.symm)
  change H.map (e'.hom ≫ σ.inv) ≫ (α.app M).hom =
    H.map (e.hom ≫ σ.inv) ≫ (α.app M).hom at h
  have h' := (cancel_mono (α.app M).hom).mp h
  rw [H.map_comp eV.inv (e'.hom ≫ σ.inv), H.map_comp eV.inv (e.hom ≫ σ.inv), h']

theorem relativeDual : relativeDualType.{u,v} := by
  intro A _ _ J G a ha hra
  obtain ⟨I, i, _, hi, hI, _⟩ := kInjectiveReplacement.{u,v} (scalarStalk.{u,v} (A := A))
  obtain ⟨hvanish, e, he, _⟩ := coinducedCohomology.{u,v} J a ha hra I i hi hI
  obtain ⟨C⟩ := modelComparison.{u,v} J a ha hra I i hi hI
  let c := a.length
  let Y := relativeObject J G
  let ω := modelCohomologyIso J G i hi hI (c : ℤ) ≪≫ e
  have vanish (n : ℤ) (hn : n ≠ (c : ℤ)) :
      IsZero ((derivedCohomologyValue (A ⧸ J) n).obj Y) :=
    (hvanish n hn).of_iso (modelCohomologyIso J G i hi hI n)
  obtain ⟨E, hE, uniq⟩ := normalizedTruncation J c vanish ω
  refine ⟨vanish, E, ?_, ?_⟩
  · intro b hb hlen hrb I' i' hi' hI' Cb
    obtain ⟨_, e', he', _⟩ := coinducedCohomology.{u,v} J a ha hra I' i' hi' hI'
    obtain ⟨C'⟩ := modelComparison.{u,v} J a ha hra I' i' hi' hI'
    have h := normalizedCohomology_independent J G hra i i' hi hi' hI hI' C C'
      (he a ha rfl hra C) (he' a ha rfl hra C')
    change TopIdentification J Cb
      (hlen ▸ ((modelCohomologyIso J G i' hi' hI' (c : ℤ)).symm ≪≫ normalizedTop J c E))
    rw [hE]
    change ω = _ at h
    rw [h, Iso.symm_self_id_assoc]
    exact he' b hb hlen hrb Cb
  · intro E' hE'
    apply uniq
    have hp := hE' a ha rfl hra I i hi hI C
    change TopIdentification J C
      ((modelCohomologyIso J G i hi hI (c : ℤ)).symm ≪≫ normalizedTop J c E') at hp
    have h := topIdentification_unique J hra C hp (he a ha rfl hra C)
    have hp' := congrArg (fun p => modelCohomologyIso J G i hi hI (c : ℤ) ≪≫ p) h
    rw [Iso.self_symm_id_assoc] at hp'
    exact hp'

/-- The relative dual is concentrated in degree c and is isomorphic to the
shifted dual of the conormal determinant line. -/
theorem relativeDualExistence (J : Ideal A) [IsNoetherianRing A]
    (G : Coinduction.{max u v} (Ideal.Quotient.mk J))
    (a : List A) (h : listIdeal a = J) (ha : RingTheory.Sequence.IsRegular A a) :
    (∀ n : ℤ, n ≠ (a.length : ℤ) → IsZero ((derivedCohomologyValue _ n).obj
      (relativeObject J G))) ∧
    Nonempty (Specs.DerivedFormalization.KoszulRelativeDual.relativeDual J G ≅
      ((derivedStalkValue.{max u v} (A ⧸ J)).obj
        (determinantModule.{u,v} J a.length))⟦-(a.length : ℤ)⟧) := by
  obtain ⟨hv, e, _, _⟩ := relativeDual.{u,v} J G a h ha
  exact ⟨hv, ⟨e⟩⟩

end DerivedFormalization.KoszulRelativeDual
