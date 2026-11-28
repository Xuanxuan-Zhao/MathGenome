import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Geometric.TorusSatake
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusOrderedConvolution
import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.TorusWeights
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Monoidal.Braided.Transport

import MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusSymmetricConvolution
noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open scoped Classical DirectSum TensorProduct MonoidalCategory BraidedCategory

namespace RepTheorySurvey.Geometric.TorusSatake

open Analytic TorusPerverseSpecs TorusOrderedConvolutionSpecs TorusFusionSpecs
  TorusSymmetricConvolutionSpecs TorusSatakeSpecs
open RepTheorySurvey.Invariants.Specs.TorusWeights
open RepTheorySurvey.Invariants.TorusWeights (gradedEquivalence gradedWeight gradedWeight_apply
  tensorWeightIso tensorMap_isComoduleMap splitTorus)
open LinearAlgebraicGroups.WeightDecomposition (weightSpace tensorCoactionMap)

open private perverseEquivalence monomialPoint_bijective from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusPerverse
open private sectionsGermsIso sectionsGermsIso_π sheaf_injective_discrete singlePlus
  singlePlusMap singlePlusQIso from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Geometric.TorusOrderedConvolution
open private tensorCoaction_tmul from MathGenome.Internal.RepresentationTheoryDeepening.RepTheorySurvey.Invariants.TorusWeights

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

private def gradingFunctor (r : ℕ) : Graded r ⥤ FiniteGrading ℚ (Characters r) where
  obj V :=
    { piece := fun a ↦ fiber V.obj (Multiplicative.toAdd a)
      finiteDimensional := fun a ↦ V.property.1 (Multiplicative.toAdd a)
      finiteSupport := V.property.2.subset (by
        rintro a ⟨x, hx⟩ h
        exact hx ((ModuleCat.subsingleton_of_isZero h).elim x 0)) }
  map f a := (f.hom.app (Discrete.mk (Multiplicative.toAdd a))).hom

private def familyFunctor (r : ℕ) : FiniteGrading ℚ (Characters r) ⥤ Graded r where
  obj V :=
    ⟨Discrete.functor fun a ↦ V.piece (Multiplicative.ofAdd a),
      fun a ↦ V.finiteDimensional (Multiplicative.ofAdd a),
      V.finiteSupport.subset (by
        intro a ha
        by_contra h
        exact ha (ModuleCat.isZero_iff_subsingleton.mpr
          ⟨fun x y ↦ (not_ne_iff.mp fun hx ↦ h ⟨x, hx⟩).trans
            (not_ne_iff.mp fun hy ↦ h ⟨y, hy⟩).symm⟩))⟩
  map f := ⟨Discrete.natTrans fun a ↦ ModuleCat.ofHom (f (Multiplicative.ofAdd a.as))⟩
  map_id V := by
    ext ⟨a⟩ x
    rfl
  map_comp f h := by
    ext ⟨a⟩ x
    rfl

private def gradingEquivalence (r : ℕ) : Graded r ≌ FiniteGrading ℚ (Characters r) :=
  CategoryTheory.Equivalence.mk (gradingFunctor r) (familyFunctor r)
    (NatIso.ofComponents (fun V ↦ (ObjectProperty.fullyFaithfulι _).preimageIso
      (Discrete.natIso fun ⟨a⟩ ↦ Iso.refl (fiber V.obj a))) (by
        intro V W f
        ext ⟨a⟩ x
        rfl))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro V W f
      funext a
      simp
      rfl))

variable {r : ℕ} {g : StageGeometry r} {c : ContinuousJets r}

private abbrev stalksEquiv (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Heart r g c ≌ Graded r :=
  perverseEquivalence r g c

private def satakeEquiv (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Heart r g c ≌ Representations r :=
  (stalksEquiv r g c).trans ((gradingEquivalence r).trans
    (gradedEquivalence ℚ (Characters r)).symm)

private def stalkWeightIso (V : Heart r g c) (a : Labels r) :
    OrderedProduct.Stalk V a ≅ weightAt ((satakeEquiv r g c).functor.obj V) a :=
  (gradedWeight (fun b : Characters r ↦ OrderedProduct.Stalk V (Multiplicative.toAdd b))
    (Multiplicative.ofAdd a)).toModuleIso

private abbrev Pieces (V : Heart r g c) (a : Labels r) : Coeff.{0} :=
  OrderedProduct.Stalk V a

private def globalToProduct (V : Heart r g c) :
    (globalSections r g c).obj V ≅ ∏ᶜ Pieces V := by
  letI : DiscreteTopology (torusSpace r) := g.discrete
  let F := (cohomology (torusSpace r) 0).obj ((forgetPerverse r g c).obj V)
  let e : Labels r ≃ (⊤ : TopologicalSpace.Opens (torusSpace r)) :=
    (Equiv.ofBijective (monomialPoint r) (monomialPoint_bijective r)).trans
      (Equiv.subtypeUnivEquiv (fun _ ↦ trivial)).symm
  exact sectionsGermsIso F ⊤ ≪≫ (Pi.whiskerEquiv e (fun _ ↦ Iso.refl _)).symm

private theorem globalToProduct_π (V : Heart r g c) (a : Labels r) :
    (globalToProduct V).hom ≫ Pi.π (Pieces V) a = globalGerm V a := by
  letI : DiscreteTopology (torusSpace r) := g.discrete
  let F := (cohomology (torusSpace r) 0).obj ((forgetPerverse r g c).obj V)
  let e : Labels r ≃ (⊤ : TopologicalSpace.Opens (torusSpace r)) :=
    (Equiv.ofBijective (monomialPoint r) (monomialPoint_bijective r)).trans
      (Equiv.subtypeUnivEquiv (fun _ ↦ trivial)).symm
  change ((sectionsGermsIso F ⊤).hom ≫ Pi.map' e (fun i ↦ 𝟙 (Pieces V i))) ≫
    Pi.π (Pieces V) a = F.presheaf.germ ⊤ (monomialPoint r a) trivial
  rw [Category.assoc, Pi.map'_comp_π]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f ↦ f ≫ 𝟙 (Pieces V a)) (sectionsGermsIso_π F ⊤ (e a))).trans
      (Category.comp_id _))

private def sumToProduct (V : Heart r g c) : StalkSum V ≅ ∏ᶜ Pieces V := by
  let A (a : Labels r) := (Pieces V a : Type)
  let f : (⨁ a, A a) →ₗ[ℚ] (∀ a, A a) := DirectSum.coeFnLinearMap ℚ
  have hf : Function.Bijective f := by
    refine ⟨DFunLike.coe_injective, fun v ↦ ?_⟩
    let B := familySupport ((stalkFamily r g c).obj V)
    have hB : B.Finite := ((stalksEquiv r g c).functor.obj V).property.2
    refine ⟨DFinsupp.mk hB.toFinset (fun i ↦ v i.val), ?_⟩
    funext a
    by_cases ha : a ∈ B
    · exact DFinsupp.mk_of_mem (β := A) (x := fun i : (↑hB.toFinset : Set (Labels r)) ↦ v i.val)
        (hB.mem_toFinset.mpr ha)
    · have hz : IsZero (Pieces V a) := Classical.not_not.mp ha
      exact (ModuleCat.subsingleton_of_isZero hz).elim _ _
  exact (LinearEquiv.ofBijective f hf).toModuleIso ≪≫ (ModuleCat.piIsoPi (Pieces V)).symm

private theorem sumToProduct_π (V : Heart r g c) (a : Labels r) :
    (sumToProduct V).hom ≫ Pi.π (Pieces V) a =
      ModuleCat.ofHom (DirectSum.component ℚ (Labels r) (fun b ↦ (Pieces V b : Type)) a) := by
  simp only [sumToProduct, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    ModuleCat.piIsoPi_inv_kernel_ι]
  rfl

private def globalSumIso (V : Heart r g c) : StalkSum V ≅ (globalSections r g c).obj V :=
  sumToProduct V ≪≫ (globalToProduct V).symm

private theorem globalSumIso_germ (V : Heart r g c) (a : Labels r) :
    (globalSumIso V).inv ≫ ModuleCat.ofHom
      (DirectSum.component ℚ (Labels r) (fun b ↦ (Pieces V b : Type)) a) = globalGerm V a := by
  rw [← sumToProduct_π, globalSumIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_assoc, globalToProduct_π]

private def rightDerivedOnSingle {X : TopCat.{0}} [DiscreteTopology X] :
    DerivedCategory.Plus.singleFunctor (Sheaves X) 0 ⋙
      (sectionsOn (⊤ : TopologicalSpace.Opens X)).rightDerivedFunctorPlus ≅
    sectionsOn (⊤ : TopologicalSpace.Opens X) ⋙
      DerivedCategory.Plus.singleFunctor Coeff.{0} 0 := by
  let C := Sheaves X
  let F := sectionsOn (⊤ : TopologicalSpace.Opens X)
  let J : C ⥤ InjectiveObject C :=
    ObjectProperty.lift _ (𝟭 C) (sheaf_injective_discrete X)
  let I := InjectiveObject.ι C
  let U := F.rightDerivedFunctorPlusUnit
  have hu (A : C) : IsIso (U.app ((singlePlus C).obj A)) := by
    let L := (singlePlus (InjectiveObject C)).obj (J.obj A)
    let L' := I.mapCochainComplexPlus.obj L
    let i : L' ≅ (singlePlus C).obj A := (singlePlusMap I).app (J.obj A)
    haveI : IsIso (U.app L') := inferInstanceAs
      (IsIso (F.rightDerivedFunctorPlusUnit.app (I.mapCochainComplexPlus.obj L)))
    exact (NatTrans.isIso_app_iff_of_iso U i).mp inferInstance
  let u := Functor.whiskerLeft (singlePlus C) U
  haveI : IsIso u := @NatIso.isIso_of_isIso_app _ _ _ _ _ _ u hu
  exact Functor.isoWhiskerRight (singlePlusQIso C).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    (asIso u).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (singlePlusMap F) _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F (singlePlusQIso Coeff.{0})

private abbrev cohomologySheaf (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Heart r g c ⥤ Sheaves (torusSpace r) :=
  forgetPerverse r g c ⋙ cohomology (torusSpace r) 0

private def heartSingleIso (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    cohomologySheaf r g c ⋙ DerivedCategory.singleFunctor (Sheaves (torusSpace r)) 0 ≅
      forgetPerverse r g c := by
  let E := stalksEquiv r g c
  let F := forgetPerverse r g c
  let M := E.functor ⋙ gradedInclusion r ⋙ skyscraperProduct r
  let I := DerivedCategory.singleFunctor (Sheaves (torusSpace r)) 0
  let H := cohomology (torusSpace r) 0
  let e : M ⋙ I ≅ F := by
    let a : (E.functor ⋙ E.inverse) ⋙ F ≅ F :=
      Functor.isoWhiskerRight E.unitIso.symm F ≪≫ F.leftUnitor
    exact a
  let d : F ⋙ H ≅ M :=
    Functor.isoWhiskerRight e.symm H ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft M (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0) ≪≫
      M.rightUnitor
  exact Functor.isoWhiskerRight d I ≪≫ e

private def heartBoundedBelow (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Heart r g c ⥤ BoundedBelow (torusSpace r) :=
  cohomologySheaf r g c ⋙ DerivedCategory.Plus.singleFunctor (Sheaves (torusSpace r)) 0

private def heartBoundedBelowComparison (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    heartBoundedBelow r g c ⋙ DerivedCategory.Plus.ι ≅ forgetPerverse r g c :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
    (DerivedCategory.Plus.singleFunctorιIso _ 0) ≪≫ heartSingleIso r g c

private def derivedGlobalComparison (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    heartBoundedBelow r g c ⋙ derivedGlobalSections r ≅
      globalSections r g c ⋙ DerivedCategory.Plus.singleFunctor Coeff.{0} 0 := by
  letI : DiscreteTopology (torusSpace r) := g.discrete
  exact Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ rightDerivedOnSingle ≪≫
    (Functor.associator _ _ _).symm

private def stalkSumFunctor (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    Heart r g c ⥤ Coeff.{0} :=
  (satakeEquiv r g c).functor ⋙ underlying r

private abbrev stalkToSum (V : Heart r g c) (a : Labels r) :
    Pieces V a ⟶ (stalkSumFunctor r g c).obj V :=
  ModuleCat.ofHom (DirectSum.lof ℚ (Labels r) (fun b ↦ (Pieces V b : Type)) a)

private theorem globalGerm_naturality {V W : Heart r g c} (f : V ⟶ W) (a : Labels r) :
    (globalSections r g c).map f ≫ globalGerm W a =
      globalGerm V a ≫ ((stalkFamily r g c).map f).app (Discrete.mk a) := by
  exact (TopCat.Presheaf.stalkFunctor_map_germ
    ⊤ (monomialPoint r a) trivial ((cohomologySheaf r g c).map f).hom).symm

private def fiberComparison (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    globalSections r g c ≅ stalkSumFunctor r g c :=
  NatIso.ofComponents (fun V ↦ (globalSumIso V).symm) (by
    intro V W f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply DFinsupp.ext
    intro a
    have h := globalGerm_naturality f a
    rw [← globalSumIso_germ V a, ← globalSumIso_germ W a] at h
    exact congrArg (fun u : (globalSections r g c).obj V ⟶ Pieces W a ↦ u v) h)

private theorem stalkToSum_eq_weight (V : Heart r g c) (a : Labels r) :
    stalkToSum V a =
      (stalkWeightIso V a).hom ≫ weightInclusion ((satakeEquiv r g c).functor.obj V) a := by
  apply ModuleCat.hom_ext
  ext x
  simp only [stalkWeightIso, weightInclusion, ModuleCat.hom_comp, ModuleCat.hom_ofHom,
    LinearMap.comp_apply]
  change DirectSum.lof ℚ (Labels r) (fun b ↦ (Pieces V b : Type)) a x =
    (gradedWeight (fun b : Characters r ↦ Pieces V (Multiplicative.toAdd b))
      (Multiplicative.ofAdd a) x).val
  have e := congrArg (fun inst : DecidableEq (Labels r) ↦
    @DirectSum.lof ℚ _ (Labels r) (fun b ↦ (Pieces V b : Type)) _ _ inst a x)
      (Subsingleton.elim (inferInstance : DecidableEq (Labels r)) (fun a b ↦ Classical.propDecidable (a = b)))
  exact e.trans (gradedWeight_apply
    (fun b : Characters r ↦ Pieces V (Multiplicative.toAdd b)) (Multiplicative.ofAdd a) x).symm

@[reassoc]
private theorem stalkToSum_naturality {V W : Heart r g c} (f : V ⟶ W) (a : Labels r) :
    stalkToSum V a ≫ (stalkSumFunctor r g c).map f =
      ((stalkFamily r g c).map f).app (Discrete.mk a) ≫ stalkToSum W a := by
  apply ModuleCat.hom_ext
  ext x
  change DirectSum.lmap (R := ℚ) (fun b ↦ (((stalkFamily r g c).map f).app (Discrete.mk b)).hom)
    (DirectSum.lof ℚ (Labels r) (fun b ↦ (Pieces V b : Type)) a x) =
    DirectSum.lof ℚ (Labels r) (fun b ↦ (Pieces W b : Type)) a
      (((stalkFamily r g c).map f).app (Discrete.mk a) x)
  rw [DirectSum.lmap_lof]

private theorem stalkWeightIso_naturality {V W : Heart r g c} (f : V ⟶ W) (a : Labels r) :
    ((stalkFamily r g c).map f).app (Discrete.mk a) ≫
        (stalkWeightIso W a).hom ≫ weightInclusion ((satakeEquiv r g c).functor.obj W) a =
      (stalkWeightIso V a).hom ≫ weightInclusion ((satakeEquiv r g c).functor.obj V) a ≫
        (underlying r).map ((satakeEquiv r g c).functor.map f) := by
  have h := (stalkToSum_naturality f a).symm
  simp only [stalkToSum_eq_weight, Category.assoc, stalkSumFunctor, Functor.comp_map] at h
  exact h

private theorem fiberComparison_stalk (V : Heart r g c) (a : Labels r) :
    stalkSection (globalSumIso V) a ≫ (fiberComparison r g c).hom.app V =
      (stalkWeightIso V a).hom ≫ weightInclusion ((satakeEquiv r g c).functor.obj V) a := by
  change (stalkToSum V a ≫ (globalSumIso V).hom) ≫ (globalSumIso V).inv = _
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using stalkToSum_eq_weight V a

variable {D : OrderedGeometry r} {P : OrderedProduct D g c} {U : OrderedConstraints P}
  {σ : SwapsConvolution P}

private abbrev pairPieces (V W : Heart r g c) (p : Labels r × Labels r) : Coeff.{0} :=
  Pieces V p.1 ⊗ Pieces W p.2

private def sumTensorToPairs (V W : Heart r g c) :
    (stalkSumFunctor r g c).obj V ⊗ (stalkSumFunctor r g c).obj W ≅
      ∐ pairPieces V W :=
  (TensorProduct.directSum ℚ ℚ (fun a ↦ (Pieces V a : Type))
    (fun b ↦ (Pieces W b : Type))).toModuleIso ≪≫
      (ModuleCat.coprodIsoDirectSum (pairPieces V W)).symm

@[reassoc]
private theorem sumTensorToPairs_ι (V W : Heart r g c) (a b : Labels r) :
    (stalkToSum V a ⊗ₘ stalkToSum W b) ≫ (sumTensorToPairs V W).hom =
      Sigma.ι (pairPieces V W) (a, b) := by
  have h : (stalkToSum V a ⊗ₘ stalkToSum W b) ≫
      (TensorProduct.directSum ℚ ℚ (fun a ↦ (Pieces V a : Type))
        (fun b ↦ (Pieces W b : Type))).toModuleIso.hom =
      ModuleCat.ofHom (DirectSum.lof ℚ (Labels r × Labels r)
        (fun p ↦ (pairPieces V W p : Type)) (a, b)) := by
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro x y
    exact TensorProduct.directSum_lof_tmul_lof ℚ ℚ
      (M₁ := fun i ↦ (Pieces V i : Type)) (M₂ := fun i ↦ (Pieces W i : Type)) a x b y
  rw [sumTensorToPairs, Iso.trans_hom, Iso.symm_hom, ← Category.assoc, h]
  exact ModuleCat.lof_coprodIsoDirectSum_inv (pairPieces V W) (a, b)

private abbrev fiberPieces (V W : Heart r g c) (n : Labels r) : Coeff.{0} :=
  (fiberSum n).obj ((stalkFamily r g c).obj V, (stalkFamily r g c).obj W)

private def pairsToFibers (V W : Heart r g c) :
    (∐ pairPieces V W) ≅ ∐ fiberPieces V W where
  hom := Sigma.desc fun p ↦
    summand (p.1 + p.2) _ _ ⟨p, rfl⟩ ≫ Sigma.ι (fiberPieces V W) (p.1 + p.2)
  inv := Sigma.desc fun n ↦ Sigma.desc fun p : SumFiber n ↦ Sigma.ι (pairPieces V W) p.val
  hom_inv_id := by
    apply Sigma.hom_ext
    intro p
    simp [summand]
  inv_hom_id := by
    apply Sigma.hom_ext
    intro n
    apply Sigma.hom_ext
    rintro ⟨p, rfl⟩
    simp [summand]

private def sumTensorIso (P : OrderedProduct D g c) (V W : Heart r g c) :
    (stalkSumFunctor r g c).obj V ⊗ (stalkSumFunctor r g c).obj W ≅
      (stalkSumFunctor r g c).obj (P.convolution.obj (V, W)) :=
  sumTensorToPairs V W ≪≫ pairsToFibers V W ≪≫
    (Limits.Sigma.mapIso fun n : Labels r ↦ (P.stalkIso n).app (V, W)) ≪≫
    ModuleCat.coprodIsoDirectSum (Pieces (P.convolution.obj (V, W)))

@[reassoc]
private theorem sumTensorIso_ι (P : OrderedProduct D g c) (V W : Heart r g c) (a b : Labels r) :
    (stalkToSum V a ⊗ₘ stalkToSum W b) ≫ (sumTensorIso P V W).hom =
      P.includeSummand V W a b ≫ stalkToSum (P.convolution.obj (V, W)) (a + b) := by
  have hMap : (Limits.Sigma.mapIso (fun n : Labels r ↦ (P.stalkIso n).app (V, W))).hom =
      Limits.Sigma.map (fun n : Labels r ↦ (P.stalkIso n).hom.app (V, W)) := rfl
  simp only [sumTensorIso, Iso.trans_hom, pairsToFibers, Category.assoc, sumTensorToPairs_ι_assoc,
    Sigma.ι_comp_desc_assoc, hMap, Sigma.ι_map_assoc,
    OrderedProduct.includeSummand, stalkToSum]
  exact congrArg (fun f ↦ summand (a + b) _ _ ⟨(a, b), rfl⟩ ≫
      (P.stalkIso (a + b)).hom.app (V, W) ≫ f)
    (ModuleCat.ι_coprodIsoDirectSum_hom (Pieces (P.convolution.obj (V, W))) (a + b))

private theorem sumTensor_hom_ext (V W : Heart r g c) {A : Coeff.{0}}
    {f h : (stalkSumFunctor r g c).obj V ⊗ (stalkSumFunctor r g c).obj W ⟶ A}
    (e : ∀ a b, (stalkToSum V a ⊗ₘ stalkToSum W b) ≫ f =
      (stalkToSum V a ⊗ₘ stalkToSum W b) ≫ h) : f = h := by
  apply (cancel_epi (sumTensorToPairs V W).inv).mp
  apply Sigma.hom_ext
  rintro ⟨a, b⟩
  have k := sumTensorToPairs_ι V W a b
  rw [← k]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using e a b

/-- Use the actual ordered operations as the definitional data of the already
proved monoidal structure. The coherence laws depend only on those operations. -/
@[instance_reducible]
private def monoidalWithData {C : Type*} [Category C] (M : MonoidalCategory C)
    (d : MonoidalCategoryStruct C) (h : M.toMonoidalCategoryStruct = d) :
    MonoidalCategory C := by
  refine { toMonoidalCategoryStruct := d
           tensorHom_def := ?_
           id_tensorHom_id := ?_
           tensorHom_comp_tensorHom := ?_
           whiskerLeft_id := ?_
           id_whiskerRight := ?_
           associator_naturality := ?_
           leftUnitor_naturality := ?_
           rightUnitor_naturality := ?_
           pentagon := ?_
           triangle := ?_ }
  all_goals cases M; cases h; assumption

private theorem monoidalWithData_eq {C : Type*} [Category C] (M : MonoidalCategory C)
    (d : MonoidalCategoryStruct C) (h : M.toMonoidalCategoryStruct = d) :
    M = monoidalWithData M d h := by
  cases M
  cases h
  rfl

private def replaceStructure (S : SymmetricConvolution U σ) (M : MonoidalCategory (Heart r g c))
    (h : S.monoidal = M) (o : M.toMonoidalCategoryStruct = orderedMonoidalData U) :
    SymmetricConvolution U σ where
  monoidal := M
  ordered := o
  symmetric := h ▸ S.symmetric
  fusionBraiding := by
    subst M
    exact S.fusionBraiding

private def normalizeConvolution (S : SymmetricConvolution U σ) : SymmetricConvolution U σ :=
  replaceStructure S (monoidalWithData S.monoidal (orderedMonoidalData U) S.ordered)
    (monoidalWithData_eq S.monoidal (orderedMonoidalData U) S.ordered) rfl

private def scalarIso (U : OrderedConstraints P) :
    𝟙_ Coeff.{0} ≅ Pieces U.unit 0 :=
  eqToIso (by simp [pointUnit]) ≪≫ (U.unitStalk.app (Discrete.mk 0)).symm

private theorem unitStalkIsZero (U : OrderedConstraints P) (a : Labels r) (ha : a ≠ 0) :
    IsZero (Pieces U.unit a) :=
  (isZero_zero Coeff.{0}).of_iso
    (U.unitStalk.app (Discrete.mk a) ≪≫ eqToIso (by simp [pointUnit, ha]))

private def sumUnitIso (U : OrderedConstraints P) :
    𝟙_ Coeff.{0} ≅ (stalkSumFunctor r g c).obj U.unit := by
  refine scalarIso U ≪≫
    { hom := stalkToSum U.unit 0
      inv := ModuleCat.ofHom (DirectSum.component ℚ (Labels r)
        (fun a ↦ (Pieces U.unit a : Type)) 0)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact DFinsupp.single_eq_same
  · apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext (R := ℚ) (ι := Labels r) (M := fun a ↦ (Pieces U.unit a : Type))
    intro a
    apply LinearMap.ext
    intro x
    by_cases ha : a = 0
    · subst a
      change DirectSum.lof ℚ (Labels r) (fun b ↦ (Pieces U.unit b : Type)) 0
        (DirectSum.component ℚ (Labels r) (fun b ↦ (Pieces U.unit b : Type)) 0
          (DirectSum.lof ℚ (Labels r) (fun b ↦ (Pieces U.unit b : Type)) 0 x)) =
        DirectSum.lof ℚ (Labels r) (fun b ↦ (Pieces U.unit b : Type)) 0 x
      rw [DirectSum.component.lof_self]
    · have hx : x = 0 := (ModuleCat.subsingleton_of_isZero (unitStalkIsZero U a ha)).elim _ _
      subst x
      rw [map_zero, map_zero]

private theorem map_sum_hom_ext {I : Type} (A : I → Coeff.{0}) (G : Coeff.{0} ⥤ Coeff.{0})
    [PreservesColimit (Discrete.functor A) G] {X Y : Coeff.{0}} (i : (∐ A) ≅ X)
    {f h : G.obj X ⟶ Y}
    (e : ∀ a, G.map (Sigma.ι A a ≫ i.hom) ≫ f = G.map (Sigma.ι A a ≫ i.hom) ≫ h) :
    f = h := by
  apply (cancel_epi (G.map i.hom)).mp
  apply (cancel_epi (sigmaComparison G A)).mp
  apply Sigma.hom_ext
  intro a
  simpa only [Category.assoc, ι_comp_sigmaComparison_assoc, Functor.map_comp] using e a

private theorem sum_hom_ext_after (V : Heart r g c) (G : Coeff.{0} ⥤ Coeff.{0})
    [PreservesColimit (Discrete.functor (Pieces V)) G] {A : Coeff.{0}}
    {f h : G.obj ((stalkSumFunctor r g c).obj V) ⟶ A}
    (e : ∀ a, G.map (stalkToSum V a) ≫ f = G.map (stalkToSum V a) ≫ h) :
    f = h := by
  apply map_sum_hom_ext (Pieces V) G (ModuleCat.coprodIsoDirectSum (Pieces V))
  intro a
  rw [ModuleCat.ι_coprodIsoDirectSum_hom]
  exact e a

private theorem sumTriple_hom_ext (V W X : Heart r g c) {A : Coeff.{0}}
    {f h : ((stalkSumFunctor r g c).obj V ⊗ (stalkSumFunctor r g c).obj W) ⊗
      (stalkSumFunctor r g c).obj X ⟶ A}
    (e : ∀ a b d, ((stalkToSum V a ⊗ₘ stalkToSum W b) ⊗ₘ stalkToSum X d) ≫ f =
      ((stalkToSum V a ⊗ₘ stalkToSum W b) ⊗ₘ stalkToSum X d) ≫ h) : f = h := by
  apply map_sum_hom_ext (pairPieces V W)
    (MonoidalCategory.tensorRight ((stalkSumFunctor r g c).obj X)) (sumTensorToPairs V W).symm
  rintro ⟨a,b⟩
  have h₀ : Sigma.ι (pairPieces V W) (a, b) ≫ (sumTensorToPairs V W).inv =
      stalkToSum V a ⊗ₘ stalkToSum W b := by
    rw [← sumTensorToPairs_ι, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Iso.symm_hom, h₀]
  apply sum_hom_ext_after X (MonoidalCategory.tensorLeft (pairPieces V W (a, b)))
  intro d
  change (_ ◁ stalkToSum X d) ≫ ((stalkToSum V a ⊗ₘ stalkToSum W b) ▷ _) ≫ f =
    (_ ◁ stalkToSum X d) ≫ ((stalkToSum V a ⊗ₘ stalkToSum W b) ▷ _) ≫ h
  simp only [← MonoidalCategory.tensorHom_def'_assoc]
  exact e a b d

@[reassoc]
private theorem transport_stalkToSum (V : Heart r g c) {a b : Labels r} (e : a = b) :
    eqToHom (congrArg (Pieces V) e) ≫ stalkToSum V b = stalkToSum V a := by
  subst b
  simp

@[reassoc]
private theorem includeSummand_naturality (P : OrderedProduct D g c)
    {V V' W W' : Heart r g c} (f : V ⟶ V') (h : W ⟶ W') (a b : Labels r) :
    P.includeSummand V W a b ≫
        ((stalkFamily r g c).map (P.convolution.map (f, h))).app (Discrete.mk (a + b)) =
      (((stalkFamily r g c).map f).app (Discrete.mk a) ⊗ₘ
        ((stalkFamily r g c).map h).app (Discrete.mk b)) ≫ P.includeSummand V' W' a b := by
  let n := a + b
  let T := stalkFamily r g c
  let p : SumFiber n := ⟨(a, b), rfl⟩
  have e := (P.stalkIso n).hom.naturality (show (V, W) ⟶ (V', W') from (f, h))
  change (fiberSum n).map (T.map f, T.map h) ≫ (P.stalkIso n).hom.app (V', W') =
    (P.stalkIso n).hom.app (V, W) ≫ (T.map (P.convolution.map (f, h))).app (Discrete.mk n) at e
  change summand n _ _ p ≫ _ ≫ _ = _ ≫ summand n _ _ p ≫ _
  rw [← e]
  simp only [fiberSum, summand, Sigma.ι_map_assoc]
  rfl

private abbrev convolutionMonoidal (S : SymmetricConvolution U σ) :
    MonoidalCategory (Heart r g c) :=
  (normalizeConvolution S).monoidal

private abbrev convolutionSymmetric (S : SymmetricConvolution U σ) :
    @SymmetricCategory (Heart r g c) _ (convolutionMonoidal S) :=
  (normalizeConvolution S).symmetric

@[reassoc]
private theorem sumAssociator_stalk (U : OrderedConstraints P) (V W X : Heart r g c)
    (a b d : Labels r) :
    P.leftSummand V W X a b d ≫ stalkToSum _ (a + b + d) ≫
      (stalkSumFunctor r g c).map (U.associator.hom.app (V, W, X)) =
    (α_ (Pieces V a) (Pieces W b) (Pieces X d)).hom ≫
      (𝟙 (Pieces V a) ⊗ₘ P.includeSummand W X b d) ≫
      P.includeSummand V (P.convolution.obj (W, X)) a (b + d) ≫
      stalkToSum _ (a + (b + d)) := by
  have e := U.associator_stalk V W X (D.triples.symm (a, b, d))
  dsimp only at e
  rw [D.triples.apply_symm_apply] at e
  rw [stalkToSum_naturality, ← Category.assoc, e]
  simp only [OrderedProduct.rightSummand, Category.assoc]
  let C := P.convolution.obj (V, P.convolution.obj (W, X))
  exact congrArg (fun f ↦ (α_ (Pieces V a) (Pieces W b) (Pieces X d)).hom ≫
    (𝟙 (Pieces V a) ⊗ₘ P.includeSummand W X b d) ≫
    P.includeSummand V (P.convolution.obj (W, X)) a (b + d) ≫ f)
      (transport_stalkToSum C (add_assoc a b d).symm)

@[reassoc]
private theorem tensor_comp_left {X Y Z A B : Coeff.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : A ⟶ B) :
    ((f ≫ g) ⊗ₘ h) = (f ⊗ₘ 𝟙 A) ≫ (g ⊗ₘ h) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

@[reassoc]
private theorem tensor_comp_right {X Y Z A B : Coeff.{0}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : A ⟶ B) :
    (h ⊗ₘ (f ≫ g)) = (𝟙 A ⊗ₘ f) ≫ (h ⊗ₘ g) := by
  rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

private theorem stalkTransport_map {V W : Heart r g c} (f : V ⟶ W)
    {a b : Labels r} (e : a = b) :
    eqToHom (congrArg (Pieces V) e) ≫
      ((stalkFamily r g c).map f).app (Discrete.mk b) ≫ stalkToSum W b =
      stalkToSum V a ≫ (stalkSumFunctor r g c).map f := by
  subst b
  simpa only [eqToHom_refl, Category.id_comp] using (stalkToSum_naturality f a).symm

private theorem stalkMap_id (V : Heart r g c) (a : Labels r) :
    ((stalkFamily r g c).map (𝟙 V)).app (Discrete.mk a) = 𝟙 (Pieces V a) :=
  congrArg (fun f : (stalkFamily r g c).obj V ⟶ (stalkFamily r g c).obj V ↦
    f.app (Discrete.mk a)) ((stalkFamily r g c).map_id V)

set_option maxHeartbeats 800000 in
private def sumCoreMonoidal (S : SymmetricConvolution U σ) :
    letI := convolutionMonoidal S
    (stalkSumFunctor r g c).CoreMonoidal := by
  letI := convolutionMonoidal S
  let F := stalkSumFunctor r g c
  refine {
    εIso := sumUnitIso U
    μIso := sumTensorIso P
    μIso_hom_natural_left := ?_
    μIso_hom_natural_right := ?_
    associativity := ?_
    left_unitality := ?_
    right_unitality := ?_ }
  · intro V W f X
    apply sumTensor_hom_ext V X
    intro a b
    rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      stalkToSum_naturality, Category.comp_id]
    change _ ≫ (sumTensorIso P W X).hom = _ ≫
      (sumTensorIso P V X).hom ≫ F.map (P.convolution.map (f, 𝟙 X))
    rw [tensor_comp_left_assoc, sumTensorIso_ι, sumTensorIso_ι_assoc]
    rw [stalkToSum_naturality, includeSummand_naturality_assoc]
    rw [stalkMap_id]
  · intro V W X f
    apply sumTensor_hom_ext X V
    intro a b
    rw [← MonoidalCategory.id_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      stalkToSum_naturality, Category.comp_id]
    change _ ≫ (sumTensorIso P X W).hom = _ ≫
      (sumTensorIso P X V).hom ≫ F.map (P.convolution.map (𝟙 X, f))
    rw [tensor_comp_right_assoc, sumTensorIso_ι, sumTensorIso_ι_assoc]
    rw [stalkToSum_naturality, includeSummand_naturality_assoc]
    rw [stalkMap_id]
  · intro V W X
    apply sumTriple_hom_ext V W X
    intro a b d
    change _ ≫ _ ≫ (sumTensorIso P (P.convolution.obj (V, W)) X).hom ≫
      F.map (U.associator.hom.app (V, W, X)) =
        _ ≫ _ ≫ _ ≫ (sumTensorIso P V (P.convolution.obj (W, X))).hom
    rw [← MonoidalCategory.tensorHom_id, MonoidalCategory.tensorHom_comp_tensorHom_assoc,
      sumTensorIso_ι, Category.comp_id, tensor_comp_left_assoc, sumTensorIso_ι_assoc,
      MonoidalCategory.associator_naturality_assoc, ← MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc, sumTensorIso_ι, Category.comp_id,
      tensor_comp_right_assoc]
    refine (sumAssociator_stalk U V W X a b d).trans ?_
    exact congrArg (fun k ↦ (α_ (Pieces V a) (Pieces W b) (Pieces X d)).hom ≫
      (𝟙 (Pieces V a) ⊗ₘ P.includeSummand W X b d) ≫ k)
        (sumTensorIso_ι P V (P.convolution.obj (W, X)) a (b + d)).symm
  · intro V
    apply sum_hom_ext_after V (MonoidalCategory.tensorLeft (𝟙_ Coeff.{0}))
    intro a
    let u : P.convolution.obj (U.unit, V) ⟶ V := U.leftUnitor.hom.app V
    change (𝟙_ Coeff.{0} ◁ stalkToSum V a) ≫ (λ_ (F.obj V)).hom =
      (𝟙_ Coeff.{0} ◁ stalkToSum V a) ≫ (sumUnitIso U).hom ▷ F.obj V ≫
        (sumTensorIso P U.unit V).hom ≫ F.map u
    have h := MonoidalCategory.leftUnitor_naturality (stalkToSum V a)
    refine h.trans ?_
    erw [← MonoidalCategory.tensorHom_def'_assoc]
    change _ = (((scalarIso U).hom ≫ stalkToSum U.unit 0) ⊗ₘ stalkToSum V a) ≫
      (sumTensorIso P U.unit V).hom ≫ F.map u
    rw [tensor_comp_left_assoc, sumTensorIso_ι_assoc]
    have e := congrArg (fun f : (𝟙_ Coeff.{0} ⊗ Pieces V a : Coeff.{0}) ⟶ Pieces V a ↦
      f ≫ stalkToSum V a) (U.leftUnitor_stalk V a)
    simp only [Category.assoc] at e
    erw [stalkTransport_map u (zero_add a)] at e
    exact e.symm
  · intro V
    apply sum_hom_ext_after V (MonoidalCategory.tensorRight (𝟙_ Coeff.{0}))
    intro a
    let u : P.convolution.obj (V, U.unit) ⟶ V := U.rightUnitor.hom.app V
    change (stalkToSum V a ▷ 𝟙_ Coeff.{0}) ≫ (ρ_ (F.obj V)).hom =
      (stalkToSum V a ▷ 𝟙_ Coeff.{0}) ≫ F.obj V ◁ (sumUnitIso U).hom ≫
        (sumTensorIso P V U.unit).hom ≫ F.map u
    have h := MonoidalCategory.rightUnitor_naturality (stalkToSum V a)
    refine h.trans ?_
    erw [← MonoidalCategory.tensorHom_def_assoc]
    change _ = (stalkToSum V a ⊗ₘ ((scalarIso U).hom ≫ stalkToSum U.unit 0)) ≫
      (sumTensorIso P V U.unit).hom ≫ F.map u
    rw [tensor_comp_right_assoc, sumTensorIso_ι_assoc]
    have e := congrArg (fun f : (Pieces V a ⊗ 𝟙_ Coeff.{0} : Coeff.{0}) ⟶ Pieces V a ↦
      f ≫ stalkToSum V a) (U.rightUnitor_stalk V a)
    simp only [Category.assoc] at e
    erw [stalkTransport_map u (add_zero a)] at e
    exact e.symm

private theorem geometricBraiding (S : SymmetricConvolution U σ) (V W : Heart r g c) :
    letI := convolutionMonoidal S
    letI := convolutionSymmetric S
    (β_ V W).hom = σ.hom.app (V, W) := by
  letI := convolutionMonoidal S
  letI := convolutionSymmetric S
  have h := (normalizeConvolution S).fusionBraiding V W
  change (β_ V W) = Iso.refl _ ≪≫ σ.app (V, W) ≪≫ (Iso.refl _).symm at h
  have h' := congrArg Iso.hom h
  simp only [Iso.trans_hom, Iso.refl_hom, Iso.symm_hom, Iso.refl_inv, Category.comp_id] at h'
  exact h'.trans (Category.id_comp (σ.hom.app (V, W)))

private theorem composeFlipWithSummands {C : Type*} [Category C]
    {A A' X X' Y Y' Z : C} {i : A ⟶ X} {j : A' ⟶ Y} {m : X ⟶ Y'}
    {b : A ⟶ A'} {h : Y ⟶ Y'} {s : X ⟶ X'} {t : X' ⟶ Z} {w : Y' ⟶ Z}
    {v : Y ⟶ Z} (ht : s ≫ t = m ≫ w) (hm : i ≫ m = b ≫ j ≫ h)
    (hw : h ≫ w = v) : i ≫ s ≫ t = b ≫ j ≫ v := by
  rw [ht, ← Category.assoc, hm, Category.assoc, Category.assoc j, hw]

private theorem flipStalkInSum (hs : FlipsConvolutionSummands P σ)
    (V W : Heart r g c) (a b : Labels r) :
    P.includeSummand V W a b ≫ stalkToSum (P.convolution.obj (V, W)) (a + b) ≫
      (stalkSumFunctor r g c).map (σ.hom.app (V, W)) =
    (β_ (Pieces V a) (Pieces W b)).hom ≫ P.includeSummand W V b a ≫
      stalkToSum (P.convolution.obj (W, V)) (b + a) :=
  composeFlipWithSummands (i := P.includeSummand V W a b)
    (stalkToSum_naturality (σ.hom.app (V, W)) (a + b)) (hs V W a b)
    (transport_stalkToSum (P.convolution.obj (W, V)) (add_comm b a))

private theorem sumFlip_stalks (hs : FlipsConvolutionSummands P σ) (V W : Heart r g c) :
    (sumTensorIso P V W).hom ≫ (stalkSumFunctor r g c).map (σ.hom.app (V, W)) =
      (β_ ((stalkSumFunctor r g c).obj V) ((stalkSumFunctor r g c).obj W)).hom ≫
        (sumTensorIso P W V).hom := by
  apply sumTensor_hom_ext V W
  intro a b
  let k : P.convolution.obj (V, W) ⟶ P.convolution.obj (W, V) := σ.hom.app (V, W)
  let F := stalkSumFunctor r g c
  let ι := stalkToSum V a
  let ι' := stalkToSum W b
  let β := (β_ (Pieces V a) (Pieces W b)).hom
  calc
    _ = P.includeSummand V W a b ≫ stalkToSum (P.convolution.obj (V, W)) (a + b) ≫
        F.map k := sumTensorIso_ι_assoc P V W a b _
    _ = β ≫ P.includeSummand W V b a ≫ stalkToSum (P.convolution.obj (W, V)) (b + a) :=
      flipStalkInSum hs V W a b
    _ = β ≫ (ι' ⊗ₘ ι) ≫ (sumTensorIso P W V).hom :=
      congrArg (fun f ↦ β ≫ f) (sumTensorIso_ι P W V b a).symm
    _ = _ := (BraidedCategory.braiding_naturality_assoc ι ι' _).symm

private theorem sumBraiding_stalks (S : SymmetricConvolution U σ)
    (hs : FlipsConvolutionSummands P σ) :
    letI := convolutionMonoidal S
    letI := convolutionSymmetric S
    ∀ V W : Heart r g c,
      (sumTensorIso P V W).hom ≫ (stalkSumFunctor r g c).map (β_ V W).hom =
      (β_ ((stalkSumFunctor r g c).obj V) ((stalkSumFunctor r g c).obj W)).hom ≫
        (sumTensorIso P W V).hom := by
  letI := convolutionMonoidal S
  letI := convolutionSymmetric S
  intro V W
  exact (congrArg (fun k : P.convolution.obj (V, W) ⟶ P.convolution.obj (W, V) ↦
    (sumTensorIso P V W).hom ≫ (stalkSumFunctor r g c).map k) (geometricBraiding S V W)).trans
      (sumFlip_stalks hs V W)

@[instance_reducible]
private def sumBraided (S : SymmetricConvolution U σ) (hs : FlipsConvolutionSummands P σ) :
    letI := convolutionMonoidal S
    letI := convolutionSymmetric S
    (stalkSumFunctor r g c).Braided := by
  letI := convolutionMonoidal S
  letI := convolutionSymmetric S
  exact { (sumCoreMonoidal S).toMonoidal with braided := sumBraiding_stalks S hs }

private abbrev satakeObject (V : Heart r g c) :=
  (satakeEquiv r g c).functor.obj V

private theorem stalkToSum_coaction (V : Heart r g c) (a : Labels r) (v : Pieces V a) :
    (satakeObject V).coaction.coaction ((stalkToSum V a).hom v) =
    (stalkToSum V a).hom v ⊗ₜ[ℚ] MonoidAlgebra.of ℚ (Characters r) (Multiplicative.ofAdd a) := by
  have h := congrArg (fun f : Pieces V a ⟶ (stalkSumFunctor r g c).obj V ↦ f.hom v)
    (stalkToSum_eq_weight V a)
  change (stalkToSum V a).hom v =
    ((stalkWeightIso V a).hom.hom v : weightSpace (satakeObject V).coaction
      (Multiplicative.ofAdd a)).val at h
  rw [h]
  exact LinearAlgebraicGroups.WeightDecomposition.mem_weightSpace.mp
    ((stalkWeightIso V a).hom.hom v).property

private theorem sumUnit_coaction (U : OrderedConstraints P) (x : (𝟙_ Coeff.{0})) :
    (satakeObject U.unit).coaction.coaction ((sumUnitIso U).hom.hom x) =
      (sumUnitIso U).hom.hom x ⊗ₜ[ℚ] MonoidAlgebra.of ℚ (Characters r) 1 :=
  stalkToSum_coaction U.unit 0 ((scalarIso U).hom.hom x)

private theorem sumTensor_coaction (P : OrderedProduct D g c) (V W : Heart r g c) :
    ((satakeObject (P.convolution.obj (V, W))).coaction.coaction).comp (sumTensorIso P V W).hom.hom =
      ((sumTensorIso P V W).hom.hom.rTensor (coordinateAlgebra r)).comp
        (tensorCoactionMap (satakeObject V).coaction (satakeObject W).coaction) := by
  apply congrArg (fun f : (stalkSumFunctor r g c).obj V ⊗ (stalkSumFunctor r g c).obj W ⟶
      ModuleCat.of ℚ ((satakeObject (P.convolution.obj (V, W))).space ⊗[ℚ]
        coordinateAlgebra r) ↦ f.hom)
  refine (show ModuleCat.ofHom _ = ModuleCat.ofHom _ from ?_)
  apply sumTensor_hom_ext V W
  intro a b
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  let v := (stalkToSum V a).hom x
  let w := (stalkToSum W b).hom y
  let j := (sumTensorIso P V W).hom.hom
  have hj : j (v ⊗ₜ[ℚ] w) =
      (stalkToSum (P.convolution.obj (V, W)) (a + b)).hom
        ((P.includeSummand V W a b).hom (x ⊗ₜ[ℚ] y)) := by
    have h := congrArg (fun f : Pieces V a ⊗ Pieces W b ⟶
      (stalkSumFunctor r g c).obj (P.convolution.obj (V, W)) ↦ f.hom (x ⊗ₜ[ℚ] y))
      (sumTensorIso_ι P V W a b)
    exact h
  change (satakeObject (P.convolution.obj (V, W))).coaction.coaction (j (v ⊗ₜ[ℚ] w)) =
    j.rTensor (coordinateAlgebra r)
      (tensorCoactionMap (satakeObject V).coaction (satakeObject W).coaction (v ⊗ₜ[ℚ] w))
  have hr : tensorCoactionMap (satakeObject V).coaction (satakeObject W).coaction (v ⊗ₜ[ℚ] w) =
      (v ⊗ₜ[ℚ] w) ⊗ₜ[ℚ] MonoidAlgebra.of ℚ (Characters r) (Multiplicative.ofAdd (a + b)) := by
    let T := tensorWeightIso (satakeObject V).coaction (satakeObject W).coaction
    have hv : v ∈ weightSpace (satakeObject V).coaction (Multiplicative.ofAdd a) :=
      LinearAlgebraicGroups.WeightDecomposition.mem_weightSpace.mpr (stalkToSum_coaction V a x)
    have hw : w ∈ weightSpace (satakeObject W).coaction (Multiplicative.ofAdd b) :=
      LinearAlgebraicGroups.WeightDecomposition.mem_weightSpace.mpr (stalkToSum_coaction W b y)
    exact (DFunLike.congr_fun T.coaction_eq (v ⊗ₜ[ℚ] w)).symm.trans
      (tensorCoaction_tmul T hv hw)
  rw [hr, LinearMap.rTensor_tmul, hj, stalkToSum_coaction]

@[instance_reducible]
private def transportBraided {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {F G : C ⥤ D} [F.Braided] (i : F ≅ G) : G.Braided := by
  letI : G.Monoidal := Functor.Monoidal.transport i
  letI : NatTrans.IsMonoidal i.hom := Functor.Monoidal.natTransIsMonoidal_of_transport i
  exact { (inferInstance : G.Monoidal) with
    braided := (Functor.LaxBraided.ofNatIso i).braided }

private theorem transportBraided_monoidal {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {F G : C ⥤ D} [F.Braided] (i : F ≅ G) :
    letI := transportBraided i
    NatTrans.IsMonoidal i.hom := by
  exact Functor.Monoidal.natTransIsMonoidal_of_transport i

section Transport

variable {C D A : Type*} [Category C] [Category D] [Category A]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalCategory A] [SymmetricCategory A]
variable (e : C ≌ D)

variable {F : C ⥤ A} {G : Monoidal.Transported e ⥤ A} (i : F ≅ (Monoidal.equivalenceTransported e).functor ⋙ G)

private def inverseComparison : (Monoidal.equivalenceTransported e).inverse ⋙ F ≅ G :=
  Functor.isoWhiskerLeft (Monoidal.equivalenceTransported e).inverse i ≪≫ (Monoidal.equivalenceTransported e).invFunIdAssoc G

@[instance_reducible]
private def transportedBraided [F.Braided] : G.Braided :=
  transportBraided (inverseComparison e i)

private abbrev transportedCompositeLax [F.Braided] :
    ((Monoidal.equivalenceTransported e).functor ⋙ G).LaxMonoidal :=
  letI := transportedBraided e i
  inferInstance

private def transportedComparison : F ≅ (Monoidal.equivalenceTransported e).functor ⋙ G :=
  F.leftUnitor.symm ≪≫ Functor.isoWhiskerRight (Monoidal.equivalenceTransported e).unitIso F ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft (Monoidal.equivalenceTransported e).functor (inverseComparison e i)

private theorem transportedComparison_monoidal [F.Braided] :
    letI := transportedBraided e i
    NatTrans.IsMonoidal (transportedComparison e i).hom := by
  letI := transportedBraided e i
  letI : NatTrans.IsMonoidal (inverseComparison e i).hom :=
    transportBraided_monoidal (inverseComparison e i)
  change NatTrans.IsMonoidal (F.leftUnitor.inv ≫
    Functor.whiskerRight (Monoidal.equivalenceTransported e).unit F ≫ (Functor.associator (Monoidal.equivalenceTransported e).functor (Monoidal.equivalenceTransported e).inverse F).hom ≫
    Functor.whiskerLeft (Monoidal.equivalenceTransported e).functor (inverseComparison e i).hom)
  infer_instance

private theorem inverse_ε :
    LaxMonoidal.ε (Monoidal.equivalenceTransported e).inverse = (Monoidal.equivalenceTransported e).unitIso.hom.app (𝟙_ C) := rfl

private theorem inverse_μ (X Y : Monoidal.Transported e) :
    LaxMonoidal.μ (Monoidal.equivalenceTransported e).inverse X Y = (Monoidal.equivalenceTransported e).unitIso.hom.app
      ((Monoidal.equivalenceTransported e).inverse.obj X ⊗ (Monoidal.equivalenceTransported e).inverse.obj Y) := rfl

private theorem transported_unit [F.Braided] :
    letI := transportedBraided e i
    LaxMonoidal.ε G = LaxMonoidal.ε F ≫ i.hom.app (𝟙_ C) := by
  letI := transportedBraided e i
  calc
    LaxMonoidal.ε G =
      LaxMonoidal.ε ((Monoidal.equivalenceTransported e).inverse ⋙ F) ≫ (inverseComparison e i).hom.app (𝟙_ _) :=
        Functor.Monoidal.transport_ε (inverseComparison e i)
    _ = _ := by
      simp only [LaxMonoidal.comp_ε, inverse_ε, inverseComparison, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Equivalence.invFunIdAssoc_hom_app,
        Category.assoc]
      rw [i.hom.naturality_assoc]
      change LaxMonoidal.ε F ≫ i.hom.app (𝟙_ C) ≫ G.map
        ((Monoidal.equivalenceTransported e).functor.map ((Monoidal.equivalenceTransported e).unitIso.hom.app (𝟙_ C))) ≫
          G.map ((Monoidal.equivalenceTransported e).counit.app ((Monoidal.equivalenceTransported e).functor.obj (𝟙_ C))) = _
      rw [← G.map_comp, (Monoidal.equivalenceTransported e).functor_unitIso_comp, G.map_id]
      exact congrArg (fun k ↦ LaxMonoidal.ε F ≫ k) (Category.comp_id (i.hom.app (𝟙_ C)))

private theorem transported_tensor [F.Braided] (X Y : Monoidal.Transported e) :
    letI := transportedBraided e i
    LaxMonoidal.μ G X Y =
      ((inverseComparison e i).inv.app X ⊗ₘ (inverseComparison e i).inv.app Y) ≫
        LaxMonoidal.μ F ((Monoidal.equivalenceTransported e).inverse.obj X) ((Monoidal.equivalenceTransported e).inverse.obj Y) ≫
          i.hom.app ((Monoidal.equivalenceTransported e).inverse.obj X ⊗ (Monoidal.equivalenceTransported e).inverse.obj Y) := by
  letI := transportedBraided e i
  calc
    LaxMonoidal.μ G X Y =
      ((inverseComparison e i).inv.app X ⊗ₘ (inverseComparison e i).inv.app Y) ≫
        LaxMonoidal.μ ((Monoidal.equivalenceTransported e).inverse ⋙ F) X Y ≫ (inverseComparison e i).hom.app (X ⊗ Y) :=
        Functor.Monoidal.transport_μ (inverseComparison e i) X Y
    _ = _ := by
      simp only [LaxMonoidal.comp_μ, inverse_μ, inverseComparison, Iso.trans_hom, NatTrans.comp_app,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Equivalence.invFunIdAssoc_hom_app,
        Category.assoc]
      rw [i.hom.naturality_assoc]
      let T := (Monoidal.equivalenceTransported e).inverse.obj X ⊗ (Monoidal.equivalenceTransported e).inverse.obj Y
      change _ ≫ _ ≫ i.hom.app T ≫ G.map ((Monoidal.equivalenceTransported e).functor.map ((Monoidal.equivalenceTransported e).unitIso.hom.app T)) ≫
        G.map ((Monoidal.equivalenceTransported e).counit.app ((Monoidal.equivalenceTransported e).functor.obj T)) = _
      rw [← G.map_comp, (Monoidal.equivalenceTransported e).functor_unitIso_comp, G.map_id]
      exact congrArg (fun k ↦
        ((inverseComparison e i).inv.app X ⊗ₘ (inverseComparison e i).inv.app Y) ≫
        LaxMonoidal.μ F ((Monoidal.equivalenceTransported e).inverse.obj X)
          ((Monoidal.equivalenceTransported e).inverse.obj Y) ≫ k)
        (Category.comp_id (i.hom.app T))

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalCategory A] [SymmetricCategory A] in
private theorem transportedComparison_app (X : C) :
    (transportedComparison e i).hom.app X = i.hom.app X := by
  simp only [transportedComparison, inverseComparison, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.id_comp, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Equivalence.invFunIdAssoc_hom_app]
  erw [i.hom.naturality_assoc]
  change _ ≫ G.map ((Monoidal.equivalenceTransported e).functor.map
    ((Monoidal.equivalenceTransported e).unitIso.hom.app X)) ≫
      G.map ((Monoidal.equivalenceTransported e).counitIso.hom.app
        ((Monoidal.equivalenceTransported e).functor.obj X)) = _
  rw [← G.map_comp]
  have h := (Monoidal.equivalenceTransported e).functor_unitIso_comp X
  exact (congrArg (fun m ↦ i.hom.app X ≫ G.map m) h).trans
    ((congrArg (fun f ↦ i.hom.app X ≫ f) (G.map_id _)).trans (Category.comp_id _))

omit [MonoidalCategory C] [SymmetricCategory C] [MonoidalCategory A] [SymmetricCategory A] in
private theorem inverseComparison_inv_app (X : Monoidal.Transported e) :
    (inverseComparison e i).inv.app X =
      G.map ((Monoidal.equivalenceTransported e).counitIso.inv.app X) ≫
        i.inv.app ((Monoidal.equivalenceTransported e).inverse.obj X) := by
  simp [inverseComparison]

end Transport

private abbrev transportedEquivalenceBraided {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [SymmetricCategory C] (e : C ≌ D) :
    letI : MonoidalCategory D := Monoidal.transport e
    letI : SymmetricCategory D := Monoidal.Transported.instSymmetricCategory e
    e.functor.Braided :=
  inferInstanceAs (Monoidal.equivalenceTransported e).functor.Braided

private abbrev repMonoidal (S : SymmetricConvolution U σ) :
    MonoidalCategory (Representations r) :=
  @Monoidal.transport (Heart r g c) _ (convolutionMonoidal S) (Representations r) _
    (satakeEquiv r g c)

private abbrev repSymmetric (S : SymmetricConvolution U σ) :
    @SymmetricCategory (Representations r) _ (repMonoidal S) :=
  @Monoidal.Transported.instSymmetricCategory (Heart r g c) _ (Representations r) _
    (satakeEquiv r g c) (convolutionMonoidal S) (convolutionSymmetric S)

private abbrev satakeBraided (S : SymmetricConvolution U σ) :
    letI := convolutionMonoidal S
    letI := convolutionSymmetric S
    letI := repMonoidal S
    letI := repSymmetric S
    (satakeEquiv r g c).functor.Braided :=
  @transportedEquivalenceBraided (Heart r g c) (Representations r) _ _
    (convolutionMonoidal S) (convolutionSymmetric S) (satakeEquiv r g c)

private def forgetIdentity (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    stalkSumFunctor r g c ≅ (Monoidal.equivalenceTransported (satakeEquiv r g c)).functor ⋙
      (show Monoidal.Transported (satakeEquiv r g c) ⥤ Coeff.{0} from underlying r) :=
  Iso.refl _

@[instance_reducible]
private def repForgetBraided (S : SymmetricConvolution U σ) (flip : FlipsConvolutionSummands P σ) :
    letI := repMonoidal S
    letI := repSymmetric S
    (underlying r).Braided :=
  @transportedBraided (Heart r g c) (Representations r) Coeff.{0} _ _ _
    (convolutionMonoidal S) (convolutionSymmetric S) _ _ (satakeEquiv r g c)
    (stalkSumFunctor r g c) (underlying r) (forgetIdentity r g c) (sumBraided S flip)

private def compareTensorFunctor (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    stalkSumFunctor r g c ≅ (satakeEquiv r g c).functor ⋙ underlying r :=
  @transportedComparison (Heart r g c) (Representations r) Coeff.{0} _ _ _
    (satakeEquiv r g c) (stalkSumFunctor r g c) (underlying r) (forgetIdentity r g c)

private theorem compareTensorFunctor_hom (V : Heart r g c) :
    (compareTensorFunctor r g c).hom.app V = 𝟙 ((stalkSumFunctor r g c).obj V) :=
  @transportedComparison_app (Heart r g c) (Representations r) Coeff.{0} _ _ _
    (satakeEquiv r g c) (stalkSumFunctor r g c) (underlying r) (forgetIdentity r g c) V

private abbrev sumLax (S : SymmetricConvolution U σ)
    (flip : FlipsConvolutionSummands P σ) :
    letI := convolutionMonoidal S
    (stalkSumFunctor r g c).LaxMonoidal :=
  letI := convolutionMonoidal S
  letI := convolutionSymmetric S
  (sumBraided S flip).toLaxBraided.toLaxMonoidal

private abbrev repCompositeLax (S : SymmetricConvolution U σ)
    (flip : FlipsConvolutionSummands P σ) :
    letI := convolutionMonoidal S
    ((satakeEquiv r g c).functor ⋙ underlying r).LaxMonoidal :=
  @transportedCompositeLax (Heart r g c) (Representations r) Coeff.{0} _ _ _
    (convolutionMonoidal S) (convolutionSymmetric S) _ _ (satakeEquiv r g c)
    (stalkSumFunctor r g c) (underlying r) (forgetIdentity r g c) (sumBraided S flip)

set_option maxHeartbeats 430000 in
private theorem compareTensorFunctor_monoidal (S : SymmetricConvolution U σ)
    (flip : FlipsConvolutionSummands P σ) :
    @NatTrans.IsMonoidal (Heart r g c) _ (convolutionMonoidal S) Coeff.{0} _ _
      (stalkSumFunctor r g c) ((satakeEquiv r g c).functor ⋙ underlying r)
      (compareTensorFunctor r g c).hom (sumLax S flip)
      (repCompositeLax S flip) :=
  @transportedComparison_monoidal (Heart r g c) (Representations r) Coeff.{0} _ _ _
    (convolutionMonoidal S) (convolutionSymmetric S) _ _ (satakeEquiv r g c)
    (stalkSumFunctor r g c) (underlying r) (forgetIdentity r g c) (sumBraided S flip)

private theorem repForget_unit (S : SymmetricConvolution U σ)
    (flip : FlipsConvolutionSummands P σ) :
    letI := repMonoidal S
    letI := repSymmetric S
    letI := repForgetBraided S flip
    LaxMonoidal.ε (underlying r) = (sumUnitIso U).hom := by
  letI := convolutionMonoidal S
  letI := convolutionSymmetric S
  letI := sumBraided S flip
  have h := @transported_unit (Heart r g c) (Representations r) Coeff.{0} _ _ _
    (convolutionMonoidal S) (convolutionSymmetric S) _ _ (satakeEquiv r g c)
    (stalkSumFunctor r g c) (underlying r) (forgetIdentity r g c) (sumBraided S flip)
  exact h.trans (Category.comp_id (sumUnitIso U).hom)

private theorem repForget_tensor (S : SymmetricConvolution U σ)
    (flip : FlipsConvolutionSummands P σ) (X Y : Representations r) :
    letI := repMonoidal S
    letI := repSymmetric S
    letI := repForgetBraided S flip
    LaxMonoidal.μ (underlying r) X Y =
      ((underlying r).map ((satakeEquiv r g c).counitIso.inv.app X) ⊗ₘ
        (underlying r).map ((satakeEquiv r g c).counitIso.inv.app Y)) ≫
        (sumTensorIso P ((satakeEquiv r g c).inverse.obj X)
          ((satakeEquiv r g c).inverse.obj Y)).hom := by
  letI := convolutionMonoidal S
  letI := convolutionSymmetric S
  letI := sumBraided S flip
  let E := satakeEquiv r g c
  let i := forgetIdentity r g c
  have h := @transported_tensor (Heart r g c) (Representations r) Coeff.{0} _ _ _
    (convolutionMonoidal S) (convolutionSymmetric S) _ _ E
    (stalkSumFunctor r g c) (underlying r) i (sumBraided S flip) X Y
  have e (Z : Representations r) : (inverseComparison E i).inv.app Z =
      (underlying r).map (E.counitIso.inv.app Z) :=
    (inverseComparison_inv_app E i Z).trans (Category.comp_id _)
  refine h.trans ((congrArg₂ (fun f h ↦ (f ⊗ₘ h) ≫
    (sumTensorIso P (E.inverse.obj X) (E.inverse.obj Y)).hom ≫
      i.hom.app (P.convolution.obj (E.inverse.obj X, E.inverse.obj Y))) (e X) (e Y)).trans ?_)
  exact congrArg (fun f ↦
    ((underlying r).map (E.counitIso.inv.app X) ⊗ₘ
      (underlying r).map (E.counitIso.inv.app Y)) ≫ f)
    (Category.comp_id (sumTensorIso P (E.inverse.obj X) (E.inverse.obj Y)).hom)

private def representationTensor (S : SymmetricConvolution U σ)
    (flip : FlipsConvolutionSummands P σ) : RepresentationTensor r where
  monoidal := repMonoidal S
  symmetric := repSymmetric S
  forgetBraided := repForgetBraided S flip
  unitCoaction := by
    intro x
    have h := repForget_unit S flip
    rw [h]
    exact sumUnit_coaction U x
  tensorCoaction := by
    intro X Y
    rw [repForget_tensor S flip X Y]
    let E := satakeEquiv r g c
    let V := E.inverse.obj X
    let W := E.inverse.obj Y
    let f := (E.counitIso.inv.app X).val
    let h := (E.counitIso.inv.app Y).val
    let A := coordinateAlgebra r
    let j := (sumTensorIso P V W).hom.hom
    let m := TensorProduct.map f h
    let T := tensorWeightIso X.coaction Y.coaction
    let T' := tensorWeightIso (satakeObject V).coaction (satakeObject W).coaction
    have e := tensorMap_isComoduleMap T T' f h
      (E.counitIso.inv.app X).property (E.counitIso.inv.app Y).property
    change (m.rTensor A).comp T.coaction.coaction = T'.coaction.coaction.comp m at e
    rw [T.coaction_eq, T'.coaction_eq] at e
    let ρ := (satakeObject (P.convolution.obj (V, W))).coaction.coaction
    change ρ.comp (j.comp m) = ((j.comp m).rTensor A).comp
      (tensorCoactionMap X.coaction Y.coaction)
    calc
      _ = (ρ.comp j).comp m := (LinearMap.comp_assoc _ _ _).symm
      _ = (j.rTensor A).comp ((tensorCoactionMap (satakeObject V).coaction
          (satakeObject W).coaction).comp m) := by
        rw [sumTensor_coaction P V W, LinearMap.comp_assoc]
      _ = _ := by rw [← e, LinearMap.rTensor_comp, LinearMap.comp_assoc]

private theorem monoidalTransportComparison {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {F G H : C ⥤ D} [F.Braided] [H.LaxMonoidal] (i : F ≅ G) (j : F ≅ H)
    (hj : NatTrans.IsMonoidal j.hom) :
    letI := transportBraided i
    NatTrans.IsMonoidal (i.symm ≪≫ j).hom := by
  letI := transportBraided i
  letI : NatTrans.IsMonoidal i.hom := transportBraided_monoidal i
  letI := hj
  change NatTrans.IsMonoidal (i.inv ≫ j.hom)
  infer_instance

private abbrev globalBraided (S : SymmetricConvolution U σ) (flip : FlipsConvolutionSummands P σ) :
    letI := convolutionMonoidal S
    letI := convolutionSymmetric S
    (globalSections r g c).Braided :=
  letI := convolutionMonoidal S
  letI := convolutionSymmetric S
  letI := sumBraided S flip
  transportBraided (fiberComparison r g c).symm

private abbrev globalLax (S : SymmetricConvolution U σ)
    (flip : FlipsConvolutionSummands P σ) :
    letI := convolutionMonoidal S
    (globalSections r g c).LaxMonoidal :=
  letI := convolutionMonoidal S
  letI := convolutionSymmetric S
  (globalBraided S flip).toLaxBraided.toLaxMonoidal

private def finalFiberIso (r : ℕ) (g : StageGeometry r) (c : ContinuousJets r) :
    globalSections r g c ≅ (satakeEquiv r g c).functor ⋙ underlying r :=
  fiberComparison r g c ≪≫ compareTensorFunctor r g c

private theorem finalFiberIso_monoidal (S : SymmetricConvolution U σ)
    (flip : FlipsConvolutionSummands P σ) :
    @NatTrans.IsMonoidal (Heart r g c) _ (convolutionMonoidal S) Coeff.{0} _ _
      (globalSections r g c) ((satakeEquiv r g c).functor ⋙ underlying r)
      (finalFiberIso r g c).hom (globalLax S flip)
      (repCompositeLax S flip) :=
  letI := convolutionMonoidal S
  letI := convolutionSymmetric S
  @monoidalTransportComparison (Heart r g c) Coeff.{0} _ _
    (convolutionMonoidal S) _ (convolutionSymmetric S).toBraidedCategory _
    (stalkSumFunctor r g c) (globalSections r g c) ((satakeEquiv r g c).functor ⋙ underlying r)
    (sumBraided S flip) (repCompositeLax S flip)
    (fiberComparison r g c).symm (compareTensorFunctor r g c)
    (compareTensorFunctor_monoidal S flip)

private def satakeComparison (S : SymmetricConvolution U σ)
    (flip : FlipsConvolutionSummands P σ) : SatakeEquivalence (normalizeConvolution S) where
  representationTensor := representationTensor S flip
  equivalence := satakeEquiv r g c
  braided := satakeBraided S
  stalkWeight := stalkWeightIso
  stalkWeight_naturality := stalkWeightIso_naturality
  boundedBelow := heartBoundedBelow r g c
  boundedBelowComparison := heartBoundedBelowComparison r g c
  derivedComparison := derivedGlobalComparison r g c
  sumIso := globalSumIso
  sumIso_germ := globalSumIso_germ
  globalBraided := globalBraided S flip
  fiberIso := finalFiberIso r g c
  fiberIso_monoidal := finalFiberIso_monoidal S flip
  fiberIso_weight := by
    intro V a
    simp only [finalFiberIso, Iso.trans_hom, NatTrans.comp_app, compareTensorFunctor_hom,
      Category.comp_id]
    exact fiberComparison_stalk V a
  globalUnit := by
    let i := fiberComparison r g c
    change (scalarIso U).hom ≫ stalkSection (globalSumIso U.unit) 0 ≫
        (globalSections r g c).map (eqToHom (rfl : U.unit = U.unit)) =
      (sumUnitIso U).hom ≫ i.inv.app U.unit
    rw [eqToHom_refl, (globalSections r g c).map_id, Category.comp_id]
    exact (Category.assoc (scalarIso U).hom (stalkToSum U.unit 0)
      (globalSumIso U.unit).hom).symm
  globalTensor := by
    intro V W a b
    let i := fiberComparison r g c
    let T := P.convolution.obj (V, W)
    change (stalkSection (globalSumIso V) a ⊗ₘ stalkSection (globalSumIso W) b) ≫
      (i.hom.app V ⊗ₘ i.hom.app W) ≫ (sumTensorIso P V W).hom ≫ i.inv.app T ≫
      (globalSections r g c).map (eqToHom (rfl : T = T)) =
        P.includeSummand V W a b ≫ stalkSection (globalSumIso T) (a + b)
    rw [eqToHom_refl, (globalSections r g c).map_id, Category.comp_id,
      MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    have hk (X : Heart r g c) (n : Labels r) :
        stalkSection (globalSumIso X) n ≫ i.hom.app X = stalkToSum X n := by
      change (stalkToSum X n ≫ (globalSumIso X).hom) ≫ (globalSumIso X).inv = _
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [hk V a, hk W b, sumTensorIso_ι_assoc]
    rfl

/-- Assemble the split-torus Satake equivalence from the proved symmetric
convolution interface. -/
theorem torusSatake_conditional (symmetricConvolution : TorusSymmetricConvolution) :
    TorusSatake := by
  intro r
  obtain ⟨D, g, c, P, U, σ, ⟨S⟩, flip, localGeometry, specialization⟩ :=
    symmetricConvolution r
  obtain ⟨_, split⟩ := splitTorus ℚ (Characters r) (Fin r) (MulEquiv.refl _)
  exact ⟨split, D, g, c, P, U, σ, normalizeConvolution S, flip, localGeometry,
    specialization, ⟨satakeComparison S flip⟩⟩

end RepTheorySurvey.Geometric.TorusSatake

theorem _root_.«RepTheorySurvey».«Geometric».«TorusSatake».«torusSatake» : _root_.«RepTheorySurvey».«Geometric».«TorusSatakeSpecs».«TorusSatake» :=
  @_root_.«RepTheorySurvey».«Geometric».«TorusSatake».«torusSatake_conditional» (@_root_.«RepTheorySurvey».«Geometric».«TorusSymmetricConvolution».«torusSymmetricConvolution»)
