import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.Monoidal
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Complexes.PushoutProductGenerators
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Model.Brown
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorHomAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorMonoidal
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainRingTransport
import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.AlgebraicTopology.ModelCategory.Transport

import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorTransport
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomologicalComplex HomotopicalAlgebra MonoidalCategory
open scoped ZeroObject

universe u a

namespace DerivedFormalization.Model.Complexes

open Specs.ComplexMonoidal Specs.ComplexGenerators Specs.ComplexProjective
open _root_.Specs.DerivedFormalization
open CochainTensorMonoidal (cochainMonoidalValue)
open CochainTensorHomAdjunction (homFromValue)
open CochainTensorTransport (adequateModelType closedAdjunctionType curryingType ringComparisonType)
open CochainRingTransport (complexFunctorValue complexEquivalenceValue)
open Cochains (compValue)

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

section Monoidal

variable {C : Type*} [Category* C] [MonoidalCategory C] [HasPushouts C]

private lemma productInl {X Y U V : C} (f : X ⟶ Y) (g : U ⟶ V) :
    pushout.inl (f ▷ U) (X ◁ g) ≫ (Arrow.mk f □ Arrow.mk g).hom = Y ◁ g :=
  pushout.inl_desc ..

private lemma productInr {X Y U V : C} (f : X ⟶ Y) (g : U ⟶ V) :
    pushout.inr (f ▷ U) (X ◁ g) ≫ (Arrow.mk f □ Arrow.mk g).hom = f ▷ V :=
  pushout.inr_desc ..

variable [HasInitial C] [BraidedCategory C] [MonoidalClosed C]

private def initialProduct (X : C) {U V : C} (g : U ⟶ V) :
    Arrow.mk (X ◁ g) ≅ (Arrow.mk (initial.to X) □ Arrow.mk g) := by
  let f := initial.to X
  have hU : IsInitial ((⊥_ C) ⊗ U) :=
    initialIsInitial.isInitialObj (tensorRight U) _
  have hV : IsInitial ((⊥_ C) ⊗ V) :=
    initialIsInitial.isInitialObj (tensorRight V) _
  haveI : IsIso ((⊥_ C) ◁ g) := isIso_of_isInitial hU hV _
  haveI : IsIso (pushout.inl (f ▷ U) ((⊥_ C) ◁ g)) :=
    (IsPushout.of_hasPushout (f ▷ U) ((⊥_ C) ◁ g)).isIso_inl_of_isIso
  exact Arrow.isoMk (asIso (pushout.inl (f ▷ U) ((⊥_ C) ◁ g))) (Iso.refl _) (by
    change pushout.inl (f ▷ U) ((⊥_ C) ◁ g) ≫ (Arrow.mk f □ Arrow.mk g).hom =
      (X ◁ g) ≫ 𝟙 (X ⊗ V)
    rw [Category.comp_id]
    exact productInl f g)

end Monoidal

section Unit

variable {C : Type*} [Category* C] [ModelCategory C]
  [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

private lemma unitComparison
    (hP : ∀ {X Y U V : C} (f : X ⟶ Y) (g : U ⟶ V),
      cofibrations C f → cofibrations C g →
      (weakEquivalences C f ∨ weakEquivalences C g) → weakEquivalences C (Arrow.mk f □ Arrow.mk g).hom)
    (hUnit : IsCofibrant (𝟙_ C))
    {Q : C} (q : Q ⟶ 𝟙_ C) (hQ : IsCofibrant Q) (hq : weakEquivalences C q)
    (X : C) (hX : IsCofibrant X) :
    weakEquivalences C ((q ▷ X) ≫ (λ_ X).hom) ∧
      weakEquivalences C ((X ◁ q) ≫ (ρ_ X).hom) := by
  let F : CofibrantObject C ⥤ C := CofibrantObject.ι ⋙ tensorLeft X
  have hF ⦃S T : CofibrantObject C⦄ (g : S ⟶ T)
      (hg : trivialCofibrations C (CofibrantObject.ι.map g)) :
      weakEquivalences C (F.map g) := by
    change weakEquivalences C (X ◁ (CofibrantObject.ι.map g))
    apply ((weakEquivalences C).arrow_mk_iso_iff
      (initialProduct X (CofibrantObject.ι.map g))).2
    exact hP (initial.to X) _ ((cofibration_iff _).mp hX) hg.1 (Or.inr hg.2)
  let q' : (⟨Q, hQ⟩ : CofibrantObject C) ⟶ ⟨𝟙_ C, hUnit⟩ :=
    ObjectProperty.homMk q
  have hLeft : weakEquivalences C (X ◁ q) :=
    Model.brown_cofibrant (weakEquivalences C) F hF q' hq
  have hRight : weakEquivalences C (q ▷ X) := by
    apply ((weakEquivalences C).arrow_mk_iso_iff
      (Arrow.isoMk' (q ▷ X) (X ◁ q) (β_ Q X) (β_ (𝟙_ C) X)
        (BraidedCategory.braiding_naturality_left q X).symm)).2
    exact hLeft
  exact ⟨(weakEquivalences C).comp_mem _ _ hRight ((weakEquivalences C).of_isIso _),
    (weakEquivalences C).comp_mem _ _ hLeft ((weakEquivalences C).of_isIso _)⟩

end Unit

section Native

attribute [local instance] cochainMonoidalValue

variable {A : Type u} [CommRing A]

private lemma nativeProduct_eq {X Y U V : Cochains A} (f : X ⟶ Y) (g : U ⟶ V) :
    (Arrow.mk f □ Arrow.mk g).hom = pushoutProduct f g := rfl

private lemma generatorII (n m : ℤ) :
    projectiveCofibrations A (pushoutProduct (iGeneratorValue A n) (iGeneratorValue A m)) := by
  obtain ⟨s, e, hs, _, _⟩ := pushoutProductII A n m
  have hg : I A (iGeneratorValue A (n + m)) := ⟨n + m⟩
  have hi : projectiveCofibrations A (iGeneratorValue A (n + m)) := by
    rw [projectiveCofibrations, ← i_rlp A]
    exact (I A).le_llp_rlp _ hg
  change ((degreewiseSurjective A ⊓ quasiIso (ModuleCat A) (.up ℤ)).llp)
    (pushoutProduct (iGeneratorValue A n) (iGeneratorValue A m))
  exact MorphismProperty.of_isPushout hs.flip hi

private lemma generatorIJ (n m : ℤ) :
    (degreewiseSurjective A).llp
      (pushoutProduct (iGeneratorValue A n) (jGeneratorValue A m)) := by
  obtain ⟨_, _, hc, hw⟩ := pushoutProductIJ A n m
  rw [projectiveTrivialCofibrations_eq_llp]
  exact ⟨hc, hw⟩

private lemma generatorJI (n m : ℤ) :
    (degreewiseSurjective A).llp
      (pushoutProduct (jGeneratorValue A m) (iGeneratorValue A n)) := by
  obtain ⟨_, _, hc, hw⟩ := pushoutProductJI A n m
  rw [projectiveTrivialCofibrations_eq_llp]
  exact ⟨hc, hw⟩

/-- In a closed braided category, the two pullback-Hom tests move the lifting
problem to either input. The left lifting class of the test map is closed
under coproducts, pushouts, sequential composition and retracts. -/
private lemma extendProduct [BraidedCategory (Cochains A)] [MonoidalClosed (Cochains A)]
    (P Q W : MorphismProperty (Cochains A))
    (h : ∀ {X Y U V : Cochains A} (f : X ⟶ Y) (g : U ⟶ V),
      P f → Q g → W.llp (Arrow.mk f □ Arrow.mk g).hom)
    {X Y U V : Cochains A} (f : X ⟶ Y) (g : U ⟶ V)
    (hf : ((coproducts.{u} P).pushouts.transfiniteCompositionsOfShape ℕ).retracts f)
    (hg : ((coproducts.{u} Q).pushouts.transfiniteCompositionsOfShape ℕ).retracts g) :
    W.llp (Arrow.mk f □ Arrow.mk g).hom := by
  intro S T p hp
  apply Arrow.PushoutProduct.hasLiftingProperty_mk_iff'.2
  apply P.retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp ℕ _ hf
  intro X' Y' f' hf'
  apply Arrow.PushoutProduct.hasLiftingProperty_mk_iff'.1
  apply Arrow.PushoutProduct.hasLiftingProperty_mk_iff.2
  apply Q.retracts_transfiniteCompositionsOfShape_pushouts_coproducts_le_llp_rlp ℕ _ hg
  intro U' V' g' hg'
  exact Arrow.PushoutProduct.hasLiftingProperty_mk_iff.1 (h f' g' hf' hg' p hp)

private lemma nativeProductAxioms (M : ProjectiveModel A)
    [BraidedCategory (Cochains A)] [MonoidalClosed (Cochains A)] :
    letI := M.model
    (∀ {X Y U V : Cochains A} (f : X ⟶ Y) (g : U ⟶ V),
        cofibrations (Cochains A) f → cofibrations (Cochains A) g →
        cofibrations (Cochains A) (Arrow.mk f □ Arrow.mk g).hom) ∧
    (∀ {X Y U V : Cochains A} (f : X ⟶ Y) (g : U ⟶ V),
        cofibrations (Cochains A) f → cofibrations (Cochains A) g →
        (weakEquivalences (Cochains A) f ∨ weakEquivalences (Cochains A) g) →
        weakEquivalences (Cochains A) (Arrow.mk f □ Arrow.mk g).hom) := by
  letI := M.model
  have hC : cofibrations (Cochains A) = projectiveCofibrations A := M.cofibrations_eq
  have hW := M.weakEquivalences_eq
  rw [hC, hW]
  refine ⟨?_, ?_⟩
  · intro X Y U V f g hf hg
    rw [← iCellRetracts_eq_projectiveCofibrations A] at hf hg
    apply extendProduct (I A) (I A)
      (degreewiseSurjective A ⊓ quasiIso (ModuleCat A) (.up ℤ)) ?_ f g hf hg
    rintro _ _ _ _ _ _ ⟨n⟩ ⟨m⟩
    rw [nativeProduct_eq]
    exact generatorII n m
  · intro X Y U V f g hf hg ht
    have finish : (degreewiseSurjective A).llp (Arrow.mk f □ Arrow.mk g).hom →
        quasiIso (ModuleCat A) (.up ℤ) (Arrow.mk f □ Arrow.mk g).hom := by
      rw [projectiveTrivialCofibrations_eq_llp]
      exact fun h ↦ h.2
    apply finish
    rcases ht with hw | hw
    · have hf' := (jCellRetracts_eq_projectiveTrivialCofibrations A).symm ▸
        (show (projectiveCofibrations A ⊓ quasiIso (ModuleCat A) (.up ℤ)) f from ⟨hf, hw⟩)
      rw [← iCellRetracts_eq_projectiveCofibrations A] at hg
      apply extendProduct (J A) (I A) (degreewiseSurjective A) ?_ f g hf' hg
      rintro _ _ _ _ _ _ ⟨m⟩ ⟨n⟩
      rw [nativeProduct_eq]
      exact generatorJI n m
    · have hg' := (jCellRetracts_eq_projectiveTrivialCofibrations A).symm ▸
        (show (projectiveCofibrations A ⊓ quasiIso (ModuleCat A) (.up ℤ)) g from ⟨hg, hw⟩)
      rw [← iCellRetracts_eq_projectiveCofibrations A] at hf
      apply extendProduct (I A) (J A) (degreewiseSurjective A) ?_ f g hf hg'
      rintro _ _ _ _ _ _ ⟨n⟩ ⟨m⟩
      rw [nativeProduct_eq]
      exact generatorIJ n m

private lemma nativeUnit (M : ProjectiveModel A) :
    letI := M.model
    IsCofibrant (𝟙_ (Cochains A)) := by
  letI := M.model
  have hC : cofibrations (Cochains A) = projectiveCofibrations A := M.cofibrations_eq
  have h0 : IsInitial (0 : Cochains A) := (isZero_zero _).isInitial
  change IsCofibrant (sphere A 0)
  rw [isCofibrant_iff_of_isInitial (0 : (0 : Cochains A) ⟶ sphere A 0) h0,
    cofibration_iff, hC, projectiveCofibrations, ← i_rlp A]
  intro X Y p hp
  rw [Model.hasLiftingProperty_iff_exists_diagonal]
  intro f g _
  let y := sphereHomEquiv 0 g
  have h : HasLiftingProperty (iGenerator A 0) p := hp _ ⟨0⟩
  obtain ⟨x, hx, hd⟩ :=
    (iGenerator_lifting_iff A p 0).1 h 0 y.val ((X.d _ _).hom.map_zero)
      ((p.f _).hom.map_zero.trans y.property.symm)
  let l := (sphereHomEquiv (X := X) 0).symm ⟨x, hd⟩
  refine ⟨l, h0.hom_ext _ _, ?_⟩
  apply (sphereHomEquiv 0).injective
  apply Subtype.ext
  rw [sphereHomEquiv_comp]
  simpa only [l, Equiv.apply_symm_apply] using hx

private lemma nativeTensorAxioms (M : ProjectiveModel A)
    [SymmetricCategory (Cochains A)] [MonoidalClosed (Cochains A)] :
    letI := M.model
    TensorModelAxioms (Cochains A) := by
  letI := M.model
  obtain ⟨hc, ht⟩ := nativeProductAxioms M
  exact ⟨hc, ht, nativeUnit M, unitComparison ht (nativeUnit M)⟩

/-- The native projective model uses the signed closed symmetric tensor. -/
theorem nativeTensorModel_conditional
    (_adequate : adequateModelType.{u,u}) (_adjunction : closedAdjunctionType.{u,u})
    (_currying : curryingType.{u,u}) (_comparison : ringComparisonType.{u,u}) :
    nativeTensorModelType.{u} := by
  intro A _ M
  obtain ⟨s, hs⟩ := DerivedFormalization.cochainTensor_isSymmetric A
  letI := s
  let adj (Y : Cochains A) : tensorRight Y ⊣ homFromValue Y :=
    DerivedFormalization.cochainTensorHomAdjunction Y
  letI := nativeClosedValue adj
  refine ⟨s, hs, adj, nativeClosedValue adj, rfl, ?_, nativeTensorAxioms M⟩
  intro X Y Z f i j x y
  change (((DerivedFormalization.cochainTensorHomAdjunction Y).homEquiv X Z f).f i x).v
    j (i + j) (add_comm j i) y = _
  rw [DerivedFormalization.cochainTensorHomAdjunction_homEquiv]
  exact DerivedFormalization.tensorHomEquiv_apply X Y Z f i j x y

end Native

section Transport

variable {C D : Type*} [Category* C] [Category* D]

/-- Conjugating the chosen functorial factorization by an equivalence gives
functorial factorizations for the inverse-image classes. -/
private lemma transportFactorization (F : C ⥤ D) [F.IsEquivalence]
    (P Q : MorphismProperty D) [P.RespectsIso] [Q.RespectsIso]
    [HasFunctorialFactorization P Q] :
    HasFunctorialFactorization (P.inverseImage F) (Q.inverseImage F) := by
  let d := functorialFactorizationData P Q
  let E := F.asEquivalence
  let Z : Arrow C ⥤ C := F.mapArrow ⋙ d.Z ⋙ E.inverse
  let i : Arrow.leftFunc ⟶ Z :=
    { app f := F.preimage (d.i.app (F.mapArrow.obj f) ≫ E.counitIso.inv.app _)
      naturality f g s := by
        apply F.map_injective
        simp only [Functor.map_comp, Functor.map_preimage, Arrow.leftFunc_map,
          Category.assoc]
        exact (d.i.naturality_assoc (F.mapArrow.map s) _).trans
          (congrArg (d.i.app (F.mapArrow.obj f) ≫ ·)
            (E.counitIso.inv.naturality (d.Z.map (F.mapArrow.map s)))) }
  let p : Z ⟶ Arrow.rightFunc :=
    { app f := F.preimage (E.counitIso.hom.app _ ≫ d.p.app (F.mapArrow.obj f))
      naturality f g s := by
        apply F.map_injective
        simp only [Functor.map_comp, Functor.map_preimage, Arrow.rightFunc_map,
          Category.assoc]
        exact (E.counitIso.hom.naturality_assoc (d.Z.map (F.mapArrow.map s)) _).trans
          (congrArg (E.counitIso.hom.app (d.Z.obj (F.mapArrow.obj f)) ≫ ·)
            (d.p.naturality (F.mapArrow.map s))) }
  refine ⟨⟨{ Z := Z, i := i, p := p, fac := ?_, hi := ?_, hp := ?_ }⟩⟩
  · apply NatTrans.ext
    funext f
    apply F.map_injective
    change F.map (i.app f ≫ p.app f) = F.map f.hom
    simp [i, p, d.fac_app]
  · intro f
    change P (F.map (i.app f))
    refine (P.arrow_mk_iso_iff (Arrow.isoMk' _ _ (Iso.refl _)
      (E.counitIso.app (d.Z.obj (F.mapArrow.obj f))).symm ?_)).1 (d.hi (F.mapArrow.obj f))
    simp [i]
  · intro f
    change Q (F.map (p.app f))
    refine (Q.arrow_mk_iso_iff (Arrow.isoMk' _ _
      (E.counitIso.app (d.Z.obj (F.mapArrow.obj f))).symm (Iso.refl _) ?_)).1
      (d.hp (F.mapArrow.obj f))
    simp [p]

variable [MonoidalCategory C] [MonoidalCategory D] [HasPushouts C] [HasPushouts D]

private def mapProduct (F : C ⥤ D) [F.Monoidal] [PreservesColimitsOfShape WalkingSpan F]
    {X Y U V : C} (f : X ⟶ Y) (g : U ⟶ V) :
    (Arrow.mk (F.map f) □ Arrow.mk (F.map g)) ≅ Arrow.mk (F.map (Arrow.mk f □ Arrow.mk g).hom) := by
  let μ := Functor.Monoidal.μIso F
  let h := F.map_isPushout (IsPushout.of_hasPushout (f ▷ U) (X ◁ g))
  have h' : IsPushout (F.map f ▷ F.obj U) (F.obj X ◁ F.map g)
      ((μ Y U).hom ≫ F.map (pushout.inl (f ▷ U) (X ◁ g)))
      ((μ X V).hom ≫ F.map (pushout.inr (f ▷ U) (X ◁ g))) := by
    refine h.of_iso' (μ X U) (μ Y U) (μ X V) (Iso.refl _) ?_ ?_ ?_ ?_
    · exact (Functor.LaxMonoidal.μ_natural_left F f U).symm
    · exact (Functor.LaxMonoidal.μ_natural_right F X g).symm
    · simp
    · simp
  refine Arrow.isoMk h'.isoPushout.symm (μ Y V) ?_
  change h'.isoPushout.inv ≫ F.map (Arrow.mk f □ Arrow.mk g).hom =
    (Arrow.mk (F.map f) □ Arrow.mk (F.map g)).hom ≫ (μ Y V).hom
  refine pushout.hom_ext (f := F.map f ▷ F.obj U) (g := F.obj X ◁ F.map g) ?_ ?_
  · rw [IsPushout.inl_isoPushout_inv_assoc, Category.assoc, ← F.map_comp, productInl,
      ← Category.assoc, productInl]
    exact (Functor.LaxMonoidal.μ_natural_right F Y g).symm
  · rw [IsPushout.inr_isoPushout_inv_assoc, Category.assoc, ← F.map_comp, productInr,
      ← Category.assoc, productInr]
    exact (Functor.LaxMonoidal.μ_natural_left F f V).symm

end Transport

section Represented

attribute [local instance] cochainMonoidalValue

variable {R : Type u} {A : Type a} [CommRing R] [CommRing A]

@[instance_reducible] private def transportedModel (e : R ≃+* A) (M : ProjectiveModel A) :
    FunctorialModelCategory (compValue.{a} R) := by
  letI := M.model
  let C := compValue.{a} R
  let D := Cochains A
  let E := complexEquivalenceValue e
  let F := E.functor
  letI : CategoryWithCofibrations C := ⟨(cofibrations D).inverseImage F⟩
  letI : CategoryWithFibrations C := ⟨(fibrations D).inverseImage F⟩
  letI : CategoryWithWeakEquivalences C := ⟨(weakEquivalences D).inverseImage F⟩
  letI mod : ModelCategory C := ModelCategory.transport E rfl rfl rfl
  exact
    { toModelCategory := mod
      hasLimits := ⟨fun _ _ ↦ Adjunction.hasLimitsOfShape_of_equivalence F⟩
      hasColimits := ⟨fun _ _ ↦ Adjunction.hasColimitsOfShape_of_equivalence F⟩
      cofibrationFactorization := transportFactorization F (cofibrations D) (trivialFibrations D)
      fibrationFactorization := transportFactorization F (trivialCofibrations D) (fibrations D) }

private lemma transportTensorAxioms {C D : Type*} [Category* C] [Category* D]
    [ModelCategory C] [ModelCategory D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [MonoidalClosed C]
    (F : C ⥤ D) [F.IsEquivalence] [F.Monoidal]
    (hC : cofibrations C = (cofibrations D).inverseImage F)
    (hW : weakEquivalences C = (weakEquivalences D).inverseImage F)
    (h : TensorModelAxioms D) : TensorModelAxioms C := by
  have hc {X Y U V : C} (f : X ⟶ Y) (g : U ⟶ V)
      (hf : cofibrations C f) (hg : cofibrations C g) : cofibrations C (Arrow.mk f □ Arrow.mk g).hom := by
    rw [hC] at hf hg ⊢
    exact ((cofibrations D).arrow_mk_iso_iff (mapProduct F f g)).1
      (h.pushoutProduct_cofibration _ _ hf hg)
  have ht {X Y U V : C} (f : X ⟶ Y) (g : U ⟶ V)
      (hf : cofibrations C f) (hg : cofibrations C g)
      (hw : weakEquivalences C f ∨ weakEquivalences C g) :
      weakEquivalences C (Arrow.mk f □ Arrow.mk g).hom := by
    rw [hC] at hf hg
    rw [hW] at hw ⊢
    exact ((weakEquivalences D).arrow_mk_iso_iff (mapProduct F f g)).1
      (h.pushoutProduct_trivial _ _ hf hg hw)
  have hu : IsCofibrant (𝟙_ C) := by
    rw [isCofibrant_iff, hC]
    have hI : IsInitial (F.obj (⊥_ C)) := initialIsInitial.isInitialObj F _
    exact ((cofibrations D).arrow_mk_iso_iff
      (Arrow.isoMk' (initial.to (𝟙_ D)) (F.map (initial.to (𝟙_ C)))
        (initialIsInitial.uniqueUpToIso hI) (Functor.Monoidal.εIso F)
        (initialIsInitial.hom_ext _ _))).1 ((cofibration_iff _).mp h.unit_cofibrant)
  exact ⟨hc, ht, hu, unitComparison ht hu⟩

/-- Transport the native projective model to complexes over the original ring
and identify its three classes on that category. -/
theorem representedTensorModel_conditional
    (adequate : adequateModelType.{u,a}) (_adjunction : closedAdjunctionType.{u,a})
    (_currying : curryingType.{u,a}) (_comparison : ringComparisonType.{u,a}) :
    representedTensorModelType.{u,a} := by
  intro R A _ _ e M
  letI := M.model
  obtain ⟨S⟩ := adequate e
  letI : FunctorialModelCategory (compValue.{a} R) := transportedModel e M
  letI := S.chainMonoidal
  letI := S.chainSymmetric
  letI := S.chainClosed
  letI := S.nativeSymmetric
  letI := S.chainTransport
  letI : MonoidalClosed (Cochains A) :=
    nativeClosedValue (fun Y ↦ DerivedFormalization.cochainTensorHomAdjunction Y)
  let C := compValue.{a} R
  let D := Cochains A
  let F := complexFunctorValue e
  have hC : cofibrations C = (cofibrations D).inverseImage F := rfl
  have hF : fibrations C = (fibrations D).inverseImage F := rfl
  have hW : weakEquivalences C = (weakEquivalences D).inverseImage F := rfl
  refine ⟨S, transportedModel e M, ?_, ?_, (Model.liftingClasses C).1.symm, hC, hF, hW, ?_⟩
  · rw [hF, show fibrations D = degreewiseSurjectiveValue A from M.fibrations_eq]
    ext X Y f
    simpa only [MorphismProperty.inverseImage_iff, degreewiseSurjectiveValue] using
      forall_congr' (DerivedFormalization.CochainRingTransport.complexProperties e X Y f).2.2.2
  · rw [hW, show weakEquivalences D = quasiIso (ModuleCat A) (.up ℤ) from M.weakEquivalences_eq]
    ext X Y f
    simpa only [MorphismProperty.inverseImage_iff, mem_quasiIso_iff] using
      (DerivedFormalization.CochainRingTransport.complexProperties e X Y f).2.1
  · letI : F.IsEquivalence := (complexEquivalenceValue e).isEquivalence_functor
    letI : F.Braided := S.chainTransport
    exact transportTensorAxioms F hC hW (nativeTensorAxioms M)

end Represented

end

end DerivedFormalization.Model.Complexes

universe v8_closure_7437fa030dda4138_u0 v8_closure_7437fa030dda4138_u1
theorem _root_.«DerivedFormalization».«Model».«Complexes».«nativeTensorModel» : _root_.«DerivedFormalization».«Specs».«ComplexMonoidal».«nativeTensorModelType».{v8_closure_7437fa030dda4138_u0} :=
  @_root_.«DerivedFormalization».«Model».«Complexes».«nativeTensorModel_conditional».{v8_closure_7437fa030dda4138_u0} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_7437fa030dda4138_u0, v8_closure_7437fa030dda4138_u0}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_7437fa030dda4138_u0, v8_closure_7437fa030dda4138_u0}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_7437fa030dda4138_u0, v8_closure_7437fa030dda4138_u0}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_7437fa030dda4138_u0, v8_closure_7437fa030dda4138_u0})
theorem _root_.«DerivedFormalization».«Model».«Complexes».«representedTensorModel» : _root_.«DerivedFormalization».«Specs».«ComplexMonoidal».«representedTensorModelType».{v8_closure_7437fa030dda4138_u0, v8_closure_7437fa030dda4138_u1} :=
  @_root_.«DerivedFormalization».«Model».«Complexes».«representedTensorModel_conditional».{v8_closure_7437fa030dda4138_u0, v8_closure_7437fa030dda4138_u1} (@_root_.«DerivedFormalization».«CochainTensorTransport».«adequateModel».{v8_closure_7437fa030dda4138_u0, v8_closure_7437fa030dda4138_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«closedAdjunction».{v8_closure_7437fa030dda4138_u0, v8_closure_7437fa030dda4138_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«currying».{v8_closure_7437fa030dda4138_u0, v8_closure_7437fa030dda4138_u1}) (@_root_.«DerivedFormalization».«CochainTensorTransport».«ringComparison».{v8_closure_7437fa030dda4138_u0, v8_closure_7437fa030dda4138_u1})
