import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CoinductionComplex
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainRingTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.KInjectiveReplacement
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.KInjectiveReplacementTransport
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedCoinduction
import Mathlib.CategoryTheory.Adjunction.Unique
import Batteries.Tactic.OpenPrivate

/-! Derived coinduction along maps of commutative rings. -/

namespace DerivedFormalization

open CategoryTheory
open Specs.DerivedFormalization.DerivedCoinduction
  (comparison compositionType existenceType restrictionComposition)

attribute [local instance] HasDerivedCategory.standard

noncomputable section

universe v u w t

section Localization

variable {R : Type u} [CommRing R]

/-- On morphisms to a K-injective target, localization induces a bijection
from homotopy classes. -/
private def localizedHomEquiv (X I : Comp.{v} R) [IsKInjective I] :
    ((homotopyQuotient R).obj X ⟶ (homotopyQuotient R).obj I) ≃
      ((Q R).obj X ⟶ (Q R).obj I) :=
  (Equiv.ofBijective (Qh R).map (CochainComplex.IsKInjective.Qh_map_bijective _ I)).trans
    (Iso.homCongr ((homotopyQuotientCompQhIso R).app X)
      ((homotopyQuotientCompQhIso R).app I))

private lemma localizedHomEquiv_map {X I : Comp.{v} R} [IsKInjective I] (p : X ⟶ I) :
    localizedHomEquiv X I ((homotopyQuotient R).map p) = (Q R).map p := by
  change (DerivedCategory.quotientCompQhIso (ModuleCat R)).inv.app X ≫
    (Qh R).map ((homotopyQuotient R).map p) ≫
      (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.app I = _
  rw [DerivedCategory.quotientCompQhIso_hom_naturality]
  simp

end Localization

section Adjunction

variable {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)

/-- The module adjunction prolongs degreewise to an adjunction on complexes. -/
private def cochainCoinductionAdjunction :
    restrictScalarsComplex.{max v w} f ⊣ Coinduction.coinduce.{v} f := by
  let a := ModuleCat.restrictCoextendScalarsAdj.{v} f
  letI := a.right_adjoint_additive
  refine Adjunction.mkOfUnitCounit
    { unit := NatTrans.mapHomologicalComplex a.unit (.up ℤ)
      counit := NatTrans.mapHomologicalComplex a.counit (.up ℤ)
      left_triangle := ?_
      right_triangle := ?_ }
  · ext M : 2
    apply HomologicalComplex.hom_ext
    intro n
    change ((ModuleCat.restrictScalars.{max v w} f).map (a.unit.app (M.X n)) ≫ 𝟙 _) ≫ a.counit.app _ = 𝟙 _
    rw [Category.comp_id]
    exact a.left_triangle_components (M.X n)
  · ext I : 2
    apply HomologicalComplex.hom_ext
    intro n
    change (a.unit.app _ ≫ 𝟙 _) ≫ (ModuleCat.coextendScalars f).map (a.counit.app (I.X n)) = 𝟙 _
    rw [Category.comp_id]
    exact a.right_triangle_components (I.X n)

/-- Transposing a homotopy class is well defined because the degreewise functors
are additive and hence act on the homotopy category. -/
private def homotopyCoinductionEquiv (M : Comp.{max v w} B) (I : Comp.{max v w} A) :
    ((homotopyQuotient B).obj M ⟶ (homotopyQuotient B).obj
        ((Coinduction.coinduce.{v} f).obj I)) ≃
      ((homotopyQuotient A).obj ((restrictScalarsComplex f).obj M) ⟶
        (homotopyQuotient A).obj I) := by
  let a := ModuleCat.restrictCoextendScalarsAdj.{v} f
  letI := a.right_adjoint_additive
  let F := (restrictScalars.{max v w} f).mapHomotopyCategory (.up ℤ)
  let G := (ModuleCat.coextendScalars.{u, w, max v w} f).mapHomotopyCategory (.up ℤ)
  let adj := cochainCoinductionAdjunction.{v} f
  refine
    { toFun := fun p => F.map p ≫ (homotopyQuotient A).map (adj.counit.app I)
      invFun := fun p => (homotopyQuotient B).map (adj.unit.app M) ≫ G.map p
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    obtain ⟨p, rfl⟩ := (homotopyQuotient B).map_surjective p
    change
      (homotopyQuotient B).map (adj.unit.app M) ≫
        G.map ((homotopyQuotient A).map ((restrictScalarsComplex f).map p) ≫
          (homotopyQuotient A).map (adj.counit.app I)) = (homotopyQuotient B).map p
    rw [← Functor.map_comp]
    change (homotopyQuotient B).map (adj.unit.app M) ≫
      (homotopyQuotient B).map ((Coinduction.coinduce.{v} f).map
        ((restrictScalarsComplex f).map p ≫ adj.counit.app I)) = _
    rw [← Functor.map_comp]
    exact congrArg ((homotopyQuotient B).map) ((adj.homEquiv M I).right_inv p)
  · intro p
    obtain ⟨p, rfl⟩ := (homotopyQuotient A).map_surjective p
    change F.map ((homotopyQuotient B).map (adj.unit.app M) ≫
      (homotopyQuotient B).map ((Coinduction.coinduce.{v} f).map p)) ≫
        (homotopyQuotient A).map (adj.counit.app I) = (homotopyQuotient A).map p
    rw [← Functor.map_comp]
    change (homotopyQuotient A).map ((restrictScalarsComplex f).map
        (adj.unit.app M ≫ (Coinduction.coinduce.{v} f).map p)) ≫
      (homotopyQuotient A).map (adj.counit.app I) = _
    rw [← Functor.map_comp]
    exact congrArg ((homotopyQuotient A).map) ((adj.homEquiv M I).left_inv p)

private lemma homotopyCoinductionEquiv_map {M : Comp.{max v w} B} {I : Comp.{max v w} A}
    (p : M ⟶ (Coinduction.coinduce.{v} f).obj I) :
    homotopyCoinductionEquiv.{v} f M I ((homotopyQuotient B).map p) =
      (homotopyQuotient A).map ((restrictScalarsComplex f).map p ≫
        Coinduction.evaluation.{v} f I) := by
  change (homotopyQuotient A).map ((restrictScalarsComplex f).map p) ≫
    (homotopyQuotient A).map (Coinduction.evaluation.{v} f I) = _
  rw [Functor.map_comp]

private theorem modelEvaluation_bijective_on_complex
    (M : Comp.{max v w} B) (I : Comp.{max v w} A) (hI : IsKInjective I) :
    Function.Bijective (fun p : (Q B).obj M ⟶ (Q B).obj ((Coinduction.coinduce.{v} f).obj I) =>
      (derivedRestrictScalars f).map p ≫
        Specs.DerivedFormalization.DerivedCoinduction.evaluation.{v} f I) := by
  let : IsKInjective I := hI
  let := Coinduction.isKInjective_coinduce.{v} f I hI
  let source := localizedHomEquiv M ((Coinduction.coinduce.{v} f).obj I)
  let target := localizedHomEquiv ((restrictScalarsComplex f).obj M) I
  let restrictIso := (derivedRestrictScalarsFactors.{max v w} f).app M
  let e := source.symm.trans ((homotopyCoinductionEquiv.{v} f M I).trans
    (target.trans (Iso.homCongr restrictIso.symm (Iso.refl ((Q A).obj I)))))
  have he (p : (Q B).obj M ⟶ (Q B).obj ((Coinduction.coinduce.{v} f).obj I)) :
      e p = (derivedRestrictScalars f).map p ≫
        Specs.DerivedFormalization.DerivedCoinduction.evaluation.{v} f I := by
    obtain ⟨q, rfl⟩ := source.surjective p
    obtain ⟨q, rfl⟩ := (homotopyQuotient B).map_surjective q
    simp only [e, Equiv.trans_apply, Equiv.symm_apply_apply, homotopyCoinductionEquiv_map,
      target, localizedHomEquiv_map, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
    change (derivedRestrictScalarsFactors f).hom.app M ≫
        (Q A).map ((restrictScalarsComplex f).map q ≫ Coinduction.evaluation.{v} f I) =
      (derivedRestrictScalars f).map ((Q B).map q) ≫
        (derivedRestrictScalarsFactors f).hom.app ((Coinduction.coinduce.{v} f).obj I) ≫
        (Q A).map (Coinduction.evaluation.{v} f I)
    rw [derivedRestrictScalarsFactors_naturality_assoc, Functor.map_comp]
  exact (funext he) ▸ e.bijective

private theorem modelEvaluation_bijective
    (X : D.{max v w} B) (I : Comp.{max v w} A) (hI : IsKInjective I) :
    Function.Bijective (fun p : X ⟶ (Q B).obj ((Coinduction.coinduce.{v} f).obj I) =>
      (derivedRestrictScalars f).map p ≫
        Specs.DerivedFormalization.DerivedCoinduction.evaluation.{v} f I) := by
  let M := (Q B).objPreimage X
  let e : (Q B).obj M ≅ X := (Q B).objObjPreimageIso X
  let left := Iso.homCongr e.symm (Iso.refl ((Q B).obj ((Coinduction.coinduce.{v} f).obj I)))
  let right := Iso.homCongr ((derivedRestrictScalars f).mapIso e) (Iso.refl ((Q A).obj I))
  let eval := Specs.DerivedFormalization.DerivedCoinduction.evaluation.{v} f I
  have h := right.bijective.comp ((modelEvaluation_bijective_on_complex.{v} f M I hI).comp
    left.bijective)
  convert h using 1
  funext p
  change (derivedRestrictScalars f).map p ≫ eval =
    (derivedRestrictScalars f).map e.inv ≫
      ((derivedRestrictScalars f).map (e.hom ≫ p ≫ 𝟙 _) ≫ eval) ≫ 𝟙 _
  simp only [Category.comp_id]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]

end Adjunction

private theorem exists_kInjectiveModel {R : Type u} [CommRing R] (Y : D.{max u v} R) :
    ∃ I : Comp.{max u v} R, IsKInjective I ∧ Nonempty (Y ≅ (Q R).obj I) := by
  obtain ⟨I, p, _, hp, hI, _⟩ := kInjectiveReplacement.{u, v} ((Q R).objPreimage Y)
  have : QuasiIso p := hp
  exact ⟨I, hI, ⟨((Q R).objObjPreimageIso Y).symm ≪≫ asIso ((Q R).map p)⟩⟩

/-- Derived restriction admits a right adjoint computed by coinduction on
every K-injective replacement. -/
theorem derivedCoinductionExists : existenceType.{v, u, w} := by
  intro A B _ _ f
  let L := derivedRestrictScalars.{max v u w} f
  choose I hI i using fun Y : D.{max v u w} A => exists_kInjectiveModel.{max v w, u} Y
  let Gobj (Y : D.{max v u w} A) : D.{max v u w} B :=
    (Q B).obj ((Coinduction.coinduce.{max v u} f).obj (I Y))
  let counit (Y : D.{max v u w} A) : L.obj (Gobj Y) ⟶ Y :=
    Specs.DerivedFormalization.DerivedCoinduction.evaluation.{max v u} f (I Y) ≫ (i Y).some.inv
  let e (X : D.{max v u w} B) (Y : D.{max v u w} A) :
      (X ⟶ Gobj Y) ≃ (L.obj X ⟶ Y) :=
    (Equiv.ofBijective _ (modelEvaluation_bijective.{max v u} f X (I Y) (hI Y))).trans
      (Iso.homCongr (Iso.refl (L.obj X)) (i Y).some.symm)
  have he (X : D.{max v u w} B) (Y : D.{max v u w} A) (p : X ⟶ Gobj Y) :
      e X Y p = L.map p ≫ counit Y := by
    simp only [e, Equiv.trans_apply, Equiv.ofBijective_apply, Iso.homCongr_apply,
      Iso.refl_inv, Iso.symm_hom, Category.id_comp, Category.assoc, counit, L]
  have hnat (X' X : D.{max v u w} B) (Y : D.{max v u w} A) (p : X' ⟶ X)
      (q : L.obj X ⟶ Y) : (e X' Y).symm (L.map p ≫ q) = p ≫ (e X Y).symm q := by
    apply (e X' Y).injective
    rw [Equiv.apply_symm_apply, he, L.map_comp, Category.assoc, ← he, Equiv.apply_symm_apply]
  let G := Adjunction.rightAdjointOfEquiv (fun X Y => (e X Y).symm) hnat
  let adj : L ⊣ G := Adjunction.adjunctionOfEquivRight (fun X Y => (e X Y).symm) hnat
  refine ⟨⟨G, adj, fun J hJ => ?_⟩⟩
  apply isIso_of_yoneda_map_bijective
  intro X
  have h := (adj.homEquiv X ((Q A).obj J)).bijective.comp
    (modelEvaluation_bijective.{max v u} f X J hJ)
  convert h using 1
  funext p
  exact (adj.homEquiv_naturality_left p
    (Specs.DerivedFormalization.DerivedCoinduction.evaluation.{max v u} f J)).symm

theorem derivedCoinductionComposition : compositionType.{v, u, w, t} := by
  intro A B C _ _ _ f g F G H
  let composite := (G.adjunction.comp F.adjunction).ofNatIsoLeft
    (restrictionComposition.{v} f g).symm
  refine ⟨composite.rightAdjointUniq H.adjunction, fun Y => ?_⟩
  rw [Adjunction.rightAdjointUniq_hom_app_counit]
  change composite.counit.app Y = _
  simp only [composite, Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Iso.symm_inv, Adjunction.comp_counit_app]

section CoefficientLift

open Specs.DerivedFormalization.CochainCoefficientLift
  (lift liftD liftDFactors fromOriginal fromOriginalCohomology)

variable {A : Type u} {B : Type w} [CommRing A] [CommRing B] (f : A →+* B)

/-- An original complex in an independent universe computes coinduction after the
same-ring lift. The inverse of the localized augmentation gives the trace on the
image of the original object. -/
theorem derivedCoinductionLiftedModel
    (G : Specs.DerivedFormalization.DerivedCoinduction.Coinduction.{max u v t} f)
    (Y : Comp.{v} A) :
    let Y' := (liftD.{max u w t, v} A).obj ((Q A).obj Y)
    ∃ (I : Comp.{max u v w t} A) (p : (lift.{max u w t, v} A).obj Y ⟶ I)
      (_ : QuasiIso p) (hI : IsKInjective I),
      (∀ n : ℤ, Mono (p.f n)) ∧
      (∀ n : ℤ, Injective (I.X n)) ∧
      (∀ n : ℤ, Function.Injective ((fromOriginal.{max u w t} p).f n)) ∧
      (∀ n : ℤ, Function.Bijective (fromOriginalCohomology.{max u w t} p n)) ∧
      let i : Y' ≅ (Q A).obj I :=
        (liftDFactors.{max u w t, v} A).app Y ≪≫ asIso ((Q A).map p)
      (derivedRestrictScalars f).map (G.modelIso f I i hI).inv ≫ G.adjunction.counit.app Y' =
        Specs.DerivedFormalization.DerivedCoinduction.evaluation.{max u v t} f I ≫ i.inv := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, J, _, _, _, p, _, hmono, hp, hI, hterms, hinj, hcoh, _⟩ :=
    KInjectiveReplacementTransport.replacementTransport.{v, u, max w t}.1 Y
  let : QuasiIso p := hp
  exact ⟨CategoryTheory.Limits.limit J, p, hp, hI, hmono, hterms, hinj, hcoh,
    G.modelCounit f _ _ hI⟩

end CoefficientLift

section RingTransport

open Specs.DerivedFormalization.CochainRingTransport
  (moduleEquivalenceValue complexEquivalenceValue complexFunctorValue derivedFunctorValue
    derivedFactorsValue conjugateValue complexRestrictionIsoValue derivedRestrictionIsoValue
    coextensionMateValue adjunctionCompatible)
open Specs.DerivedFormalization.DerivedCoinduction renaming Coinduction → DerivedCoinduction
open private forwardMateIsIso from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainRingTransport

variable {R : Type u} {S : Type w} {A B : Type (max v w)}
  [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  (e : R ≃+* A) (d : S ≃+* B) (f : R →+* S)

private theorem transport_kInjective {A₀ : Type t} [CommRing A₀] (e : R ≃+* A₀)
    {I : Comp.{t} R} (hI : IsKInjective I) :
    IsKInjective ((complexFunctorValue e).obj I) := by
  let E := complexEquivalenceValue e
  let F := E.functor
  let m := (moduleEquivalenceValue e).functor
  let : IsKInjective I := hI
  refine ⟨fun {X} p hX => ?_⟩
  let q := F.preimage (E.counitIso.hom.app X ≫ p)
  have hX' : (E.inverse.obj X).Acyclic :=
    (CochainRingTransport.complexProperties (e := e) _ _ (𝟙 (E.inverse.obj X))).1.mp
      (fun n => (hX n).of_iso (E.counitIso.app X).symm)
  have h := m.mapHomotopy (CochainComplex.IsKInjective.homotopyZero q hX')
  have hq : F.map q = E.counitIso.hom.app X ≫ p := F.map_preimage _
  refine ⟨(Homotopy.ofEq ?_).trans ((h.compLeft (E.counitIso.inv.app X)).trans (.ofEq ?_))⟩
  · change p = E.counitIso.inv.app X ≫ F.map q
    rw [hq, Iso.inv_hom_id_app_assoc]
  · change E.counitIso.inv.app X ≫ F.map 0 = 0
    rw [Functor.map_zero, Limits.comp_zero]

private theorem comparison_counit {G : D.{max v w} R ⥤ D.{max v w} S}
    (adj : derivedRestrictScalars f ⊣ G) (I : Comp.{max v w} R) :
    (derivedRestrictScalars f).map (comparison.{v} f adj I) ≫ adj.counit.app ((Q R).obj I) =
      Specs.DerivedFormalization.DerivedCoinduction.evaluation.{v} f I := by
  exact (adj.homEquiv_counit (g := comparison.{v} f adj I)).symm.trans
    ((adj.homEquiv _ _).symm_apply_apply _)

local notation "fₐ" => conjugateValue e d f
local notation "F" => complexFunctorValue e
local notation "H" => complexFunctorValue d
local notation "E" => derivedFunctorValue e
local notation "T" => derivedFunctorValue d
local notation "δ" => derivedRestrictionIsoValue e d f

private theorem transport_evaluation
    (α : ModuleCat.coextendScalars f ⋙ (moduleEquivalenceValue d).functor ≅
      (moduleEquivalenceValue e).functor ⋙ ModuleCat.coextendScalars fₐ)
    (hα : α.hom = coextensionMateValue.{v} e d f) (I : Comp.{max v w} R) :
    let J := (Coinduction.coinduce.{v} f).obj I
    let a := NatIso.mapHomologicalComplex α (.up ℤ)
    (derivedRestrictScalars.{max v w} fₐ).map ((derivedFactorsValue d).hom.app J ≫ (Q B).map (a.hom.app I)) ≫
        Specs.DerivedFormalization.DerivedCoinduction.evaluation.{max v w} fₐ ((F).obj I) =
      (δ).inv.app ((Q S).obj J) ≫
        (E).map (Specs.DerivedFormalization.DerivedCoinduction.evaluation.{v} f I) ≫
        (derivedFactorsValue e).hom.app I := by
  let J := (Coinduction.coinduce.{v} f).obj I
  let a : Coinduction.coinduce.{v} f ⋙ H ≅ F ⋙ Coinduction.coinduce.{max v w} fₐ :=
    NatIso.mapHomologicalComplex α (.up ℤ)
  let r := derivedRestrictScalarsFactors.{max v w} f
  let r' := derivedRestrictScalarsFactors.{max v w} fₐ
  let b := complexRestrictionIsoValue e d f
  let q := Q.{max v w} A
  have hc : (restrictScalarsComplex fₐ).map (a.hom.app I) ≫
      Coinduction.evaluation.{max v w} fₐ ((F).obj I) =
    b.inv.app J ≫ (F).map (Coinduction.evaluation.{v} f I) := by
    apply HomologicalComplex.hom_ext
    intro n
    change (ModuleCat.restrictScalars fₐ).map (α.hom.app (I.X n)) ≫
        (ModuleCat.restrictCoextendScalarsAdj fₐ).counit.app (((F).obj I).X n) = _
    rw [hα]
    exact mateEquiv_counit (ModuleCat.restrictCoextendScalarsAdj.{v} f)
      (ModuleCat.restrictCoextendScalarsAdj.{max v w} fₐ) _ (I.X n)
  have hs :
      (δ).hom.app ((Q S).obj J) ≫
        (derivedRestrictScalars.{max v w} fₐ).map ((derivedFactorsValue d).hom.app J) ≫
        r'.hom.app ((H).obj J) =
      (E).map (r.hom.app J) ≫
        (derivedFactorsValue e).hom.app ((restrictScalarsComplex f).obj J) ≫
        q.map (b.hom.app J) :=
    (CochainRingTransport.derivedRestrictionComponents (e := e) (d := d) (f := f)) J
  have hs' :
      (derivedRestrictScalars.{max v w} fₐ).map ((derivedFactorsValue d).hom.app J) ≫
        r'.hom.app ((H).obj J) ≫ q.map (b.inv.app J) =
      (δ).inv.app ((Q S).obj J) ≫ (E).map (r.hom.app J) ≫
        (derivedFactorsValue e).hom.app ((restrictScalarsComplex f).obj J) := by
    apply ((δ).app ((Q S).obj J)).eq_inv_comp.mpr
    change (δ).hom.app ((Q S).obj J) ≫
      (derivedRestrictScalars.{max v w} fₐ).map ((derivedFactorsValue d).hom.app J) ≫
      r'.hom.app ((H).obj J) ≫ q.map (b.inv.app J) = _
    rw [reassoc_of% hs]
    rw [← q.map_comp, Iso.hom_inv_id_app]
    erw [q.map_id, Category.comp_id]
  have hn := (derivedFactorsValue e).hom.naturality (Coinduction.evaluation.{v} f I)
  change (E).map ((Q R).map (Coinduction.evaluation.{v} f I)) ≫
      (derivedFactorsValue e).hom.app I =
    (derivedFactorsValue e).hom.app ((restrictScalarsComplex f).obj J) ≫
      q.map ((F).map (Coinduction.evaluation.{v} f I)) at hn
  change (derivedRestrictScalars.{max v w} fₐ).map ((derivedFactorsValue d).hom.app J ≫ (Q B).map (a.hom.app I)) ≫
      r'.hom.app _ ≫ q.map (Coinduction.evaluation.{max v w} fₐ ((F).obj I)) =
    (δ).inv.app ((Q S).obj J) ≫ (E).map (r.hom.app J ≫
      (Q R).map (Coinduction.evaluation.{v} f I)) ≫ (derivedFactorsValue e).hom.app I
  rw [Functor.map_comp, Category.assoc, derivedRestrictScalarsFactors_naturality_assoc]
  rw [← Functor.map_comp, hc, Functor.map_comp]
  rw [reassoc_of% hs', Functor.map_comp]
  simp only [Category.assoc, hn]
  rfl

/-- Change of ring representatives identifies the two derived right adjoints via
the mate of the restriction comparison. On K-injective models this is the
localization of the degreewise coextension mate. -/
theorem derivedCoinductionRingTransport (G : DerivedCoinduction.{v} f)
    (G' : DerivedCoinduction.{max v w} fₐ) :
    ∃ β : G.functor ⋙ T ≅ E ⋙ G'.functor,
      β.hom = mateEquiv G.adjunction G'.adjunction (δ).inv ∧
      adjunctionCompatible G.adjunction G'.adjunction (δ).inv β.hom ∧
      ∃ α : ModuleCat.coextendScalars f ⋙ (moduleEquivalenceValue d).functor ≅
          (moduleEquivalenceValue e).functor ⋙ ModuleCat.coextendScalars fₐ,
        α.hom = coextensionMateValue.{v} e d f ∧
        ∀ I : Comp.{max v w} R, IsKInjective I →
          IsKInjective ((F).obj I) ∧
          (T).map (comparison.{v} f G.adjunction I) ≫ β.hom.app ((Q R).obj I) =
            (derivedFactorsValue d).hom.app ((Coinduction.coinduce.{v} f).obj I) ≫
              (Q B).map ((NatIso.mapHomologicalComplex α (.up ℤ)).hom.app I) ≫
              comparison.{max v w} fₐ G'.adjunction ((F).obj I) ≫
              G'.functor.map ((derivedFactorsValue e).inv.app I) := by
  let b := mateEquiv G.adjunction G'.adjunction (δ).inv
  have hb : IsIso b :=
    forwardMateIsIso G.adjunction G'.adjunction (CochainRingTransport.derivedEquivalence d)
      (CochainRingTransport.derivedEquivalence e) (δ).symm
  obtain ⟨α, hα, _, _⟩ := (CochainRingTransport.coextensionMate.{v, u, w}) e d f
  refine ⟨asIso b, rfl, ⟨unit_mateEquiv _ _ _, mateEquiv_counit _ _ _⟩, α, hα,
    fun I hI => ⟨transport_kInjective e hI, ?_⟩⟩
  let p := comparison.{v} f G.adjunction I
  let p' := comparison.{max v w} fₐ G'.adjunction ((F).obj I)
  let i := (derivedFactorsValue e).app I
  let j := (derivedFactorsValue d).app ((Coinduction.coinduce.{v} f).obj I)
  let a : Coinduction.coinduce.{v} f ⋙ H ≅ F ⋙ Coinduction.coinduce.{max v w} fₐ :=
    NatIso.mapHomologicalComplex α (.up ℤ)
  let X := (T).obj ((Q S).obj ((Coinduction.coinduce.{v} f).obj I))
  have hδ := (δ).inv.naturality p
  change (derivedRestrictScalars.{max v w} fₐ).map ((T).map p) ≫ (δ).inv.app (G.functor.obj ((Q R).obj I)) =
    (δ).inv.app ((Q S).obj ((Coinduction.coinduce.{v} f).obj I)) ≫ (E).map ((derivedRestrictScalars.{max v w} f).map p) at hδ
  have hε := G'.adjunction.counit.naturality i.inv
  change (derivedRestrictScalars.{max v w} fₐ).map (G'.functor.map i.inv) ≫ G'.adjunction.counit.app ((E).obj ((Q R).obj I)) =
    G'.adjunction.counit.app ((Q A).obj ((F).obj I)) ≫ i.inv at hε
  have h := transport_evaluation e d f α hα I
  change (derivedRestrictScalars.{max v w} fₐ).map (j.hom ≫ (Q B).map (a.hom.app I)) ≫
    Specs.DerivedFormalization.DerivedCoinduction.evaluation.{max v w} fₐ ((F).obj I) =
      (δ).inv.app ((Q S).obj ((Coinduction.coinduce.{v} f).obj I)) ≫
        (E).map (Specs.DerivedFormalization.DerivedCoinduction.evaluation.{v} f I) ≫ i.hom at h
  apply (G'.adjunction.homEquiv X ((E).obj ((Q R).obj I))).symm.injective
  change (G'.adjunction.homEquiv _ _).symm ((T).map p ≫ b.app ((Q R).obj I)) =
    (G'.adjunction.homEquiv _ _).symm
      (j.hom ≫ (Q B).map (a.hom.app I) ≫ p' ≫ G'.functor.map i.inv)
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [mateEquiv_counit G.adjunction G'.adjunction (δ).inv,
    reassoc_of% hδ, ← (E).map_comp, comparison_counit]
  change _ = (derivedRestrictScalars.{max v w} fₐ).map j.hom ≫
    (derivedRestrictScalars.{max v w} fₐ).map ((Q B).map (a.hom.app I)) ≫
    (derivedRestrictScalars.{max v w} fₐ).map p' ≫
    (derivedRestrictScalars.{max v w} fₐ).map (G'.functor.map i.inv) ≫
      G'.adjunction.counit.app ((E).obj ((Q R).obj I))
  rw [hε]
  rw [reassoc_of% (comparison_counit fₐ G'.adjunction ((F).obj I))]
  rw [← Functor.map_comp_assoc, reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

end RingTransport

end

end DerivedFormalization
