import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomAdjunction
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainTensorTransport
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedHomModels
import Batteries.Tactic.OpenPrivate

/-! Internal derived Hom and the closed adjunction for unbounded cochains. -/

namespace DerivedFormalization.DerivedHomAdjunction

open CategoryTheory Opposite
open Specs.DerivedFormalization.DerivedHomAdjunction
open Specs.DerivedFormalization.Cochains
open Specs.DerivedFormalization.CochainTensor (isKFlat tensor)
open Specs.DerivedFormalization.CochainModels (internalHomValue internalHomMapValue
  internalHomCohomologyValue)
open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel)
open Specs.DerivedFormalization.DerivedHomModels (Models rHomValue)

universe u a v w t s

attribute [local instance] HasDerivedCategory.standard

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.checkUnivs false
set_option linter.style.haveILetI false

variable {R : Type u} [CommRing R]

theorem homOfFlatInjective : HomOfFlatInjective.{u,a} := by
  intro R _ P I hP hI
  apply (isKInjective_iff_internalHom_acyclic (internalHomValue P I)).2
  intro E hE
  obtain ⟨c⟩ := CochainTensorTransport.currying.{u,a} R
  let i := c.iso E P I
  have h := (isKInjective_iff_internalHom_acyclic I).1 hI _ (hP E hE)
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact (h n).isZero_homology.of_iso
    (((HomologicalComplex.homologyFunctor (ModuleCat.{a} R) (.up ℤ) n).mapIso i).symm)

theorem singleReplacements : SingleReplacements.{u,a} :=
  ⟨DerivedHomModels.modelMap_natural, DerivedHomModels.modelMap_isIso,
    DerivedHomModels.strictComparisons, DerivedHomModels.modelChoiceIndependence⟩

/-- Localization is a linear equivalence on maps out of a K-projective
complex or into a K-injective complex. -/
private def localizeHom (B J : compValue.{a} R)
    (h : Function.Bijective ((qhValue.{a} R).map :
      ((quotientValue R).obj B ⟶ (quotientValue R).obj J) → _)) :
    ((quotientValue R).obj B ⟶ (quotientValue R).obj J) ≃ₗ[R]
      ((qValue R).obj B ⟶ (qValue R).obj J) :=
  letI : Functor.Linear R (qhValue.{a} R) :=
    inferInstanceAs (Functor.Linear R
      (DerivedCategory.Qh : homotopyValue.{a} R ⥤ derivedValue.{a} R))
  letI : (qhValue.{a} R).Additive :=
    inferInstanceAs (DerivedCategory.Qh : homotopyValue.{a} R ⥤ derivedValue.{a} R).Additive
  (LinearEquiv.ofBijective ((qhValue.{a} R).mapLinearMap R) h).trans
    (Linear.homCongr R ((quotientCompQhIsoValue.{a} R).app B) ((quotientCompQhIsoValue.{a} R).app J))

private theorem localizeHom_apply (B J : compValue.{a} R) (h)
    (f : (quotientValue R).obj B ⟶ (quotientValue R).obj J) :
    localizeHom B J h f = (quotientCompQhIsoValue R).inv.app B ≫
      (qhValue R).map f ≫ (quotientCompQhIsoValue R).hom.app J := by
  change ((quotientCompQhIsoValue R).inv.app B ≫ (qhValue R).map f) ≫
    (quotientCompQhIsoValue R).hom.app J = _
  simp only [Category.assoc]

private theorem localizeHom_map {B J : (compValue.{a} R)} (h) (f : B ⟶ J) :
    localizeHom B J h ((quotientValue.{a} R).map f) = (qValue.{a} R).map f := by
  rw [localizeHom_apply]
  change (quotientCompQhIsoValue R).inv.app B ≫
    (quotientValue R ⋙ qhValue R).map f ≫ (quotientCompQhIsoValue R).hom.app J = _
  rw [(quotientCompQhIsoValue.{a} R).hom.naturality, Iso.inv_hom_id_app_assoc]

private theorem localizeHom_surj {B J : compValue.{a} R}
    (h : Function.Bijective ((qhValue.{a} R).map :
      ((quotientValue R).obj B ⟶ (quotientValue R).obj J) → _)) :
    Function.Surjective ((qValue.{a} R).map : (B ⟶ J) → _) := by
  intro f
  obtain ⟨g, hg⟩ := (localizeHom B J h).surjective f
  have hquot : (quotientValue R).map g.out = g := HomotopyCategory.quotient_map_out g
  exact ⟨g.out, by rw [← localizeHom_map h, hquot, hg]⟩

private theorem mapsIntoInjective (B J : (compValue.{a} R)) (hJ : J.IsKInjective) :
    Function.Bijective ((qhValue.{a} R).map : ((quotientValue.{a} R).obj B ⟶ (quotientValue.{a} R).obj J) → _) := by
  letI := hJ
  exact CochainComplex.IsKInjective.Qh_map_bijective ((quotientValue.{a} R).obj B) J

private theorem mapsFromProjective (B J : (compValue.{a} R)) (hB : B.IsKProjective) :
    Function.Bijective ((qhValue.{a} R).map : ((quotientValue.{a} R).obj B ⟶ (quotientValue.{a} R).obj J) → _) := by
  letI := hB
  exact CochainComplex.IsKProjective.Qh_map_bijective B ((quotientValue.{a} R).obj J)

open CochainComplex.HomComplex (Cochain) in
private theorem rawCurry_eq (S P I : (compValue.{a} R))
    (c : Specs.DerivedFormalization.CochainTensorTransport.ClosedAdjunction P)
    (f : tensor S P ⟶ I) :
    c.adj.homEquiv S I f = CochainTensorTransport.curryEquiv S P I f := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro j m hj
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain rfl : m = i + j := by omega
  exact (c.on_pure S I f i j z x).trans
    (CochainTensorTransport.curryEquiv_apply S P I f i j z x).symm

section Closed

variable {A : Type a} [CommRing A] {e : R ≃+* A} (M : AdequateModel e)

private def localizedCurry (S P I : (compValue.{a} R)) (hP : isKFlat P) (hI : I.IsKInjective) :
    ((qValue R).obj (tensor S P) ⟶ (qValue R).obj I) ≃
      ((qValue R).obj S ⟶ (qValue R).obj (internalHomValue P I)) :=
  let c := M.rawClosed P
  (localizeHom _ _ (mapsIntoInjective _ I hI)).symm.toEquiv.trans <|
    (Iso.homCongr (c.leftFactors.app S).symm (Iso.refl _)).trans <|
      (c.adjK.homEquiv ((quotientValue.{a} R).obj S) ((quotientValue.{a} R).obj I)).trans <|
        (Iso.homCongr (Iso.refl _) (c.rightFactors.app I)).trans <|
          (localizeHom _ _ (mapsIntoInjective S _ (homOfFlatInjective P I hP hI))).toEquiv

private theorem localizedCurry_map (S P I : (compValue.{a} R)) (hP : isKFlat P)
    (hI : I.IsKInjective) (f : tensor S P ⟶ I) :
    localizedCurry M S P I hP hI ((qValue.{a} R).map f) =
      (qValue.{a} R).map (((M.rawClosed P).adj.homEquiv S I) f) := by
  let c := M.rawClosed P
  let h := mapsIntoInjective (tensor S P) I hI
  have h1 : (localizeHom _ _ h).symm ((qValue.{a} R).map f) = (quotientValue.{a} R).map f :=
    (LinearEquiv.symm_apply_eq _).2 (localizeHom_map h f).symm
  have h2 := c.homotopy S I f
  change localizeHom S (internalHomValue P I)
    (mapsIntoInjective S _ (homOfFlatInjective P I hP hI))
    (𝟙 _ ≫ (c.adjK.homEquiv _ _
      ((c.leftFactors.app S).hom ≫ (localizeHom _ _ h).symm ((qValue R).map f) ≫ 𝟙 _)) ≫
        (c.rightFactors.app I).hom) = _
  rw [Category.comp_id, Category.id_comp, h1]
  exact (congrArg (localizeHom S (internalHomValue P I)
    (mapsIntoInjective S _ (homOfFlatInjective P I hP hI))) h2).trans (localizeHom_map _ _)

private theorem localizedCurry_signed (S P I : (compValue.{a} R)) (hP : isKFlat P)
    (hI : I.IsKInjective) (f : tensor S P ⟶ I) :
    localizedCurry M S P I hP hI ((qValue.{a} R).map f) =
      (qValue.{a} R).map (CochainTensorTransport.curryEquiv S P I f) := by
  rw [localizedCurry_map, rawCurry_eq]

private def localizedCurryLinear (S P I : (compValue.{a} R)) (hP : isKFlat P) (hI : I.IsKInjective) :
    ((qValue R).obj (tensor S P) ⟶ (qValue R).obj I) ≃ₗ[R]
      ((qValue R).obj S ⟶ (qValue R).obj (internalHomValue P I)) where
  __ := localizedCurry M S P I hP hI
  map_add' f g := by
    obtain ⟨f, rfl⟩ := localizeHom_surj (mapsIntoInjective _ I hI) f
    obtain ⟨g, rfl⟩ := localizeHom_surj (mapsIntoInjective _ I hI) g
    change localizedCurry M S P I hP hI ((qValue R).map f + (qValue R).map g) =
      localizedCurry M S P I hP hI ((qValue R).map f) +
        localizedCurry M S P I hP hI ((qValue R).map g)
    rw [← (qValue.{a} R).map_add, localizedCurry_signed, localizedCurry_signed, localizedCurry_signed,
      map_add, (qValue.{a} R).map_add]
  map_smul' r f := by
    obtain ⟨f, rfl⟩ := localizeHom_surj (mapsIntoInjective _ I hI) f
    change localizedCurry M S P I hP hI (r • (qValue.{a} R).map f) =
      r • localizedCurry M S P I hP hI ((qValue.{a} R).map f)
    rw [← (qValue.{a} R).map_smul, localizedCurry_signed, localizedCurry_signed, map_smul, (qValue.{a} R).map_smul]

private theorem localizedCurry_natural {S S' P P' I I' : (compValue.{a} R)}
    (hP : isKFlat P) (hP' : isKFlat P') (hI : I.IsKInjective) (hI' : I'.IsKInjective)
    (z : S' ⟶ S) (x : P' ⟶ P) (y : I ⟶ I') (f : (qValue.{a} R).obj (tensor S P) ⟶ (qValue.{a} R).obj I) :
    localizedCurry M S' P' I' hP' hI'
        ((qValue.{a} R).map (Specs.DerivedFormalization.CochainTensor.map z x) ≫ f ≫ (qValue.{a} R).map y) =
      (qValue.{a} R).map z ≫ localizedCurry M S P I hP hI f ≫ (qValue.{a} R).map (internalHomMapValue x y) := by
  obtain ⟨f, rfl⟩ := localizeHom_surj (mapsIntoInjective _ I hI) f
  rw [← (qValue.{a} R).map_comp, ← (qValue.{a} R).map_comp, localizedCurry_signed, localizedCurry_signed,
    CochainTensorTransport.curryEquiv_natural, (qValue.{a} R).map_comp, (qValue.{a} R).map_comp]
  rfl

variable {M} (T : Specs.DerivedFormalization.DerivedTensor.Model M) (H : Models.{u,a} R)

private theorem tensorComparison_natural
    {Z Z' X X' : derivedValue.{a} R} (S : Presentation Z) (S' : Presentation Z')
    (P : Presentation X) (P' : Presentation X') (hP : isKFlat P.complex)
    (hP' : isKFlat P'.complex)
    {z : Z' ⟶ Z} {x : X' ⟶ X} (z₀ : S'.complex ⟶ S.complex)
    (x₀ : P'.complex ⟶ P.complex) (hz : S'.Over S z z₀) (hx : P'.Over P x x₀) :
    T.toDescent.tensorFunctor.map (Prod.mkHom z x) ≫ (tensorComparison T S P hP).hom =
      (tensorComparison T S' P' hP').hom ≫
        (qValue R).map (Specs.DerivedFormalization.CochainTensor.map z₀ x₀) := by
  let F := T.toDescent.tensorFunctor
  have h : Prod.mkHom z x ≫ (S.iso.prod P.iso).inv =
      (S'.iso.prod P'.iso).inv ≫ Prod.mkHom ((qValue R).map z₀) ((qValue R).map x₀) := by
    apply (cancel_mono (S.iso.prod P.iso).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change Prod.mkHom z x =
      (S'.iso.prod P'.iso).inv ≫
        Prod.mkHom ((qValue R).map z₀ ≫ S.iso.hom) ((qValue R).map x₀ ≫ P.iso.hom)
    rw [show (qValue R).map z₀ ≫ S.iso.hom = S'.iso.hom ≫ z from hz,
      show (qValue R).map x₀ ≫ P.iso.hom = P'.iso.hom ≫ x from hx]
    change _ = (S'.iso.prod P'.iso).inv ≫ (S'.iso.prod P'.iso).hom ≫ Prod.mkHom z x
    simp
  have hn := T.compare_natural z₀ x₀ (Or.inr hP') (Or.inr hP)
  change F.map (Prod.mkHom z x) ≫ F.map (S.iso.prod P.iso).inv ≫
      (T.compare S.complex P.complex _).hom = _
  rw [← F.map_comp_assoc, h, F.map_comp_assoc, hn]
  simp only [tensorComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Category.assoc]
  rfl

private theorem homComparison_natural
    {X X' Y Y' : derivedValue.{a} R} (P : Presentation X) (P' : Presentation X')
    (I : Presentation Y) (I' : Presentation Y')
    (h : P.complex.IsKProjective ∨ I.complex.IsKInjective)
    (h' : P'.complex.IsKProjective ∨ I'.complex.IsKInjective)
    {x : X' ⟶ X} {y : Y ⟶ Y'} (x₀ : P'.complex ⟶ P.complex)
    (y₀ : I.complex ⟶ I'.complex) (hx : P'.Over P x x₀) (hy : I.Over I' y y₀) :
    (qValue R).map (internalHomMapValue x₀ y₀) ≫ homComparison H P' I' =
      homComparison H P I ≫ (rHomValue H).map (Prod.mkHom x.op y) := by
  have hOver {U V : derivedValue.{a} R} {B : Presentation U} {J : Presentation V}
      {f : U ⟶ V} {g : B.complex ⟶ J.complex} (hg : B.Over J f g) :
      (qValue R).map g = B.iso.hom ≫ f ≫ J.iso.inv := by
    apply (cancel_mono J.iso.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
      (show (qValue R).map g ≫ J.iso.hom = B.iso.hom ≫ f from hg)
  exact DerivedHomModels.modelIso_chain_natural H P.iso P'.iso I.iso I'.iso
    h h' x y x₀ y₀ (hOver hx) (hOver hy)

private def homComparisonIso {X Y : derivedValue.{a} R}
    (P : Presentation X) (I : Presentation Y)
    (h : P.complex.IsKProjective ∨ I.complex.IsKInjective) :
    (qValue R).obj (internalHomValue P.complex I.complex) ≅ (rHomValue H).obj (op X, Y) :=
  DerivedHomModels.modelIso H P.representative I.representative h

private def computeCurry {Z X Y : derivedValue.{a} R}
    (S : Presentation Z) (P : Presentation X) (I : Presentation Y)
    (hP : isKFlat P.complex) (hI : I.complex.IsKInjective) :
    (T.toDescent.tensorFunctor.obj (Z, X) ⟶ Y) ≃ₗ[R] (Z ⟶ (rHomValue H).obj (op X, Y)) :=
  (Linear.homCongr R (tensorComparison T S P hP) I.iso.symm).trans <|
    (localizedCurryLinear M S.complex P.complex I.complex hP hI).trans <|
      Linear.homCongr R S.iso (homComparisonIso H P I (Or.inr hI))

private theorem computeCurry_apply {Z X Y : derivedValue.{a} R}
    (S : Presentation Z) (P : Presentation X) (I : Presentation Y)
    (hP : isKFlat P.complex) (hI : I.complex.IsKInjective)
    (f : T.toDescent.tensorFunctor.obj (Z, X) ⟶ Y) :
    computeCurry T H S P I hP hI f = S.iso.inv ≫
      localizedCurry M S.complex P.complex I.complex hP hI
        ((tensorComparison T S P hP).inv ≫ f ≫ I.iso.inv) ≫ homComparison H P I := by
  simp only [computeCurry, LinearEquiv.trans_apply, Linear.homCongr_apply, Iso.symm_hom,
    Category.assoc]
  rfl

private theorem computeCurry_natural {Z Z' X X' Y Y' : derivedValue.{a} R}
    (S : Presentation Z) (S' : Presentation Z') (P : Presentation X) (P' : Presentation X')
    (I : Presentation Y) (I' : Presentation Y')
    (hP : isKFlat P.complex) (hP' : isKFlat P'.complex)
    (hI : I.complex.IsKInjective) (hI' : I'.complex.IsKInjective)
    {z : Z' ⟶ Z} {x : X' ⟶ X} {y : Y ⟶ Y'}
    (z₀ : S'.complex ⟶ S.complex) (x₀ : P'.complex ⟶ P.complex) (y₀ : I.complex ⟶ I'.complex)
    (hz : S'.Over S z z₀) (hx : P'.Over P x x₀) (hy : I.Over I' y y₀)
    (f : T.toDescent.tensorFunctor.obj (Z, X) ⟶ Y) :
    computeCurry T H S' P' I' hP' hI' (T.toDescent.tensorFunctor.map (Prod.mkHom z x) ≫ f ≫ y) =
      z ≫ computeCurry T H S P I hP hI f ≫ (rHomValue H).map (Prod.mkHom x.op y) := by
  let τ := tensorComparison T S P hP
  let τ' := tensorComparison T S' P' hP'
  have ht : τ'.inv ≫ T.toDescent.tensorFunctor.map (Prod.mkHom z x) =
      (qValue R).map (Specs.DerivedFormalization.CochainTensor.map z₀ x₀) ≫ τ.inv := by
    apply (cancel_mono τ.hom).1
    have hn : T.toDescent.tensorFunctor.map (Prod.mkHom z x) ≫ τ.hom =
        τ'.hom ≫ (qValue R).map (Specs.DerivedFormalization.CochainTensor.map z₀ x₀) :=
      tensorComparison_natural T S S' P P' hP hP' z₀ x₀ hz hx
    rw [Category.assoc, hn, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hi : y ≫ I'.iso.inv = I.iso.inv ≫ (qValue R).map y₀ := by
    apply (cancel_mono I'.iso.hom).1
    simp [Presentation.Over] at hy
    simp [Category.assoc, hy]
  have hs : S'.iso.inv ≫ (qValue R).map z₀ = z ≫ S.iso.inv := by
    apply (cancel_mono S.iso.hom).1
    simp [Presentation.Over] at hz
    simp [Category.assoc, hz]
  simp only [computeCurry_apply, Category.assoc]
  change S'.iso.inv ≫
      localizedCurry M S'.complex P'.complex I'.complex hP' hI'
        (τ'.inv ≫ T.toDescent.tensorFunctor.map (Prod.mkHom z x) ≫ f ≫ y ≫ I'.iso.inv) ≫
      homComparison H P' I' = _
  rw [hi, ← Category.assoc τ'.inv, ht, Category.assoc]
  have hn := localizedCurry_natural M hP hP' hI hI' z₀ x₀ y₀ (τ.inv ≫ f ≫ (I.iso.inv))
  simp only [Category.assoc] at hn
  rw [hn]
  simp only [Category.assoc]
  rw [homComparison_natural H P P' I I' (Or.inr hI) (Or.inr hI') x₀ y₀ hx hy,
    ← Category.assoc S'.iso.inv, hs, Category.assoc]

end Closed

private def presentationOf {X : derivedValue.{a} R}
    (P : Specs.DerivedFormalization.DerivedHomModels.Representative X) : Presentation X :=
  ⟨P.obj.as, ((quotientCompQhIsoValue R).app P.obj.as).symm ≪≫ P.iso⟩

private theorem existsProjectiveFlat [Small.{a} R] (X : derivedValue.{a} R) :
    ∃ P : Presentation X, P.complex.IsKProjective ∧ isKFlat P.complex := by
  let U := (qValue R).objPreimage X
  obtain ⟨P, p, hp, _, _, hP, hflat⟩ := SemifreeReplacement.nativeReplacement.{u,a} R U
  letI := hp
  exact ⟨⟨P, asIso ((qValue R).map p) ≪≫ (qValue R).objObjPreimageIso X⟩, hP, hflat⟩

private theorem overOfProjective {X Y : derivedValue.{a} R}
    (P : Presentation X) (S : Presentation Y) (hP : P.complex.IsKProjective) (f : X ⟶ Y) :
    ∃ g, P.Over S f g := by
  obtain ⟨g, hg⟩ := localizeHom_surj (mapsFromProjective P.complex S.complex hP)
    (P.iso.hom ≫ f ≫ S.iso.inv)
  exact ⟨g, by simp [Presentation.Over, hg]⟩

private theorem overIntoInjective {X Y : derivedValue.{a} R}
    (P : Presentation X) (S : Presentation Y) (hS : S.complex.IsKInjective) (f : X ⟶ Y) :
    ∃ g, P.Over S f g := by
  obtain ⟨g, hg⟩ := localizeHom_surj (mapsIntoInjective P.complex S.complex hS)
    (P.iso.hom ≫ f ≫ S.iso.inv)
  exact ⟨g, by simp [Presentation.Over, hg]⟩

private theorem closedData {A : Type a} [CommRing A] {e : R ≃+* A} {M : AdequateModel e}
    (T : Specs.DerivedFormalization.DerivedTensor.Model M) (H : Models.{u,a} R) :
    Nonempty (Closed T H) := by
  letI : Small.{a} R := small_of_injective e.injective
  let P (X : derivedValue.{a} R) := (existsProjectiveFlat X).choose
  have hp (X : derivedValue.{a} R) : (P X).complex.IsKProjective :=
    (existsProjectiveFlat X).choose_spec.1
  have hf (X : derivedValue.{a} R) : isKFlat (P X).complex :=
    (existsProjectiveFlat X).choose_spec.2
  let I (Y : derivedValue.{a} R) := presentationOf (H.injective Y)
  have hi (Y : derivedValue.{a} R) : (I Y).complex.IsKInjective := H.isInjective Y
  refine ⟨⟨fun Z X Y => computeCurry T H (P Z) (P X) (I Y) (hf X) (hi Y), ?_, ?_⟩⟩
  · intro Z Z' X X' Y Y' z x y f
    obtain ⟨z₀, hz⟩ := overOfProjective (P Z') (P Z) (hp Z') z
    obtain ⟨x₀, hx⟩ := overOfProjective (P X') (P X) (hp X') x
    obtain ⟨y₀, hy⟩ := overIntoInjective (I Y) (I Y') (hi Y') y
    exact computeCurry_natural T H (P Z) (P Z') (P X) (P X') (I Y) (I Y')
      (hf X) (hf X') (hi Y) (hi Y') z₀ x₀ y₀ hz hx hy f
  · intro Z X Y S U J hU hJ f
    let g := (tensorComparison T S U hU).hom ≫ (qValue R).map f ≫ J.iso.hom
    obtain ⟨z₀, hz⟩ := overOfProjective (P Z) S (hp Z) (𝟙 Z)
    obtain ⟨x₀, hx⟩ := overOfProjective (P X) U (hp X) (𝟙 X)
    obtain ⟨y₀, hy⟩ := overIntoInjective J (I Y) (hi Y) (𝟙 Y)
    have hn := computeCurry_natural T H S (P Z) U (P X) J (I Y)
      hU (hf X) hJ (hi Y) z₀ x₀ y₀ hz hx hy g
    change computeCurry T H (P Z) (P X) (I Y) (hf X) (hi Y)
      (T.toDescent.tensorFunctor.map (𝟙 _) ≫ g ≫ 𝟙 Y) =
      𝟙 Z ≫ computeCurry T H S U J hU hJ g ≫ (rHomValue H).map (𝟙 _) at hn
    rw [T.toDescent.tensorFunctor.map_id, (rHomValue H).map_id,
      Category.id_comp, Category.comp_id, Category.id_comp, Category.comp_id] at hn
    change computeCurry T H (P Z) (P X) (I Y) (hf X) (hi Y) g = _
    rw [hn, computeCurry_apply]
    simp only [g, Iso.inv_hom_id_assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [localizedCurry_map]

theorem closed : ClosedType.{u,a} :=
  fun T H => closedData T H


section Cohomology

open scoped CategoryTheory
open HomologicalComplex (homologyMap)
open private internalHomCohomology_natural from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ModelQuasiIsoInvariance

variable (H : Models.{u,a} R)

private theorem localizeHom_natural {B B' J J' : compValue.{a} R}
    (h : Function.Bijective ((qhValue.{a} R).map :
      ((quotientValue R).obj B ⟶ (quotientValue R).obj J) → _))
    (h' : Function.Bijective ((qhValue.{a} R).map :
      ((quotientValue R).obj B' ⟶ (quotientValue R).obj J') → _))
    (x : B' ⟶ B) (y : J ⟶ J')
    (f : (quotientValue R).obj B ⟶ (quotientValue R).obj J) :
    localizeHom B' J' h' ((quotientValue R).map x ≫ f ≫ (quotientValue R).map y) =
      (qValue R).map x ≫ localizeHom B J h f ≫ (qValue R).map y := by
  let g := f.out
  have hg : (quotientValue R).map g = f := HomotopyCategory.quotient_map_out f
  rw [← hg, ← (quotientValue R).map_comp, ← (quotientValue R).map_comp,
    localizeHom_map, localizeHom_map, (qValue R).map_comp, (qValue R).map_comp]

private theorem shiftedPresentation_natural {Y Y' : derivedValue.{a} R}
    (I : Presentation Y) (I' : Presentation Y') {y : Y ⟶ Y'}
    (y₀ : I.complex ⟶ I'.complex) (hy : I.Over I' y y₀) (n : ℤ) :
    (qValue R).map ((shiftFunctor (compValue.{a} R) n).map y₀) ≫
      (shiftedPresentation I' n).hom =
      (shiftedPresentation I n).hom ≫ (shiftFunctor (derivedValue.{a} R) n).map y := by
  let F := shiftFunctor (derivedValue.{a} R) n
  let e := qShiftIsoValue.{a} R n
  have hn := e.hom.naturality y₀
  change (qValue R).map ((shiftFunctor (compValue.{a} R) n).map y₀) ≫ e.hom.app I'.complex =
    e.hom.app I.complex ≫ F.map ((qValue R).map y₀) at hn
  have hy' : (qValue R).map y₀ ≫ I'.iso.hom = I.iso.hom ≫ y := hy
  change (qValue R).map ((shiftFunctor (compValue.{a} R) n).map y₀) ≫
    (e.hom.app I'.complex ≫ F.map I'.iso.hom) =
    (e.hom.app I.complex ≫ F.map I.iso.hom) ≫ F.map y
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, hy', F.map_comp, Category.assoc]

private def cohomologyComparisonIso {X Y : derivedValue.{a} R}
    (P : Presentation X) (I : Presentation Y) (hP : P.complex.IsKProjective) (n : ℤ) :
    (internalHomValue P.complex I.complex).homology n ≅
      (derivedCohomologyValue R n).obj ((rHomValue H).obj (op X, Y)) :=
  ((cohomologyFactorsValue R n).app (internalHomValue P.complex I.complex)).symm ≪≫
    (derivedCohomologyValue R n).mapIso (homComparisonIso H P I (Or.inl hP))

private theorem cohomologyComparisonIso_natural {X X' Y Y' : derivedValue.{a} R}
    (P : Presentation X) (P' : Presentation X') (I : Presentation Y) (I' : Presentation Y')
    (hP : P.complex.IsKProjective) (hP' : P'.complex.IsKProjective)
    {x : X' ⟶ X} {y : Y ⟶ Y'} (x₀ : P'.complex ⟶ P.complex)
    (y₀ : I.complex ⟶ I'.complex) (hx : P'.Over P x x₀) (hy : I.Over I' y y₀)
    (n : ℤ) :
    homologyMap (internalHomMapValue x₀ y₀) n ≫ (cohomologyComparisonIso H P' I' hP' n).hom =
      (cohomologyComparisonIso H P I hP n).hom ≫
        (derivedCohomologyValue R n).map ((rHomValue H).map (Prod.mkHom x.op y)) := by
  let m := internalHomMapValue x₀ y₀
  let F := derivedCohomologyValue.{a} R n
  let e := cohomologyFactorsValue.{a} R n
  have hn := e.inv.naturality m
  change homologyMap m n ≫ e.inv.app _ = e.inv.app _ ≫ F.map ((qValue R).map m) at hn
  change homologyMap m n ≫ (e.inv.app _ ≫ F.map (homComparison H P' I')) =
    (e.inv.app _ ≫ F.map (homComparison H P I)) ≫ F.map ((rHomValue H).map (Prod.mkHom x.op y))
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp,
    homComparison_natural H P P' I I' (Or.inl hP) (Or.inl hP') x₀ y₀ hx hy,
    F.map_comp, Category.assoc]

private def cohomologyOnComplex {X Y : derivedValue.{a} R}
    (P : Presentation X) (I : Presentation Y) (hP : P.complex.IsKProjective) (n : ℤ) :
    (internalHomValue P.complex I.complex).homology n ≃ₗ[R] (X ⟶ Y⟦n⟧) :=
  (internalHomCohomologyValue _ _ n).trans <|
    (localizeHom P.complex (I.complex⟦n⟧) (mapsFromProjective _ _ hP)).trans <|
      Linear.homCongr R P.iso (shiftedPresentation I n)

private theorem cohomologyOnComplex_apply {X Y : derivedValue.{a} R}
    (P : Presentation X) (I : Presentation Y) (hP : P.complex.IsKProjective) (n : ℤ)
    (z : (internalHomValue P.complex I.complex).homology n) :
    cohomologyOnComplex P I hP n z =
      P.iso.inv ≫ localizeHom P.complex (I.complex⟦n⟧) (mapsFromProjective _ _ hP)
        (internalHomCohomologyValue P.complex I.complex n z) ≫ (shiftedPresentation I n).hom := by
  simp only [cohomologyOnComplex, LinearEquiv.trans_apply, Linear.homCongr_apply, Category.assoc]
  rfl

private theorem cohomologyOnComplex_natural {X X' Y Y' : derivedValue.{a} R}
    (P : Presentation X) (P' : Presentation X') (I : Presentation Y) (I' : Presentation Y')
    (hP : P.complex.IsKProjective) (hP' : P'.complex.IsKProjective)
    {x : X' ⟶ X} {y : Y ⟶ Y'} (x₀ : P'.complex ⟶ P.complex)
    (y₀ : I.complex ⟶ I'.complex) (hx : P'.Over P x x₀) (hy : I.Over I' y y₀)
    (n : ℤ) (z : (internalHomValue P.complex I.complex).homology n) :
    cohomologyOnComplex P' I' hP' n (homologyMap (internalHomMapValue x₀ y₀) n z) =
      x ≫ cohomologyOnComplex P I hP n z ≫ (shiftFunctor (derivedValue.{a} R) n).map y := by
  have hn := internalHomCohomology_natural x₀ y₀ n z
  let y₁ := (shiftFunctor (compValue.{a} R) n).map y₀
  change internalHomCohomologyValue _ _ n (homologyMap (internalHomMapValue x₀ y₀) n z) =
    (quotientValue R).map x₀ ≫ internalHomCohomologyValue _ _ n z ≫ (quotientValue R).map y₁ at hn
  have hx' : P'.iso.inv ≫ (qValue R).map x₀ = x ≫ P.iso.inv := by
    apply (cancel_mono P.iso.hom).1
    have h : (qValue R).map x₀ ≫ P.iso.hom = P'.iso.hom ≫ x := hx
    rw [Category.assoc, h, Iso.inv_hom_id_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hy' : (qValue R).map y₁ ≫ (shiftedPresentation I' n).hom =
      (shiftedPresentation I n).hom ≫ (shiftFunctor (derivedValue.{a} R) n).map y :=
    shiftedPresentation_natural I I' y₀ hy n
  rw [cohomologyOnComplex_apply, cohomologyOnComplex_apply, hn,
    localizeHom_natural (mapsFromProjective P.complex (I.complex⟦n⟧) hP)]
  simp only [Category.assoc]
  rw [hy', ← Category.assoc P'.iso.inv, hx', Category.assoc]

private def computeCohomology {X Y : derivedValue.{a} R}
    (P : Presentation X) (I : Presentation Y) (hP : P.complex.IsKProjective) (n : ℤ) :
    ((derivedCohomologyValue R n).obj ((rHomValue H).obj (op X, Y))) ≃ₗ[R] (X ⟶ Y⟦n⟧) :=
  ((cohomologyComparisonIso H P I hP n).symm.toLinearEquiv).trans
    (cohomologyOnComplex P I hP n)

private theorem computeCohomology_on_iso {X Y : derivedValue.{a} R}
    (P : Presentation X) (I : Presentation Y) (hP : P.complex.IsKProjective) (n : ℤ)
    (z : (internalHomValue P.complex I.complex).homology n) :
    computeCohomology H P I hP n ((cohomologyComparisonIso H P I hP n).hom z) =
      cohomologyOnComplex P I hP n z :=
  congrArg (cohomologyOnComplex P I hP n)
    ((cohomologyComparisonIso H P I hP n).toLinearEquiv.symm_apply_apply z)

private theorem computeCohomology_natural {X X' Y Y' : derivedValue.{a} R}
    (P : Presentation X) (P' : Presentation X') (I : Presentation Y) (I' : Presentation Y')
    (hP : P.complex.IsKProjective) (hP' : P'.complex.IsKProjective)
    {x : X' ⟶ X} {y : Y ⟶ Y'} (x₀ : P'.complex ⟶ P.complex)
    (y₀ : I.complex ⟶ I'.complex) (hx : P'.Over P x x₀) (hy : I.Over I' y y₀)
    (n : ℤ) (z : (derivedCohomologyValue R n).obj ((rHomValue H).obj (op X, Y))) :
    computeCohomology H P' I' hP' n ((derivedCohomologyValue R n).map
        ((rHomValue H).map (Prod.mkHom x.op y)) z) =
      x ≫ computeCohomology H P I hP n z ≫ (shiftFunctor (derivedValue.{a} R) n).map y := by
  obtain ⟨w, rfl⟩ := (cohomologyComparisonIso H P I hP n).toLinearEquiv.surjective z
  change computeCohomology H P' I' hP' n
    (((cohomologyComparisonIso H P I hP n).hom ≫
      (derivedCohomologyValue R n).map ((rHomValue H).map (Prod.mkHom x.op y))) w) =
    x ≫ computeCohomology H P I hP n ((cohomologyComparisonIso H P I hP n).hom w) ≫
      (shiftFunctor (derivedValue.{a} R) n).map y
  rw [← cohomologyComparisonIso_natural H P P' I I' hP hP' x₀ y₀ hx hy n,
    ModuleCat.comp_apply, computeCohomology_on_iso, computeCohomology_on_iso]
  exact cohomologyOnComplex_natural P P' I I' hP hP' x₀ y₀ hx hy n w

theorem cohomology : CohomologyType.{u,a} := by
  intro R _ H
  let P (X : derivedValue.{a} R) := presentationOf (H.projective X)
  let I (Y : derivedValue.{a} R) := presentationOf (H.injective Y)
  have hp (X : derivedValue.{a} R) : (P X).complex.IsKProjective := H.isProjective X
  have hi (Y : derivedValue.{a} R) : (I Y).complex.IsKInjective := H.isInjective Y
  refine ⟨⟨fun X Y n => computeCohomology H (P X) (I Y) (hp X) n, ?_, ?_⟩⟩
  · intro X X' Y Y' x y n z
    obtain ⟨x₀, hx⟩ := overOfProjective (P X') (P X) (hp X') x
    obtain ⟨y₀, hy⟩ := overIntoInjective (I Y) (I Y') (hi Y') y
    exact computeCohomology_natural H (P X) (P X') (I Y) (I Y') (hp X) (hp X') x₀ y₀ hx hy n z
  · intro X Y B J hB n z
    let w := (cohomologyComparisonIso H B J hB n).hom z
    obtain ⟨x₀, hx⟩ := overOfProjective (P X) B (hp X) (𝟙 X)
    obtain ⟨y₀, hy⟩ := overIntoInjective J (I Y) (hi Y) (𝟙 Y)
    have hn := computeCohomology_natural H B (P X) J (I Y) hB (hp X) x₀ y₀ hx hy n w
    change computeCohomology H (P X) (I Y) (hp X) n
        ((derivedCohomologyValue R n).map ((rHomValue H).map (𝟙 _)) w) =
      𝟙 X ≫ computeCohomology H B J hB n w ≫ (shiftFunctor (derivedValue.{a} R) n).map (𝟙 Y) at hn
    rw [(rHomValue H).map_id, (derivedCohomologyValue R n).map_id, ModuleCat.id_apply,
      (shiftFunctor (derivedValue.{a} R) n).map_id, Category.id_comp, Category.comp_id] at hn
    change computeCohomology H (P X) (I Y) (hp X) n w = _
    rw [hn, computeCohomology_on_iso, cohomologyOnComplex_apply, localizeHom_apply]
    simp only [Category.assoc]

end Cohomology

theorem liftedInputs : LiftedInputs.{u,v,w,t,s} := by
  intro R _
  dsimp only
  let e := Specs.DerivedFormalization.CochainRingTransport.uliftRingEquivValue.{max u v w t s} R
  let M := CochainTensorTransport.adequateModelData e
  let T := DerivedTensor.model M
  let H := DerivedHomModels.models.{u,max v w t s} R
  obtain ⟨c⟩ := closed T H
  obtain ⟨h⟩ := cohomology H
  refine ⟨M, T, H, c, h, ?_, DerivedHomModels.originalComparison.{u,w,t,max v s},
    DerivedHomModels.mixedProductComparison.{u,w,t,max v s}⟩
  intro Z X Y
  exact ⟨c.adjunction _, c.adjunction_homEquiv _ _ _⟩

end
end DerivedFormalization.DerivedHomAdjunction
