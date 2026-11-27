import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedScalarExtension
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.DerivedTensor
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.SemifreeReplacement
import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.ScalarExtensionTransport
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.CategoryTheory.Localization.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.Equivalence
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Localization.OfQuotient
import Mathlib.Algebra.Homology.Precylinder
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Adjunction.Mates
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! Derived extension of scalars and the comparisons on its models. -/

namespace DerivedFormalization.DerivedScalarExtension

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Specs.DerivedFormalization
open Specs.DerivedFormalization.DerivedScalarExtension
open Specs.DerivedFormalization.Cochains (compValue derivedValue homotopyValue qValue qhValue
  quotientValue quotientCompQhIsoValue)
open Specs.DerivedFormalization.DerivedTensor (Descent Model flatQh flatQuasiIso kFlatHomotopy)
open Specs.DerivedFormalization.CochainTensor (isKFlat)
open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel)
open Specs.DerivedFormalization.ScalarExtensionTransport (extension)

universe u w z a v

attribute [local instance] HasDerivedCategory.standard
set_option linter.style.haveILetI false

noncomputable section

private theorem model_naturality {R : Type u} {S : Type w} [CommRing R] [CommRing S]
    {F : compValue.{a} R ⥤ compValue.{a} S} (L : Lift F)
    {P Q : compValue.{a} R} (hP : isKFlat P) (hQ : isKFlat Q) (k : P ⟶ Q) :
    L.derived.map ((qValue R).map k) ≫ (L.model Q hQ).hom =
      (L.model P hP).hom ≫ (qValue S).map (F.map k) :=
  L.factors.hom.naturality (ObjectProperty.homMk (X := ⟨P, hP⟩) (Y := ⟨Q, hQ⟩) k)

set_option backward.isDefEq.respectTransparency false in
theorem originalPresentations : OriginalPresentations.{u,w,a,v} := by
  intro R S _ _ B _ d f L j J E
  constructor
  · intro X
    obtain ⟨P, p, hp, hs, hf, hP, _, _, _⟩ :=
      SemifreeReplacement.adequateReplacement.{u,v,max w a} R X
    haveI := hp
    exact ⟨P, p, hp, hP, hs, hf, ⟨originalModel.{u,w,a,v} L p hP⟩⟩
  · intro X Y P Q p q hp hq hP hQ k l h
    let qR := qValue.{max u w v a} R
    let aX := (CochainCoefficientLift.liftDFactors.{max u w a, v} R).app X
    let aY := (CochainCoefficientLift.liftDFactors.{max u w a, v} R).app Y
    haveI : IsIso (qR.map p) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
    haveI : IsIso (qR.map q) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
    let p' := asIso (qR.map p)
    let q' := asIso (qR.map q)
    have h₁ : (qValue R ⋙ J).map k ≫ aY.hom = aX.hom ≫ qR.map (j.map k) :=
      (CochainCoefficientLift.liftDFactors.{max u w a, v} R).hom.naturality k
    have h₂ : qR.map (j.map k) ≫ q'.inv = p'.inv ≫ qR.map l := by
      apply (cancel_epi p'.hom).mp
      apply (cancel_mono q'.hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id]
      change qR.map p ≫ qR.map (j.map k) = qR.map l ≫ qR.map q
      rw [← qR.map_comp, ← qR.map_comp, h]
    change L.derived.map ((qValue R ⋙ J).map k) ≫
        L.derived.map (aY.hom ≫ q'.inv) ≫ (L.toLift.model Q (L.projectiveFlat Q hQ)).hom =
      (L.derived.map (aX.hom ≫ p'.inv) ≫ (L.toLift.model P (L.projectiveFlat P hP)).hom) ≫
        (qValue S).map (E.map l)
    have h₃ : (qValue R ⋙ J).map k ≫ (aY.hom ≫ q'.inv) =
        (aX.hom ≫ p'.inv) ≫ qR.map l := by
      calc
        _ = ((qValue R ⋙ J).map k ≫ aY.hom) ≫ q'.inv := (Category.assoc ..).symm
        _ = _ := by
          rw [h₁, Category.assoc, h₂, Category.assoc]
    rw [← Functor.map_comp_assoc, h₃, Functor.map_comp_assoc,
      model_naturality L.toLift (L.projectiveFlat P hP) (L.projectiveFlat Q hQ) l]
    simp only [Category.assoc, E]


section MonoidalLocalization

open Functor.LaxMonoidal BraidedCategory

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]

/-- A monoidal functor preserves braiding if its composite with an
essentially surjective braided functor does. -/
@[instance_reducible]
private def braidedOfComp (J : C ⥤ D) [J.EssSurj] [J.Braided]
    (F : D ⥤ E) [F.Monoidal] (h : ∀ X Y : C,
      μ (J ⋙ F) X Y ≫ (J ⋙ F).map (β_ X Y).hom =
        (β_ ((J ⋙ F).obj X) ((J ⋙ F).obj Y)).hom ≫ μ (J ⋙ F) Y X) :
    F.Braided where
  toMonoidal := inferInstance
  braided X Y := by
    have hp (U V : C) :
        μ F (J.obj U) (J.obj V) ≫ F.map (β_ (J.obj U) (J.obj V)).hom =
          (β_ (F.obj (J.obj U)) (F.obj (J.obj V))).hom ≫ μ F (J.obj V) (J.obj U) := by
      apply (cancel_mono (F.map (μ J V U))).mp
      have hUV := h U V
      simp only [Functor.comp_map, Functor.comp_obj, comp_μ, Category.assoc] at hUV
      rw [← Functor.map_comp, Functor.LaxBraided.braided (F := J), Functor.map_comp] at hUV
      simpa only [Category.assoc] using hUV
    let b := J.objObjPreimageIso X
    let c := J.objObjPreimageIso Y
    apply (cancel_epi (tensorIso (F.mapIso b) (F.mapIso c)).hom).mp
    change (F.map b.hom ⊗ₘ F.map c.hom) ≫ μ F X Y ≫ F.map (β_ X Y).hom =
      (F.map b.hom ⊗ₘ F.map c.hom) ≫ (β_ (F.obj X) (F.obj Y)).hom ≫ μ F Y X
    rw [μ_natural_assoc, ← Functor.map_comp, braiding_naturality, Functor.map_comp,
      reassoc_of% hp, braiding_naturality_assoc, μ_natural]

@[instance_reducible]
private def braidedLift (J : C ⥤ D) (W : MorphismProperty C) [J.IsLocalization W]
    [J.Braided] [W.ContainsIdentities] (F : D ⥤ E) (G : C ⥤ E) [G.Braided]
    (e : J ⋙ F ≅ G) : F.Braided := by
  letI : Localization.Lifting J W G F := ⟨e⟩
  letI : F.Monoidal := Localization.Monoidal.functorMonoidalOfComp J W F G
  haveI : NatTrans.IsMonoidal e.hom :=
    Localization.Monoidal.lifting_isMonoidal J W F G
  haveI : NatTrans.IsMonoidal e.symm.hom :=
    inferInstanceAs (NatTrans.IsMonoidal e.inv)
  letI : (J ⋙ F).LaxBraided := Functor.LaxBraided.ofNatIso e.symm
  haveI := Localization.essSurj (L := J) W
  exact braidedOfComp J F (Functor.LaxBraided.braided (F := J ⋙ F))

private theorem braidedLift_factors (J : C ⥤ D) (W : MorphismProperty C) [J.IsLocalization W]
    [J.Braided] [W.ContainsIdentities] (F : D ⥤ E) (G : C ⥤ E) [G.Braided]
    (e : J ⋙ F ≅ G) :
    letI := braidedLift J W F G e
    NatTrans.IsMonoidal e.hom := by
  letI : Localization.Lifting J W G F := ⟨e⟩
  exact Localization.Monoidal.lifting_isMonoidal J W F G

/-- The full subcategories inherit the tensor comparison of a braided
functor that carries the source property to the target property. -/
@[instance_reducible]
private def braidedRestriction (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsMonoidal] [Q.IsMonoidal] (F : C ⥤ D) [F.Braided]
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj)) :
    (Q.lift (P.ι ⋙ F) hF).Braided := by
  let G := Q.lift (P.ι ⋙ F) hF
  let H := P.ι ⋙ F
  let core : G.CoreMonoidal :=
    { εIso := Q.isoMk (Functor.Monoidal.εIso H)
      μIso := fun X Y => Q.isoMk (Functor.Monoidal.μIso H X Y)
      μIso_hom_natural_left := fun f Y => Q.hom_ext (μ_natural_left H f Y)
      μIso_hom_natural_right := fun X f => Q.hom_ext (μ_natural_right H X f)
      associativity := fun X Y Z => Q.hom_ext (associativity H X Y Z)
      left_unitality := fun X => by
        apply Q.hom_ext
        change (λ_ (H.obj X)).hom = ε H ▷ H.obj X ≫ μ H _ X ≫ H.map (λ_ X).hom
        exact left_unitality H X
      right_unitality := fun X => by
        apply Q.hom_ext
        change (ρ_ (H.obj X)).hom = H.obj X ◁ ε H ≫ μ H X _ ≫ H.map (ρ_ X).hom
        exact right_unitality H X }
  letI : G.Monoidal := core.toMonoidal
  change G.Braided
  refine { toMonoidal := inferInstance, braided := fun X Y => ?_ }
  apply Q.hom_ext
  exact Functor.LaxBraided.braided (F := H) X Y

private theorem braidedRestriction_μ (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsMonoidal] [Q.IsMonoidal] (F : C ⥤ D) [F.Braided]
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj)) (X Y : P.FullSubcategory) :
    letI := braidedRestriction P Q F hF
    (μ (Q.lift (P.ι ⋙ F) hF) X Y).hom = μ F X.obj Y.obj := by
  letI := braidedRestriction P Q F hF
  change μ (P.ι ⋙ F) X Y = _
  simp only [comp_μ, ObjectProperty.ι_μ]
  change μ F X.obj Y.obj ≫ F.map (𝟙 _) = _
  rw [F.map_id, Category.comp_id]

private theorem braidedRestriction_ε (P : ObjectProperty C) (Q : ObjectProperty D)
    [P.IsMonoidal] [Q.IsMonoidal] (F : C ⥤ D) [F.Braided]
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj)) :
    letI := braidedRestriction P Q F hF
    (ε (Q.lift (P.ι ⋙ F) hF)).hom = ε F := by
  letI := braidedRestriction P Q F hF
  change ε (P.ι ⋙ F) = _
  simp only [comp_ε, ObjectProperty.ι_ε]
  change ε F ≫ F.map (𝟙 _) = _
  rw [F.map_id, Category.comp_id]

end MonoidalLocalization

section FlatHomotopy

open Specs.DerivedFormalization.CochainTensorTransport (representedUnit)
open Specs.DerivedFormalization.DerivedTensor (flatObject)

variable {R : Type u} {A : Type a} [CommRing R] [CommRing A] {e : R ≃+* A}
  (M : AdequateModel e)

private def homotopyTensorComparison (X Y : compValue.{a} R) :
    letI := M.homotopyMonoidal
    (quotientValue R).obj (CochainTensor.tensor X Y) ≅
      (quotientValue R).obj X ⊗ (quotientValue R).obj Y :=
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  (quotientValue R).mapIso (M.tensorModel X Y) ≪≫
    (Functor.Monoidal.μIso (quotientValue R) X Y).symm

private theorem flat_of_homotopy_iso (M : AdequateModel e) {X Y : compValue.{a} R}
    (i : (quotientValue R).obj X ≅ (quotientValue R).obj Y) (hX : isKFlat X) : isKFlat Y := by
  intro E hE
  letI := M.homotopyMonoidal
  let j := homotopyTensorComparison M E X ≪≫ tensorIso (Iso.refl _) i ≪≫
    (homotopyTensorComparison M E Y).symm
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).1
    (ObjectProperty.prop_of_iso _ j
      ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hX E hE)))

private theorem projective_flat (M : AdequateModel e) {P : compValue.{a} R} (hP : P.IsKProjective) : isKFlat P := by
  haveI : Small.{a} R := Small.mk ⟨A, ⟨e.toEquiv⟩⟩
  obtain ⟨Q, q, hq, _, _, hQ, hflat⟩ :=
    SemifreeReplacement.nativeReplacement.{u,a} R P
  haveI := hP
  haveI := hQ
  have hi : IsIso ((quotientValue R).map q) := by
    have h := (CochainComplex.IsKProjective.quasiIso_iff q).1 hq
    exact HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ _ h
  exact flat_of_homotopy_iso M (asIso ((quotientValue R).map q)) hflat

open HomologicalComplex HomotopicalAlgebra

private abbrev flatQuot (R : Type u) [CommRing R] :
    (flatComplexes.{u,a} R).FullSubcategory ⥤ (kFlatHomotopy.{u,a} R).FullSubcategory :=
  (kFlatHomotopy.{u,a} R).lift ((flatComplexes.{u,a} R).ι ⋙ quotientValue R) fun P => P.property

private instance (R : Type u) [CommRing R] : (flatQuot.{u,a} R).EssSurj where
  mem_essImage := fun ⟨⟨X⟩, hX⟩ => ⟨⟨X, hX⟩, ⟨Iso.refl _⟩⟩

private abbrev flatChainEquivalences (R : Type u) [CommRing R] :
    MorphismProperty (flatComplexes.{u,a} R).FullSubcategory :=
  (homotopyEquivalences (ModuleCat.{a} R) (.up ℤ)).inverseImage (flatComplexes.{u,a} R).ι

private abbrev flatChainQuasiIso (R : Type u) [CommRing R] :
    MorphismProperty (flatComplexes.{u,a} R).FullSubcategory :=
  (HomologicalComplex.quasiIso (ModuleCat.{a} R) (.up ℤ)).inverseImage (flatComplexes.{u,a} R).ι

private instance (R : Type u) [CommRing R] : (flatQuot.{u,a} R).Full where
  map_surjective f := by
    obtain ⟨k, hk⟩ := (HomotopyCategory.quotient (ModuleCat.{a} R) (.up ℤ)).map_surjective f.hom
    exact ⟨ObjectProperty.homMk k, ObjectProperty.hom_ext _ hk⟩

private theorem flatQuot_isLocalization (M : AdequateModel e) :
    (flatQuot.{u,a} R).IsLocalization (flatChainEquivalences.{u,a} R) := by
  apply Functor.isLocalization_of_essSurj_of_full_of_exists_cylinders
  · intro X Y f hf
    have hi : IsIso ((kFlatHomotopy.{u,a} R).ι.map ((flatQuot.{u,a} R).map f)) := by
      change IsIso ((HomotopyCategory.quotient (ModuleCat.{a} R) (.up ℤ)).map f.hom)
      exact HomotopyCategory.quotient_inverts_homotopyEquivalences _ _ _ hf
    exact isIso_of_reflects_iso _ (kFlatHomotopy.{u,a} R).ι
  · intro X Y f₀ f₁ hf
    have hh := HomotopyCategory.homotopyOfEq f₀.hom f₁.hom
      ((kFlatHomotopy.{u,a} R).ι.congr_map hf)
    let he := cylinder.homotopyEquiv X.obj (fun (n : ℤ) => ⟨n - 1, by simp⟩)
    have hC : isKFlat X.obj.cylinder :=
      flat_of_homotopy_iso M (HomotopyCategory.isoOfHomotopyEquiv he).symm X.property
    let cyl := X.obj.precylinder.toFullSubcategory (P := flatComplexes.{u,a} R) hC
    exact ⟨cyl, Precylinder.LeftHomotopy.fullSubcategoryEquiv.symm
      { h := cylinder.desc _ _ hh
        h₀ := cylinder.ι₀_desc _ _ hh
        h₁ := cylinder.ι₁_desc _ _ hh }, ⟨he, rfl⟩⟩

private theorem flatQ_isLocalization (M : AdequateModel e)
    [loc : (flatQh.{u,a} R).IsLocalization (flatQuasiIso.{u,a} R)] :
    (flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R) := by
  haveI := flatQuot_isLocalization M
  haveI hcomp : (flatQuot.{u,a} R ⋙ flatQh.{u,a} R).IsLocalization
      (flatChainQuasiIso.{u,a} R) := by
    refine Functor.IsLocalization.comp _ _ (flatChainEquivalences.{u,a} R)
      (flatQuasiIso.{u,a} R) _ ?_ ?_ ?_
    · intro X Y f hf
      exact Localization.inverts (flatQh.{u,a} R) (flatQuasiIso.{u,a} R)
        ((flatQuot.{u,a} R).map f) ((HomotopyCategory.quotient_map_mem_quasiIso_iff f.hom).2 hf)
    · intro X Y f hf
      exact homotopyEquivalences_le_quasiIso _ _ _ hf
    · rintro ⟨⟨X⟩, hX⟩ ⟨⟨Y⟩, hY⟩ f hf
      let U : (flatComplexes.{u,a} R).FullSubcategory := ⟨X, hX⟩
      let V : (flatComplexes.{u,a} R).FullSubcategory := ⟨Y, hY⟩
      obtain ⟨k, rfl⟩ := (flatQuot.{u,a} R).map_surjective (X := U) (Y := V) f
      exact ⟨_, _, k, (HomotopyCategory.quotient_map_mem_quasiIso_iff k.hom).1 hf,
        ⟨Iso.refl _⟩⟩
  let fc : flatQuot.{u,a} R ⋙ flatQh.{u,a} R ≅ flatQ.{u,a} R :=
    NatIso.ofComponents (fun X => (quotientCompQhIsoValue R).app X.obj)
      (fun f => (quotientCompQhIsoValue R).hom.naturality f.hom)
  exact Functor.IsLocalization.of_iso (flatChainQuasiIso.{u,a} R) fc

end FlatHomotopy

section AdjunctionConstruction

open Specs.DerivedFormalization.DerivedRestriction (restrictScalarsComplexValue
  derivedRestrictScalarsValue derivedRestrictScalarsFactorsValue)

/-- A natural unit with bijective transposition determines an adjunction. -/
private def adjunctionOfUnit {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G)
    (hη : ∀ X Y, Function.Bijective (fun k : F.obj X ⟶ Y => η.app X ≫ G.map k)) :
    F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y => Equiv.ofBijective _ (hη X Y)
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        apply (Equiv.ofBijective _ (hη X' Y)).injective
        simp only [Equiv.apply_symm_apply, Equiv.ofBijective_apply, Functor.map_comp,
          ← Category.assoc]
        have hn := η.naturality f
        change f ≫ η.app X = η.app X' ≫ G.map (F.map f) at hn
        rw [← hn, Category.assoc]
        change f ≫ g = f ≫ (Equiv.ofBijective _ (hη X Y))
          ((Equiv.ofBijective _ (hη X Y)).symm g)
        rw [Equiv.apply_symm_apply]
      homEquiv_naturality_right := fun f g => by
        simp only [Equiv.ofBijective_apply, Functor.map_comp, Category.assoc] }

private theorem adjunctionOfUnit_homEquiv {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G)
    (hη : ∀ X Y, Function.Bijective (fun k : F.obj X ⟶ Y => η.app X ≫ G.map k))
    {X : C} {Y : D} (k : F.obj X ⟶ Y) :
    (adjunctionOfUnit η hη).homEquiv X Y k = η.app X ≫ G.map k := by
  simp [adjunctionOfUnit]

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S]
  {f : R →+* S} {F : compValue.{a} R ⥤ compValue.{a} S}

private def unitOnFlat (adj₀ : F ⊣ restrictScalarsComplexValue.{a} f) (L : Lift F) :
    flatQ.{u,a} R ⟶ flatQ.{u,a} R ⋙ L.derived ⋙ derivedRestrictScalarsValue.{a} f :=
  let j := (flatComplexes.{u,a} R).ι
  let qR := qValue.{a} R
  let RU := derivedRestrictScalarsValue.{a} f
  let α := derivedRestrictScalarsFactorsValue.{a} f
  Functor.whiskerLeft j (qR.leftUnitor.inv ≫ Functor.whiskerRight adj₀.unit qR) ≫
    Functor.whiskerLeft (j ⋙ F) α.inv ≫
    Functor.whiskerRight L.factors.inv RU ≫
    (Functor.associator _ _ _).hom

private def localizedUnit [loc : (flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)]
    (adj₀ : F ⊣ restrictScalarsComplexValue.{a} f) (L : Lift F) :
    𝟭 (derivedValue.{a} R) ⟶ L.derived ⋙ derivedRestrictScalarsValue.{a} f :=
  let I := flatQ.{u,a} R
  let H := L.derived ⋙ derivedRestrictScalarsValue.{a} f
  let W := flatChainQuasiIso.{u,a} R
  letI : Localization.Lifting I W I (𝟭 _) := ⟨I.rightUnitor⟩
  letI : Localization.Lifting I W (I ⋙ H) H := ⟨Iso.refl _⟩
  Localization.liftNatTrans I W I (I ⋙ H) (𝟭 _) H (unitOnFlat adj₀ L)

set_option backward.isDefEq.respectTransparency false in
private theorem localizedUnit_app
    [loc : (flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)]
    (adj₀ : F ⊣ restrictScalarsComplexValue.{a} f) (L : Lift F)
    (P : compValue.{a} R) (hP : isKFlat P) :
    (localizedUnit adj₀ L).app ((qValue R).obj P) =
      (qValue R).map (adj₀.unit.app P) ≫
        (derivedRestrictScalarsFactorsValue f).inv.app (F.obj P) ≫
        (derivedRestrictScalarsValue f).map (L.model P hP).inv := by
  change (localizedUnit adj₀ L).app ((flatQ.{u,a} R).obj ⟨P,hP⟩) = _
  unfold localizedUnit
  rw [Localization.liftNatTrans_app]
  simp [Localization.Lifting.iso, unitOnFlat, Lift.model]

set_option backward.isDefEq.respectTransparency false in
private theorem unit_model_transposition
    [loc : (flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)]
    (adj₀ : F ⊣ restrictScalarsComplexValue.{a} f) (L : Lift F)
    (P : compValue.{a} R) (Y : compValue.{a} S) (hP : isKFlat P) (k : F.obj P ⟶ Y) :
    (localizedUnit adj₀ L).app ((qValue R).obj P) ≫
        (derivedRestrictScalarsValue f).map
          ((L.model P hP).hom ≫ (qValue S).map k) =
      (qValue R).map (adj₀.homEquiv P Y k) ≫
        (derivedRestrictScalarsFactorsValue f).inv.app Y := by
  rw [localizedUnit_app adj₀ L P hP, Functor.map_comp, Adjunction.homEquiv_unit]
  simp only [Category.assoc, Iso.inv_hom_id_map_assoc]
  have h := (derivedRestrictScalarsFactorsValue.{a} f).inv.naturality k
  change (qValue R).map ((restrictScalarsComplexValue f).map k) ≫
      (derivedRestrictScalarsFactorsValue f).inv.app Y =
    (derivedRestrictScalarsFactorsValue f).inv.app (F.obj P) ≫
      (derivedRestrictScalarsValue f).map ((qValue S).map k) at h
  rw [← h, ← Functor.map_comp_assoc]

private def projectiveHomEquiv {R : Type u} [CommRing R]
    (P Y : compValue.{a} R) [P.IsKProjective] :
    ((quotientValue R).obj P ⟶ (quotientValue R).obj Y) ≃
      ((qValue R).obj P ⟶ (qValue R).obj Y) :=
  (Equiv.ofBijective _ (CochainComplex.IsKProjective.Qh_map_bijective P ((quotientValue R).obj Y))).trans
    (((quotientCompQhIsoValue R).app P).homCongr ((quotientCompQhIsoValue R).app Y))

@[simp]
private theorem projectiveHomEquiv_quotient {R : Type u} [CommRing R]
    (P Y : compValue.{a} R) [P.IsKProjective] (h : P ⟶ Y) :
    projectiveHomEquiv P Y ((quotientValue R).map h) = (qValue R).map h := by
  have eq := (quotientCompQhIsoValue R).hom.naturality h
  change (qhValue R).map ((quotientValue R).map h) ≫ (quotientCompQhIsoValue R).hom.app Y =
    (quotientCompQhIsoValue R).hom.app P ≫ (qValue R).map h at eq
  change (quotientCompQhIsoValue R).inv.app P ≫
      (qhValue R).map ((quotientValue R).map h) ≫ (quotientCompQhIsoValue R).hom.app Y = _
  rw [eq, Iso.inv_hom_id_app_assoc]

section HomotopyAdjunction

variable {E : ModuleCat.{a} R ⥤ ModuleCat.{a} S} [E.Additive]

local notation "Ek" => Functor.mapHomotopyCategory E (ComplexShape.up ℤ)
local notation "Uk" => Functor.mapHomotopyCategory (ModuleCat.restrictScalars f) (ComplexShape.up ℤ)
local notation "Er" => Functor.mapHomologicalComplex E (ComplexShape.up ℤ)

private def homotopyAdjunction (adj₀ : Er ⊣ restrictScalarsComplexValue.{a} f) : Ek ⊣ Uk := by
  letI : CatCommSq Er (quotientValue.{a} R) (quotientValue.{a} S) Ek :=
    ⟨(E.mapHomotopyCategoryFactors (.up ℤ)).symm⟩
  letI : CatCommSq (restrictScalarsComplexValue.{a} f) (quotientValue.{a} S)
      (quotientValue.{a} R) Uk :=
    ⟨((ModuleCat.restrictScalars.{a} f).mapHomotopyCategoryFactors (.up ℤ)).symm⟩
  haveI : (quotientValue.{a} R).IsLocalization
      (HomologicalComplex.homotopyEquivalences (ModuleCat.{a} R) (.up ℤ)) :=
    inferInstanceAs ((HomotopyCategory.quotient (ModuleCat.{a} R) (.up ℤ)).IsLocalization _)
  haveI : (quotientValue.{a} S).IsLocalization
      (HomologicalComplex.homotopyEquivalences (ModuleCat.{a} S) (.up ℤ)) :=
    inferInstanceAs ((HomotopyCategory.quotient (ModuleCat.{a} S) (.up ℤ)).IsLocalization _)
  exact adj₀.localization (quotientValue.{a} R) (HomologicalComplex.homotopyEquivalences _ _)
    (quotientValue.{a} S) (HomologicalComplex.homotopyEquivalences _ _) Ek Uk

set_option backward.isDefEq.respectTransparency false in
@[simp]
private theorem homotopyAdjunction_transpose (adj₀ : Er ⊣ restrictScalarsComplexValue.{a} f)
    (P : compValue.{a} R) (Y : compValue.{a} S) (k : (Er).obj P ⟶ Y) :
    (homotopyAdjunction adj₀).homEquiv ((quotientValue R).obj P) ((quotientValue S).obj Y)
        ((quotientValue S).map k) = (quotientValue R).map (adj₀.homEquiv P Y k) := by
  rw [Adjunction.homEquiv_unit, homotopyAdjunction, Adjunction.localization_unit_app,
    Adjunction.homEquiv_unit]
  change (quotientValue R).map (adj₀.unit.app P) ≫ 𝟙 _ ≫ (Uk).map (𝟙 _) ≫
      (Uk).map ((quotientValue S).map k) = (quotientValue R).map _
  simp only [Category.id_comp]
  change (quotientValue R).map (adj₀.unit.app P) ≫
    (quotientValue R).map ((restrictScalarsComplexValue f).map k) = _
  rw [← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
private theorem localizedUnit_bijective
    [loc : (flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)]
    (adj₀ : Er ⊣ restrictScalarsComplexValue.{a} f) (L : Lift Er)
    (hflat : ∀ P : compValue.{a} R, P.IsKProjective → isKFlat P)
    (hproj : ∀ P : compValue.{a} R, P.IsKProjective → CochainComplex.IsKProjective ((Er).obj P))
    (models : ∀ X : derivedValue.{a} R,
      ∃ P : compValue.{a} R, P.IsKProjective ∧ Nonempty ((qValue R).obj P ≅ X)) :
    ∀ X Y, Function.Bijective (fun k : L.derived.obj X ⟶ Y =>
      (localizedUnit adj₀ L).app X ≫ (derivedRestrictScalarsValue f).map k) := by
  intro X Y
  obtain ⟨P, hp, ⟨xp⟩⟩ := models X
  haveI := Localization.essSurj (L := qValue.{a} S) (HomologicalComplex.quasiIso _ _)
  let Y₀ := (qValue.{a} S).objPreimage Y
  let yp := (qValue.{a} S).objObjPreimageIso Y
  let U := derivedRestrictScalarsValue.{a} f
  let η := localizedUnit adj₀ L
  let a₀ := L.model P (hflat P hp)
  haveI := hp
  haveI := hproj P hp
  let b := Iso.homCongr a₀ (Iso.refl ((qValue S).obj Y₀))
  let c := Iso.homCongr (Iso.refl ((qValue R).obj P))
    ((derivedRestrictScalarsFactorsValue.{a} f).app Y₀).symm
  let equiv :=
    b.trans ((projectiveHomEquiv ((Er).obj P) Y₀).symm.trans
      (((homotopyAdjunction adj₀).homEquiv ((quotientValue R).obj P) ((quotientValue S).obj Y₀)).trans
        ((projectiveHomEquiv P ((restrictScalarsComplexValue f).obj Y₀)).trans c)))
  have on_model : Function.Bijective
      (fun k : L.derived.obj ((qValue R).obj P) ⟶ (qValue S).obj Y₀ =>
        η.app ((qValue R).obj P) ≫ U.map k) := by
    convert equiv.bijective using 1
    funext k
    obtain ⟨l, hl⟩ := (projectiveHomEquiv ((Er).obj P) Y₀).surjective (b k)
    obtain ⟨l₀, rfl⟩ :=
      (HomotopyCategory.quotient (ModuleCat.{a} S) (.up ℤ)).map_surjective l
    change projectiveHomEquiv ((Er).obj P) Y₀ ((quotientValue S).map l₀) = b k at hl
    have hk : k = a₀.hom ≫ (qValue S).map l₀ := by
      have h := hl
      rw [projectiveHomEquiv_quotient] at h
      change (qValue S).map l₀ = a₀.inv ≫ k ≫ 𝟙 _ at h
      rw [Category.comp_id] at h
      rw [h, Iso.hom_inv_id_assoc]
    calc
      _ = (qValue R).map (adj₀.homEquiv P Y₀ l₀) ≫
          (derivedRestrictScalarsFactorsValue f).inv.app Y₀ := by
        rw [hk]
        exact unit_model_transposition adj₀ L P Y₀ (hflat P hp) l₀
      _ = equiv k := by
        simp only [equiv, Equiv.trans_apply]
        rw [← hl, Equiv.symm_apply_apply]
        erw [homotopyAdjunction_transpose adj₀ P Y₀ l₀]
        erw [projectiveHomEquiv_quotient P ((restrictScalarsComplexValue f).obj Y₀)]
        change _ = 𝟙 _ ≫ (qValue R).map (adj₀.homEquiv P Y₀ l₀) ≫
          (derivedRestrictScalarsFactorsValue f).inv.app Y₀
        rw [Category.id_comp]
  let pre := Iso.homCongr (L.derived.mapIso xp.symm) yp.symm
  let post := Iso.homCongr xp (U.mapIso yp)
  convert post.bijective.comp (on_model.comp pre.bijective) using 1
  funext k
  simp only [Function.comp_apply, pre, post, Iso.homCongr_apply, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.symm_inv, Iso.symm_hom, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
  have eq := η.naturality xp.hom
  change xp.hom ≫ η.app X = η.app ((qValue R).obj P) ≫ U.map (L.derived.map xp.hom) at eq
  change η.app X ≫ U.map k =
    xp.inv ≫ η.app ((qValue R).obj P) ≫ U.map (L.derived.map xp.hom ≫ k)
  rw [U.map_comp, ← reassoc_of% eq, Iso.inv_hom_id_assoc]

end HomotopyAdjunction

private theorem projective_presentations {A : Type a} [CommRing A] (e : R ≃+* A)
    (X : derivedValue.{a} R) :
    ∃ P : compValue.{a} R, P.IsKProjective ∧ Nonempty ((qValue R).obj P ≅ X) := by
  haveI : Small.{a} R := Small.mk ⟨A, ⟨e.toEquiv⟩⟩
  haveI := Localization.essSurj (L := qValue.{a} R) (HomologicalComplex.quasiIso _ _)
  let P := (qValue.{a} R).objPreimage X
  obtain ⟨Q, q, hq, _, _, hp, _⟩ := SemifreeReplacement.nativeReplacement.{u,a} R P
  haveI : IsIso ((qValue R).map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  exact ⟨Q, hp, ⟨asIso ((qValue R).map q) ≪≫ (qValue R).objObjPreimageIso X⟩⟩

end AdjunctionConstruction


section ExtensionConstruction

open Specs.DerivedFormalization.DerivedRestriction (restrictScalarsComplexValue)
open Specs.DerivedFormalization.CochainTensorTransport (representedUnit)
open Specs.DerivedFormalization.CochainRingTransport (representedExtension)
open Specs.DerivedFormalization.ScalarExtensionTransport (ModelStability extensionAdjunction)

variable {R : Type u} {S : Type w} {A B : Type a} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B} {f : R →+* S}
  {MR : AdequateModel e}

private theorem quasiIso_of_iso_square {C : Type*} [Category* C] [Abelian C]
    {X Y X' Y' : CochainComplex C ℤ}
    {i : X ≅ X'} {j : Y ≅ Y'} {k : X ⟶ Y} {l : X' ⟶ Y'}
    (h : k ≫ j.hom = i.hom ≫ l) : QuasiIso k ↔ QuasiIso l := by
  rw [← quasiIso_iff_comp_right k j.hom, h, quasiIso_iff_comp_left]

private theorem flatMap_quasiIso (M : Model MR) (U : compValue.{a} R)
    {P Q : compValue.{a} R} (hP : isKFlat P) (hQ : isKFlat Q) (k : P ⟶ Q)
    (hk : QuasiIso k) : QuasiIso (CochainTensor.map (𝟙 U) k) := by
  let qR := qValue.{a} R
  let m := M.toDescent.tensorFunctor
  haveI : IsIso (qR.map k) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ k).2 hk
  haveI : IsIso (qR.map (𝟙 U)) := by rw [qR.map_id]; infer_instance
  let b : (qR.obj U, qR.obj P) ≅ (qR.obj U, qR.obj Q) :=
    Iso.prod (asIso (qR.map (𝟙 U))) (asIso (qR.map k))
  have h := M.compare_natural (𝟙 U) k (Or.inr hP) (Or.inr hQ)
  change m.map b.hom ≫ (M.compare U Q (Or.inr hQ)).hom =
    (M.compare U P (Or.inr hP)).hom ≫ qR.map (CochainTensor.map (𝟙 U) k) at h
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).1
  exact IsIso.of_isIso_fac_left h.symm

private def leftUnitModel (MS : AdequateModel d) (P : compValue.{a} S) :
    CochainTensor.tensor (representedUnit d) P ≅ P :=
  letI := MS.chainMonoidal
  MS.tensorModel _ _ ≪≫ tensorIso MS.unitModel (Iso.refl P) ≪≫ λ_ P

private theorem leftUnitModel_naturality (MS : AdequateModel d)
    {P Q : compValue.{a} S} (k : P ⟶ Q) :
    CochainTensor.map (𝟙 (representedUnit d)) k ≫ (leftUnitModel MS Q).hom =
      (leftUnitModel MS P).hom ≫ k := by
  letI := MS.chainMonoidal
  simp only [leftUnitModel, Iso.trans_hom, tensorIso_hom, Iso.refl_hom, Category.assoc]
  rw [reassoc_of% MS.tensorModel_natural]
  have ht : (𝟙 (representedUnit d) ⊗ₘ k) ≫ (MS.unitModel.hom ⊗ₘ 𝟙 Q) =
      (MS.unitModel.hom ⊗ₘ 𝟙 P) ≫ (𝟙 (𝟙_ (compValue.{a} S)) ⊗ₘ k) := by
    calc
      _ = (𝟙 (representedUnit d) ≫ MS.unitModel.hom) ⊗ₘ (k ≫ 𝟙 Q) :=
        tensorHom_comp_tensorHom _ _ _ _
      _ = (MS.unitModel.hom ≫ 𝟙 (𝟙_ (compValue.{a} S))) ⊗ₘ (𝟙 P ≫ k) := by
        simp only [Category.id_comp, Category.comp_id]
      _ = _ := (tensorHom_comp_tensorHom _ _ _ _).symm
  rw [reassoc_of% ht, id_tensorHom, leftUnitor_naturality]

set_option backward.isDefEq.respectTransparency false in
private theorem extension_quasiIso (MS : AdequateModel d)
    (M : Model MR) (stability : ModelStability d f)
    {P Q : compValue.{a} R} (hP : isKFlat P) (hQ : isKFlat Q) (k : P ⟶ Q)
    (hk : QuasiIso k) : QuasiIso ((extension d f).map k) := by
  let E := representedUnit d
  let K := CochainTensor.map (𝟙 E) ((extension d f).map k)
  let U := restrictScalarsComplexValue.{a} f
  have hn := stability.cancel_natural (𝟙 E) k
  change U.map K ≫ (stability.cancel E Q).hom =
    (stability.cancel E P).hom ≫ CochainTensor.map (U.map (𝟙 E)) k at hn
  rw [U.map_id] at hn
  have hu : QuasiIso (U.map K) :=
    (quasiIso_of_iso_square hn).2 (flatMap_quasiIso M (U.obj E) hP hQ k hk)
  have hK : QuasiIso K :=
    (HomologicalComplex.quasiIso_map_iff_of_preservesHomology K
      (ModuleCat.restrictScalars.{a} f)).1 hu
  exact (quasiIso_of_iso_square (leftUnitModel_naturality MS ((extension d f).map k))).1 hK

private def liftToDerived
    [loc : (flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)]
    (E : compValue.{a} R ⥤ compValue.{a} S)
    (hE : ∀ {P Q} (_ : isKFlat P) (_ : isKFlat Q) (k : P ⟶ Q),
      QuasiIso k → QuasiIso (E.map k)) : Lift E :=
  let qr := flatQ.{u,a} R
  let E' := (flatComplexes.{u,a} R).ι ⋙ E ⋙ qValue.{a} S
  have hE' : (flatChainQuasiIso.{u,a} R).IsInvertedBy E' := fun P Q k hk =>
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 (hE P.property Q.property k.hom hk)
  ⟨Localization.lift E' hE' qr, Localization.fac E' hE' qr⟩

set_option backward.isDefEq.respectTransparency false in
private def makeAdjointModel (MR : AdequateModel e)
    [loc : (flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)]
    {E : ModuleCat.{a} R ⥤ ModuleCat.{a} S} [E.Additive]
    (adj₀ : E.mapHomologicalComplex (.up ℤ) ⊣ restrictScalarsComplexValue.{a} f)
    (L : Lift (E.mapHomologicalComplex (.up ℤ)))
    (flat : ∀ P : compValue.{a} R, isKFlat P → isKFlat ((E.mapHomologicalComplex (.up ℤ)).obj P))
    (proj : ∀ P : compValue.{a} R, P.IsKProjective →
      CochainComplex.IsKProjective ((E.mapHomologicalComplex (.up ℤ)).obj P)) :
    AdjointModel f (E.mapHomologicalComplex (.up ℤ)) adj₀ :=
  { toLift := L
    adj := adjunctionOfUnit (localizedUnit adj₀ L)
      (localizedUnit_bijective adj₀ L (fun _ => projective_flat MR) proj (projective_presentations e))
    preservesFlat := flat
    preservesProjective := proj
    projectiveFlat := fun _ => projective_flat MR
    adj_on_model := fun P Y hP k => by
      rw [adjunctionOfUnit_homEquiv]
      exact unit_model_transposition adj₀ L P Y (projective_flat MR hP) k }

/-- Extension to the original target ring, computed on the U07 flat localization
and adjoint to the actual restriction functor. -/
private def adjointExtension (MS : AdequateModel d) (DR : Descent MR)
    (M : Model MR) (stability : ModelStability d f) : Extension d f := by
  haveI := DR.localization
  haveI := flatQ_isLocalization MR
  haveI : (representedExtension d f).Additive :=
    (Specs.DerivedFormalization.CochainRingTransport.representedExtensionAdjunction d f).left_adjoint_additive
  let L := liftToDerived (extension d f) (fun hP hQ => extension_quasiIso MS M stability hP hQ)
  exact makeAdjointModel MR (E := representedExtension d f) (extensionAdjunction d f) L
    stability.preserves_kFlat stability.preserves_kProjective

end ExtensionConstruction


section FlatTensor

open Functor.LaxMonoidal
open Specs.DerivedFormalization.CochainTensorTransport (representedUnit)
open Specs.DerivedFormalization.DerivedTensor (flatObject)

attribute [local instance] CochainTensorMonoidal.cochainMonoidalValue

@[instance_reducible]
private def braidedTransport {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C] [BraidedCategory D]
    {F G : C ⥤ D} [F.Braided] (e : F ≅ G) : G.Braided := by
  letI : G.Monoidal := Functor.Monoidal.transport e
  haveI : NatTrans.IsMonoidal e.hom := Functor.Monoidal.natTransIsMonoidal_of_transport e
  letI : G.LaxBraided := Functor.LaxBraided.ofNatIso e
  exact { toMonoidal := inferInstance, braided := Functor.LaxBraided.braided (F := G) }

private theorem inverseMonoidal {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (P : ObjectProperty D) [P.IsClosedUnderIsomorphisms] [P.IsMonoidal] (F : C ⥤ D)
    [F.Monoidal] : (P.inverseImage F).IsMonoidal where
  prop_unit := P.prop_of_iso (Functor.Monoidal.εIso F) P.prop_unit
  prop_tensor X Y hX hY :=
    P.prop_of_iso (Functor.Monoidal.μIso F X Y) (ObjectProperty.prop_tensor hX hY : P _)

variable {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}

private theorem flatHomotopy_closed (M : AdequateModel e) :
    (kFlatHomotopy.{u,a} R).IsClosedUnderIsomorphisms where
  of_iso {X Y} i h := by
    obtain ⟨X⟩ := X
    obtain ⟨Y⟩ := Y
    exact flat_of_homotopy_iso M i h

private theorem flatComplexes_monoidal (M : AdequateModel e)
    [MonoidalCategory (compValue.{a} R)] [MonoidalCategory (homotopyValue.{a} R)]
    [(kFlatHomotopy.{u,a} R).IsMonoidal] [(quotientValue.{a} R).Monoidal] :
    (flatComplexes.{u,a} R).IsMonoidal := by
  haveI := flatHomotopy_closed M
  exact inverseMonoidal (kFlatHomotopy.{u,a} R) (quotientValue.{a} R)

private def flatQuotFactors (R : Type u) [CommRing R] :
    flatQuot.{u,a} R ⋙ flatQh.{u,a} R ≅ flatQ.{u,a} R :=
  NatIso.ofComponents (fun X => (quotientCompQhIsoValue R).app X.obj)
    (fun f => (quotientCompQhIsoValue R).hom.naturality f.hom)

variable (R)
  [MonoidalCategory (compValue.{a} R)] [BraidedCategory (compValue.{a} R)]
  [MonoidalCategory (homotopyValue.{a} R)] [BraidedCategory (homotopyValue.{a} R)]
  [MonoidalCategory (derivedValue.{a} R)] [BraidedCategory (derivedValue.{a} R)]
  [(flatComplexes.{u,a} R).IsMonoidal] [(kFlatHomotopy.{u,a} R).IsMonoidal]
  [(quotientValue.{a} R).Braided] [(flatQh.{u,a} R).Braided]

@[instance_reducible]
private def flatQuotBraided : (flatQuot.{u,a} R).Braided :=
  braidedRestriction _ _ (quotientValue.{a} R) (fun P => P.property)

@[instance_reducible]
private def flatQBraided : (flatQ.{u,a} R).Braided :=
  letI := flatQuotBraided R
  braidedTransport (flatQuotFactors R)

set_option backward.isDefEq.respectTransparency false in
private theorem flatQ_μ (X Y : (flatComplexes.{u,a} R).FullSubcategory) :
    letI := flatQBraided R
    μ (flatQ.{u,a} R) X Y =
      (tensorIso ((quotientCompQhIsoValue R).app X.obj).symm
        ((quotientCompQhIsoValue R).app Y.obj).symm).hom ≫
        μ (flatQh.{u,a} R) ((flatQuot.{u,a} R).obj X) ((flatQuot.{u,a} R).obj Y) ≫
        (qhValue R).map (μ (quotientValue.{a} R) X.obj Y.obj) ≫
        (quotientCompQhIsoValue R).hom.app (X.obj ⊗ Y.obj) := by
  letI := flatQuotBraided R
  letI := flatQBraided R
  change μ (flatQ.{u,a} R) X Y =
    ((flatQuotFactors R).inv.app X ⊗ₘ (flatQuotFactors R).inv.app Y) ≫
        μ (flatQh.{u,a} R) ((flatQuot.{u,a} R).obj X) ((flatQuot.{u,a} R).obj Y) ≫
        (qhValue R).map (μ (quotientValue.{a} R) X.obj Y.obj) ≫
        (flatQuotFactors R).hom.app (X ⊗ Y)
  rw [Functor.Monoidal.transport_μ, comp_μ, Category.assoc]
  change _ ≫ _ ≫ (qhValue R).map (μ (flatQuot R) X Y).hom ≫ _ = _
  rw [braidedRestriction_μ (flatComplexes.{u,a} R) (kFlatHomotopy.{u,a} R)]

set_option backward.isDefEq.respectTransparency false in
private theorem flatQ_ε :
    letI := flatQBraided R
    ε (flatQ.{u,a} R) =
      ε (flatQh.{u,a} R) ≫ (qhValue R).map (ε (quotientValue.{a} R)) ≫
        (quotientCompQhIsoValue R).hom.app (𝟙_ (compValue.{a} R)) := by
  letI := flatQuotBraided R
  letI := flatQBraided R
  rw [Functor.Monoidal.transport_ε, comp_ε, Category.assoc]
  change _ ≫ (qhValue R).map (ε (flatQuot R)).hom ≫ _ = _
  rw [braidedRestriction_ε (flatComplexes.{u,a} R) (kFlatHomotopy.{u,a} R)]
  rfl

end FlatTensor


section DerivedTensorator

open Functor.LaxMonoidal
open Functor.Monoidal (εIso μIso)
open Specs.DerivedFormalization.CochainTensorTransport (representedUnit)
open Specs.DerivedFormalization.ScalarExtensionTransport (MonoidalChange)

variable {R : Type u} {S : Type w} {A B : Type a} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B} {f : R →+* S}
  {MR : AdequateModel e} {MS : AdequateModel d}

private abbrev flatMap (F : compValue.{a} R ⥤ compValue.{a} S)
    (hF : ∀ P, isKFlat P → isKFlat (F.obj P)) :
    (flatComplexes.{u,a} R).FullSubcategory ⥤ (flatComplexes.{w,a} S).FullSubcategory :=
  (flatComplexes.{w,a} S).lift ((flatComplexes.{u,a} R).ι ⋙ F) fun P => hF P.obj P.property

private def liftFactors {F : compValue.{a} R ⥤ compValue.{a} S}
    (L : Lift F) (hF : ∀ P, isKFlat P → isKFlat (F.obj P)) :
    flatQ.{u,a} R ⋙ L.derived ≅ flatMap F hF ⋙ flatQ.{w,a} S :=
  NatIso.ofComponents (fun P => L.factors.app P) (fun k => L.factors.hom.naturality k)

variable [MonoidalCategory (compValue.{a} R)] [BraidedCategory (compValue.{a} R)]
  [MonoidalCategory (compValue.{a} S)] [BraidedCategory (compValue.{a} S)]
  [(flatComplexes.{u,a} R).IsMonoidal] [(flatComplexes.{w,a} S).IsMonoidal]
  [MonoidalCategory (derivedValue.{a} R)] [BraidedCategory (derivedValue.{a} R)]
  [MonoidalCategory (derivedValue.{a} S)] [BraidedCategory (derivedValue.{a} S)]
  [(flatQ.{u,a} R).Braided] [(flatQ.{w,a} S).Braided]
  [(flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)]
  {F : compValue.{a} R ⥤ compValue.{a} S} [F.Braided]
  (L : Lift F) (hF : ∀ P, isKFlat P → isKFlat (F.obj P))

@[instance_reducible]
private def derivedBraided : L.derived.Braided := by
  letI : (flatMap F hF).Braided :=
    braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{w,a} S) F
      (fun P => hF P.obj P.property)
  exact braidedLift (flatQ.{u,a} R) (flatChainQuasiIso.{u,a} R)
    L.derived (flatMap F hF ⋙ flatQ.{w,a} S) (liftFactors L hF)

private theorem derivedBraided_factors :
    letI := derivedBraided L hF
    letI : (flatMap F hF).Braided := braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{w,a} S) F
      (fun P => hF P.obj P.property)
    (liftFactors L hF).hom.IsMonoidal :=
  letI : (flatMap F hF).Braided := braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{w,a} S) F
      (fun P => hF P.obj P.property)
  braidedLift_factors (flatQ.{u,a} R) (flatChainQuasiIso.{u,a} R)
    L.derived (flatMap F hF ⋙ flatQ.{w,a} S) (liftFactors L hF)

set_option backward.isDefEq.respectTransparency false in
private theorem derivedBraided_μ (P Q : (flatComplexes.{u,a} R).FullSubcategory) :
    letI := derivedBraided L hF
    μ L.derived ((qValue R).obj P.obj) ((qValue R).obj Q.obj) ≫
      L.derived.map (μ (flatQ.{u,a} R) P Q) ≫
      (L.model (P ⊗ Q).obj (P ⊗ Q).property).hom =
    ((L.model P.obj P.property).hom ⊗ₘ (L.model Q.obj Q.property).hom) ≫
      μ (flatQ.{w,a} S) ((flatMap F hF).obj P) ((flatMap F hF).obj Q) ≫
      (qValue S).map (μ F P.obj Q.obj) := by
  letI := derivedBraided L hF
  letI : (flatMap F hF).Braided := braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{w,a} S) F
      (fun P => hF P.obj P.property)
  haveI := derivedBraided_factors L hF
  have h := NatTrans.IsMonoidal.tensor (τ := (liftFactors L hF).hom) P Q
  simp only [comp_μ, Category.assoc] at h
  change _ = _ ≫ _ ≫ (qValue S).map (μ (flatMap F hF) P Q).hom at h
  rw [braidedRestriction_μ (flatComplexes.{u,a} R) (flatComplexes.{w,a} S)] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem derivedBraided_ε :
    letI := derivedBraided L hF
    ε L.derived ≫ L.derived.map (ε (flatQ.{u,a} R)) ≫
      (L.model (𝟙_ (flatComplexes.{u,a} R).FullSubcategory).obj
        (𝟙_ (flatComplexes.{u,a} R).FullSubcategory).property).hom =
    ε (flatQ.{w,a} S) ≫ (qValue S).map (ε F) := by
  letI := derivedBraided L hF
  letI : (flatMap F hF).Braided := braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{w,a} S) F
      (fun P => hF P.obj P.property)
  haveI := derivedBraided_factors L hF
  have h := NatTrans.IsMonoidal.unit (τ := (liftFactors L hF).hom)
  simp only [comp_ε, Category.assoc] at h
  change _ = _ ≫ (qValue S).map (ε (flatMap F hF)).hom at h
  rw [braidedRestriction_ε (flatComplexes.{u,a} R) (flatComplexes.{w,a} S)] at h
  exact h

end DerivedTensorator


section OriginalBraiding

open Functor.LaxMonoidal
open Functor.Monoidal (εIso μIso)
open Specs.DerivedFormalization.CochainTensorTransport (representedUnit)
open Specs.DerivedFormalization.ScalarExtensionTransport (MonoidalChange)

variable {R : Type u} {S : Type w} {A B : Type a} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B} {f : R →+* S}
  {MR : AdequateModel e} {MS : AdequateModel d}
  (DR : Descent MR) (DS : Descent MS)

set_option backward.isDefEq.respectTransparency false in
private theorem flatComparison_μ :
    letI := MR.chainMonoidal
    letI := MR.chainSymmetric
    letI := MR.homotopyMonoidal
    letI := MR.homotopySymmetric
    letI := MR.quotientBraided
    letI := DR.flatMonoidal
    letI := DR.monoidal
    letI := DR.symmetric
    letI := DR.braided
    letI := flatComplexes_monoidal MR
    letI := flatQBraided R
    ∀ (P Q : (flatComplexes.{u,a} R).FullSubcategory),
      (DR.flatComparison P.obj Q.obj P.property Q.property).hom =
        μ (flatQ.{u,a} R) P Q ≫ (qValue R).map (MR.tensorModel P.obj Q.obj).inv := by
  intros
  rw [flatQ_μ]
  simp only [Descent.flatComparison, Iso.trans_hom, Functor.mapIso_hom, Functor.Monoidal.μIso_hom, Category.assoc]
  erw [(quotientCompQhIsoValue R).hom.naturality (MR.tensorModel _ _).inv]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem unitComparison_ε :
    letI := MR.chainMonoidal
    letI := MR.chainSymmetric
    letI := MR.homotopyMonoidal
    letI := MR.homotopySymmetric
    letI := MR.quotientBraided
    letI := DR.flatMonoidal
    letI := DR.monoidal
    letI := DR.symmetric
    letI := DR.braided
    letI := flatComplexes_monoidal MR
    letI := flatQBraided R
    DR.unitComparison.hom =
      ε (flatQ.{u,a} R) ≫ (qValue R).map MR.unitModel.inv := by
  rw [flatQ_ε]
  simp only [Descent.unitComparison, Iso.trans_hom, Functor.mapIso_hom, Functor.Monoidal.εIso_hom, Category.assoc]
  erw [(quotientCompQhIsoValue R).hom.naturality MR.unitModel.inv]

set_option backward.isDefEq.respectTransparency false in
private def makeMonoidalExtension (F : MonoidalChange e d f MR MS) (L : Extension d f) :
    MonoidalExtension DR DS F L := by
  letI := MR.chainMonoidal
  letI := MR.chainSymmetric
  letI := MR.homotopyMonoidal
  letI := MR.homotopySymmetric
  letI := MR.quotientBraided
  letI := DR.flatMonoidal
  letI := DR.monoidal
  letI := DR.symmetric
  letI := DR.braided
  letI := flatComplexes_monoidal MR
  letI := flatQBraided R
  letI := MS.chainMonoidal
  letI := MS.chainSymmetric
  letI := MS.homotopyMonoidal
  letI := MS.homotopySymmetric
  letI := MS.quotientBraided
  letI := DS.flatMonoidal
  letI := DS.monoidal
  letI := DS.symmetric
  letI := DS.braided
  letI := flatComplexes_monoidal MS
  letI := flatQBraided S
  haveI := DR.localization
  haveI := flatQ_isLocalization MR
  letI := F.extensionBraided
  let I := L.toLift
  let E := extension d f
  let G := flatMap E L.preservesFlat
  letI := derivedBraided I L.preservesFlat
  refine { braided := inferInstance, tensor_on_models := ?_, unit_on_model := ?_ }
  · intro P Q hP hQ hPQ
    let X : (flatComplexes.{u,a} R).FullSubcategory := ⟨P, hP⟩
    let Y : (flatComplexes.{u,a} R).FullSubcategory := ⟨Q, hQ⟩
    have hm := derivedBraided_μ I L.preservesFlat X Y
    have hs := model_naturality I (X ⊗ Y).property hPQ (MR.tensorModel P Q).inv
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.Monoidal.μIso_hom, Functor.mapIso_hom, Iso.symm_hom,
      tensorIso_hom]
    rw [flatComparison_μ DR X Y]
    erw [flatComparison_μ DS (G.obj X) (G.obj Y)]
    simp only [Functor.map_comp, Category.assoc]
    erw [hs, reassoc_of% hm]
    let a := (L.toLift.model P hP).hom ⊗ₘ (L.toLift.model Q hQ).hom
    let b := μ (flatQ.{w,a} S) (G.obj X) (G.obj Y)
    let i := MS.tensorModel (E.obj P) (E.obj Q)
    let q := qValue S
    let k := q.map (μ E P Q) ≫ q.map (E.map (MR.tensorModel P Q).inv)
    change a ≫ b ≫ k = a ≫ b ≫ q.map i.inv ≫ q.map i.hom ≫ k
    rw [Iso.inv_hom_id_map_assoc]
  · intro h
    have hm := derivedBraided_ε I L.preservesFlat
    have hs := model_naturality I (𝟙_ (flatComplexes.{u,a} R).FullSubcategory).property h MR.unitModel.inv
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.Monoidal.εIso_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [unitComparison_ε DR, unitComparison_ε DS]
    simp only [Functor.map_comp, Category.assoc]
    erw [hs, reassoc_of% hm]
    simp only [Iso.inv_hom_id_map_assoc]

end OriginalBraiding


section RingTensorTransport

open Specs.DerivedFormalization.CochainRingTransport (complexFunctorValue homotopyFunctorValue
  derivedFunctorValue derivedFactorsValue derivedFactorshValue)
open Specs.DerivedFormalization.CochainTensorTransport (representedUnit)
open Functor.LaxMonoidal
open Functor.Monoidal (εIso μIso)
attribute [local instance] CochainTensorMonoidal.cochainMonoidalValue

private theorem monoidalOfEquivalence {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (E : C ≌ D) [E.functor.Monoidal]
    (P : ObjectProperty C) [P.IsMonoidal] (Q : ObjectProperty D) [Q.IsClosedUnderIsomorphisms]
    (h : ∀ X, Q (E.functor.obj X) ↔ P X) : Q.IsMonoidal where
  prop_unit :=
    Q.prop_of_iso (εIso E.functor).symm ((h _).2 P.prop_unit)
  prop_tensor X Y hX hY := by
    let i := E.counitIso.app X
    let j := E.counitIso.app Y
    have hx := (h _).1 (Q.prop_of_iso i.symm hX)
    have hy := (h _).1 (Q.prop_of_iso j.symm hY)
    exact Q.prop_of_iso ((μIso E.functor _ _).symm ≪≫ tensorIso i j)
      ((h _).2 (ObjectProperty.prop_tensor hx hy))

variable {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
    {M : AdequateModel e}

private def diagonalAdequacy (A : Type a) [CommRing A] : AdequateModel (RingEquiv.refl A) :=
  Classical.choice (DerivedFormalization.CochainTensorTransport.adequateModel (RingEquiv.refl A))

private theorem ringFlat_iff (M : AdequateModel e) (X : homotopyValue.{a} R) :
    kFlatHomotopy.{a,a} A ((homotopyFunctorValue e).obj X) ↔ kFlatHomotopy.{u,a} R X := by
  obtain ⟨X⟩ := X
  exact M.kFlat X

set_option backward.isDefEq.respectTransparency false in
private def flatRingEquivalence (M : AdequateModel e) :
    (kFlatHomotopy.{u,a} R).FullSubcategory ≌ (kFlatHomotopy.{a,a} A).FullSubcategory := by
  haveI := flatHomotopy_closed (diagonalAdequacy A)
  apply (DerivedFormalization.CochainRingTransport.homotopyEquivalence e).congrFullSubcategory
  ext X
  exact ringFlat_iff M X

private def flatRingFactors (M : AdequateModel e) :
    flatQh.{u,a} R ⋙ derivedFunctorValue e ≅ (flatRingEquivalence M).functor ⋙ flatQh.{a,a} A :=
  NatIso.ofComponents (fun X => (derivedFactorshValue e).app X.obj)
    (fun k => (derivedFactorshValue e).hom.naturality k.hom)

set_option backward.isDefEq.respectTransparency false in
private theorem flatQh_isIso_iff {X Y : (kFlatHomotopy.{u,a} R).FullSubcategory} (k : X ⟶ Y) :
    IsIso ((flatQh.{u,a} R).map k) ↔ flatQuasiIso.{u,a} R k := by
  obtain ⟨⟨X⟩, hx⟩ := X
  obtain ⟨⟨Y⟩, hy⟩ := Y
  obtain ⟨l, hl⟩ := (HomotopyCategory.quotient (ModuleCat.{a} R) (.up ℤ)).map_surjective k.hom
  change IsIso ((qhValue R).map k.hom) ↔
    HomotopyCategory.quasiIso (ModuleCat.{a} R) (.up ℤ) k.hom
  rw [← hl, HomotopyCategory.quotient_map_mem_quasiIso_iff l]
  exact ((NatIso.isIso_map_iff (quotientCompQhIsoValue R) l)).trans
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ l)

private theorem flatRing_preserves_reflects (M : AdequateModel e)
    {X Y : (kFlatHomotopy.{u,a} R).FullSubcategory} (k : X ⟶ Y) :
    flatQuasiIso.{a,a} A ((flatRingEquivalence M).functor.map k) ↔ flatQuasiIso.{u,a} R k := by
  rw [← flatQh_isIso_iff, ← flatQh_isIso_iff]
  let E := DerivedFormalization.CochainRingTransport.derivedEquivalence e
  haveI : (derivedFunctorValue e).ReflectsIsomorphisms :=
    inferInstanceAs E.functor.ReflectsIsomorphisms
  exact ((NatIso.isIso_map_iff (flatRingFactors M) k).symm).trans
    (isIso_iff_of_reflects_iso ((flatQh.{u,a} R).map k) (derivedFunctorValue e))

private theorem nativeFlatLocalization (D : Descent M) :
    (flatQh.{a,a} A).IsLocalization (flatQuasiIso.{a,a} A) := by
  haveI := D.localization
  let E := flatRingEquivalence M
  let E' := DerivedFormalization.CochainRingTransport.derivedEquivalence e
  letI : CatCommSq E.functor (flatQh.{u,a} R) (flatQh.{a,a} A) E'.functor :=
    ⟨(flatRingFactors M).symm⟩
  refine Functor.IsLocalization.of_equivalences (flatQh.{u,a} R) (flatQuasiIso.{u,a} R)
    (flatQh.{a,a} A) (flatQuasiIso.{a,a} A) E E' ?_ ?_
  · intro X Y k hk
    exact (flatQuasiIso.{a,a} A).le_isoClosure _ ((flatRing_preserves_reflects M k).2 hk)
  · intro X Y k hk
    exact (flatQh_isIso_iff k).2 hk

private theorem nativeFlatMonoidal (D : Descent M) :
    letI := M.nativeHomotopyMonoidal
    (kFlatHomotopy.{a,a} A).IsMonoidal := by
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.nativeHomotopyMonoidal
  letI := M.nativeHomotopySymmetric
  letI := M.homotopyTransport
  haveI := D.flatMonoidal
  haveI := flatHomotopy_closed (diagonalAdequacy A)
  let E := DerivedFormalization.CochainRingTransport.homotopyEquivalence e
  letI : E.functor.Monoidal := M.homotopyTransport.toMonoidal
  exact monoidalOfEquivalence E (kFlatHomotopy.{u,a} R) (kFlatHomotopy.{a,a} A)
    (ringFlat_iff M)

private theorem flatQuasiIso_monoidal (D : Descent M) :
    letI := M.homotopyMonoidal
    letI := D.flatMonoidal
    (flatQuasiIso.{u,a} R).IsMonoidal := by
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := D.flatMonoidal
  letI := D.monoidal
  letI := D.symmetric
  letI := D.braided
  refine MorphismProperty.IsMonoidal.mk' _ (fun f g hf hg => ?_)
  apply (flatQh_isIso_iff (f ⊗ₘ g)).1
  let q := flatQh.{u,a} R
  haveI : IsIso (q.map f) := (flatQh_isIso_iff f).2 hf
  haveI : IsIso (q.map g) := (flatQh_isIso_iff g).2 hg
  haveI : IsIso (q.map f ⊗ₘ q.map g) := (tensorIso (asIso (q.map f)) (asIso (q.map g))).isIso_hom
  change IsIso (q.map (f ⊗ₘ g))
  rw [Functor.Monoidal.map_tensor]
  infer_instance

private theorem nativeFlatQuasiIso_monoidal (D : Descent M) :
    letI := M.nativeHomotopyMonoidal
    letI := nativeFlatMonoidal D
    (flatQuasiIso.{a,a} A).IsMonoidal := by
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.nativeHomotopyMonoidal
  letI := M.nativeHomotopySymmetric
  letI := M.homotopyTransport
  haveI := D.flatMonoidal
  haveI := nativeFlatMonoidal D
  haveI := flatQuasiIso_monoidal D
  let E := flatRingEquivalence M
  letI : E.functor.Braided :=
    braidedRestriction (kFlatHomotopy.{u,a} R) (kFlatHomotopy.{a,a} A) (homotopyFunctorValue e)
      (fun P => (ringFlat_iff M P.obj).2 P.property)
  letI : E.inverse.Monoidal := E.inverseMonoidal
  let W := flatQuasiIso.{u,a} R
  let V := flatQuasiIso.{a,a} A
  have hW : W.inverseImage E.inverse = V := by
    ext X Y f
    change W (E.inverse.map f) ↔ V f
    exact (flatRing_preserves_reflects M (E.inverse.map f)).symm.trans
      (V.arrow_mk_iso_iff (((Functor.mapArrowFunctor _ _).mapIso E.counitIso).app (Arrow.mk f)))
  have h : (W.inverseImage E.inverse).IsMonoidal := inferInstance
  change V.IsMonoidal
  exact hW ▸ h

private def makeNativeTensor (D : Descent M) : NativeTensor M := by
  letI := M.nativeHomotopyMonoidal
  letI := M.nativeHomotopySymmetric
  letI := nativeFlatMonoidal D
  haveI := nativeFlatLocalization D
  haveI := nativeFlatQuasiIso_monoidal D
  let q := flatQh.{a,a} A
  let W := flatQuasiIso.{a,a} A
  let i := Iso.refl (q.obj (𝟙_ _))
  let N := LocalizedMonoidal q W i
  let m : MonoidalCategory N := inferInstance
  let s : SymmetricCategory N := inferInstance
  let b : (Localization.Monoidal.toMonoidalCategory q W i).Braided := inferInstance
  exact ⟨nativeFlatMonoidal D, m, s, nativeFlatLocalization D, b⟩

set_option backward.isDefEq.respectTransparency false in
private theorem nativeTensorComparison_μ (N : NativeTensor M) :
    letI := M.nativeSymmetric
    letI := M.nativeHomotopyMonoidal
    letI := M.nativeHomotopySymmetric
    letI := M.nativeQuotientBraided
    letI := N.flatMonoidal
    letI := N.monoidal
    letI := N.symmetric
    letI := N.braided
    letI := flatComplexes_monoidal (diagonalAdequacy A)
    letI := flatQBraided A
    ∀ (P Q : (flatComplexes.{a,a} A).FullSubcategory),
      (N.tensorComparison P.obj Q.obj P.property Q.property).hom = μ (flatQ.{a,a} A) P Q := by
  intros
  rw [flatQ_μ]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem nativeUnitComparison_ε (N : NativeTensor M) :
    letI := M.nativeSymmetric
    letI := M.nativeHomotopyMonoidal
    letI := M.nativeHomotopySymmetric
    letI := M.nativeQuotientBraided
    letI := N.flatMonoidal
    letI := N.monoidal
    letI := N.symmetric
    letI := N.braided
    letI := flatComplexes_monoidal (diagonalAdequacy A)
    letI := flatQBraided A
    N.unitComparison.hom = ε (flatQ.{a,a} A) := by
  rw [flatQ_ε]
  rfl

private def ringLift : Lift (complexFunctorValue e) :=
  ⟨derivedFunctorValue e, NatIso.ofComponents (fun P => (derivedFactorsValue e).app P.obj)
    (fun k => (derivedFactorsValue e).hom.naturality k.hom)⟩

set_option backward.isDefEq.respectTransparency false in
private def makeRingTensor (D : Descent M) : RingTensor D := by
  let N := makeNativeTensor D
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  letI := D.flatMonoidal
  letI := D.monoidal
  letI := D.symmetric
  letI := D.braided
  letI := flatComplexes_monoidal M
  letI := flatQBraided R
  haveI := D.localization
  haveI := flatQ_isLocalization M
  letI := M.nativeSymmetric
  letI := M.nativeHomotopyMonoidal
  letI := M.nativeHomotopySymmetric
  letI := M.nativeQuotientBraided
  letI := N.flatMonoidal
  letI := N.monoidal
  letI := N.symmetric
  letI := N.braided
  letI := flatComplexes_monoidal (diagonalAdequacy A)
  letI := flatQBraided A
  letI := M.chainTransport
  let L := ringLift (e := e)
  let H := complexFunctorValue e
  let stable (P : compValue.{a} R) := (M.kFlat P).2
  let G := flatMap H stable
  letI := derivedBraided L stable
  refine { toNativeTensor := N, transport := derivedBraided L stable, tensor_on_models := ?_, unit_on_model := ?_ }
  · intro P Q hP hQ
    let X : (flatComplexes.{u,a} R).FullSubcategory := ⟨P, hP⟩
    let Y : (flatComplexes.{u,a} R).FullSubcategory := ⟨Q, hQ⟩
    let j := M.tensorModel P Q
    have hm := derivedBraided_μ L stable X Y
    have hn := (derivedFactorsValue e).hom.naturality j.inv
    change L.derived.map ((qValue R).map j.inv) ≫ (derivedFactorsValue e).hom.app
        (CochainTensor.tensor P Q) =
      (derivedFactorsValue e).hom.app (P ⊗ Q) ≫ (qValue A).map (H.map j.inv) at hn
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.Monoidal.μIso_hom, Functor.mapIso_hom, Iso.symm_hom,
      tensorIso_hom]
    rw [flatComparison_μ D X Y]
    erw [nativeTensorComparison_μ N (G.obj X) (G.obj Y)]
    simp only [Functor.map_comp, Category.assoc]
    erw [hn]
    exact (reassoc_of% hm) ((qValue A).map (H.map j.inv))
  · have hm := derivedBraided_ε L stable
    have hn := (derivedFactorsValue e).hom.naturality M.unitModel.inv
    change L.derived.map ((qValue R).map M.unitModel.inv) ≫ (derivedFactorsValue e).hom.app
        (representedUnit e) =
      (derivedFactorsValue e).hom.app (𝟙_ (compValue.{a} R)) ≫
        (qValue A).map (H.map M.unitModel.inv) at hn
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.Monoidal.εIso_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [unitComparison_ε D, nativeUnitComparison_ε N]
    simp only [Functor.map_comp, Category.assoc]
    erw [hn]
    exact (reassoc_of% hm) ((qValue A).map (H.map M.unitModel.inv))

theorem ringTensor : RingTensorExists.{u,a} := by
  intro R A _ _ e M D
  exact ⟨makeRingTensor D⟩

end RingTensorTransport


section DiagonalChange

open Specs.DerivedFormalization.CochainRingTransport (conjugateValue complexEquivalenceValue
  complexFunctorValue derivedFunctorValue derivedFactorsValue)
open Specs.DerivedFormalization.ScalarExtensionTransport (MonoidalChange DiagonalComparison
  ModelStability diagonalExtension diagonalAdjunction)
open Functor.LaxMonoidal
open Functor.Monoidal (εIso μIso)
attribute [local instance] CochainTensorMonoidal.cochainMonoidalValue

variable {R : Type u} {S : Type w} {A B : Type a} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B} {f : R →+* S}
  {MR : AdequateModel e} {MS : AdequateModel d}
  {DR : Descent MR} {DS : Descent MS}
  {F : MonoidalChange e d f MR MS}

private theorem diagonalExtension_flat (P : compValue.{a} A) (hP : isKFlat P) :
    isKFlat ((diagonalExtension e d f).obj P) :=
  (DerivedFormalization.CochainTensor.diagonalKFlat _).2
    (DerivedFormalization.isKFlat_extendScalars
      (conjugateValue e d f) P ((DerivedFormalization.CochainTensor.diagonalKFlat P).1 hP))

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
private theorem diagonalExtension_quasiIso (D : DiagonalComparison e d f MR MS F)
    (source : Model MR) (stability : ModelStability d f)
    {P Q : compValue.{a} A} (hP : isKFlat P) (hQ : isKFlat Q) (k : P ⟶ Q)
    (hk : QuasiIso k) : QuasiIso ((diagonalExtension e d f).map k) := by
  let E := complexEquivalenceValue e
  let T := diagonalExtension e d f
  let P' := E.inverse.obj P
  let Q' := E.inverse.obj Q
  let l := E.inverse.map k
  have flat (X : compValue.{a} A) (hX : isKFlat X) : isKFlat (E.inverse.obj X) :=
    (MR.kFlat (E.inverse.obj X)).1
      (flat_of_homotopy_iso (diagonalAdequacy A)
        ((quotientValue A).mapIso (E.counitIso.app X).symm) hX)
  have hn : (complexFunctorValue e).map l ≫ (E.counitIso.app Q).hom =
      (E.counitIso.app P).hom ≫ k := E.counitIso.hom.naturality k
  have hl : QuasiIso l :=
    (DerivedFormalization.CochainRingTransport.complexProperties e P' Q' l).2.1.mp
      ((quasiIso_of_iso_square hn).2 hk)
  have hL := extension_quasiIso MS source stability (flat P hP) (flat Q hQ) l hl
  have hL' := (DerivedFormalization.CochainRingTransport.complexProperties d _ _ _).2.1.mpr hL
  have ht : (complexFunctorValue d).map ((extension d f).map l) ≫ (D.comparison.app Q').hom =
      (D.comparison.app P').hom ≫ T.map ((complexFunctorValue e).map l) :=
    D.comparison.hom.naturality l
  have hT : QuasiIso (T.map ((complexFunctorValue e).map l)) :=
    (quasiIso_of_iso_square ht).1 hL'
  have hs : T.map ((complexFunctorValue e).map l) ≫ (T.mapIso (E.counitIso.app Q)).hom =
      (T.mapIso (E.counitIso.app P)).hom ≫ T.map k := by
    simp only [Functor.mapIso_hom, ← T.map_comp]
    exact T.congr_map (E.counitIso.hom.naturality k)
  exact (quasiIso_of_iso_square hs).1 hT

set_option backward.isDefEq.respectTransparency false in
private def makeNativeAdjoint (N : NativeTensor MR) (D : DiagonalComparison e d f MR MS F)
    (source : Model MR) (stability : ModelStability d f) :
    NativeExtension e d f := by
  let f' := conjugateValue e d f
  let T := ModuleCat.extendScalars.{a,a,a} f'
  haveI : T.Additive := (ModuleCat.extendRestrictScalarsAdj.{a} f').left_adjoint_additive
  haveI := N.localization
  haveI := flatQ_isLocalization (diagonalAdequacy A)
  let L := liftToDerived (diagonalExtension e d f)
    (fun hP hQ => diagonalExtension_quasiIso D source stability hP hQ)
  exact makeAdjointModel (diagonalAdequacy A) (E := T) (diagonalAdjunction e d f) L
    (diagonalExtension_flat (e := e) (d := d) (f := f))
    (fun P hP => DerivedFormalization.isKProjective_extendScalars f' P hP)

end DiagonalChange


section MonoidalSquares

open Functor.LaxMonoidal

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]

set_option backward.isDefEq.respectTransparency false in
/-- A monoidal square can be checked after precomposition along an essentially
surjective strong monoidal functor. -/
private theorem monoidal_of_whiskerLeft (J : C ⥤ D) [J.EssSurj] [J.Monoidal]
    {F G : D ⥤ E} [F.LaxMonoidal] [G.LaxMonoidal] (τ : F ⟶ G)
    (h : (J.whiskerLeft τ).IsMonoidal) : τ.IsMonoidal := by
  letI := h
  constructor
  · apply (cancel_mono (G.map (ε J))).mp
    have hε := NatTrans.IsMonoidal.unit (τ := J.whiskerLeft τ)
    simp only [comp_ε, Functor.whiskerLeft_app, Category.assoc] at hε
    rw [Category.assoc, ← τ.naturality (ε J), ← Category.assoc]
    simpa only [Category.assoc] using hε
  · intro X Y
    have ht (P Q : C) : μ F (J.obj P) (J.obj Q) ≫ τ.app (J.obj P ⊗ J.obj Q) =
        (τ.app (J.obj P) ⊗ₘ τ.app (J.obj Q)) ≫ μ G (J.obj P) (J.obj Q) := by
      apply (cancel_mono (G.map (μ J P Q))).mp
      have hn := NatTrans.IsMonoidal.tensor (τ := J.whiskerLeft τ) P Q
      simp only [comp_μ, Functor.whiskerLeft_app, Category.assoc] at hn
      rw [Category.assoc, ← τ.naturality (μ J P Q), ← Category.assoc, Category.assoc]
      simpa only [Category.assoc] using hn
    let i := J.objObjPreimageIso X
    let j := J.objObjPreimageIso Y
    apply (cancel_epi (tensorIso (F.mapIso i) (F.mapIso j)).hom).mp
    change (F.map i.hom ⊗ₘ F.map j.hom) ≫ (μ F X Y ≫ τ.app (X ⊗ Y)) =
      (F.map i.hom ⊗ₘ F.map j.hom) ≫ ((τ.app X ⊗ₘ τ.app Y) ≫ μ G X Y)
    rw [μ_natural_assoc, τ.naturality, reassoc_of% ht, ← μ_natural G i.hom j.hom]
    let a := τ.app (J.obj (J.objPreimage X))
    let b := τ.app (J.obj (J.objPreimage Y))
    let c := τ.app X
    let d := τ.app Y
    let m := μ G X Y
    have heq : (a ⊗ₘ b) ≫ (G.map i.hom ⊗ₘ G.map j.hom) =
        (F.map i.hom ⊗ₘ F.map j.hom) ≫ (c ⊗ₘ d) := by
      calc
        _ = (a ≫ G.map i.hom) ⊗ₘ (b ≫ G.map j.hom) :=
          tensorHom_comp_tensorHom _ _ _ _
        _ = (F.map i.hom ≫ c) ⊗ₘ (F.map j.hom ≫ d) := by
          exact congrArg₂ (fun f g => f ⊗ₘ g) (τ.naturality i.hom).symm (τ.naturality j.hom).symm
        _ = _ := (tensorHom_comp_tensorHom _ _ _ _).symm
    change (a ⊗ₘ b) ≫ (G.map i.hom ⊗ₘ G.map j.hom) ≫ m =
      (F.map i.hom ⊗ₘ F.map j.hom) ≫ (c ⊗ₘ d) ≫ m
    simpa only [Category.assoc] using congrArg (fun k => k ≫ m) heq

variable {C' D' : Type*} [Category* C'] [Category* D'] [MonoidalCategory C'] [MonoidalCategory D']
  [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]
  [BraidedCategory C'] [BraidedCategory D']

private abbrev restrictFunctor {C D : Type*} [Category* C] [Category* D]
    {P : ObjectProperty C} {Q : ObjectProperty D} (F : C ⥤ D)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj)) :=
  Q.lift (P.ι ⋙ F) hF

/-- Restrict a square of ordinary functors to full subcategories stable under its four sides. -/
private def restrictSquare
    {P : ObjectProperty C} {Q : ObjectProperty D} {Q' : ObjectProperty C'} {U : ObjectProperty E}
    {F : C ⥤ D} {G : D ⥤ E} {F' : C ⥤ C'} {G' : C' ⥤ E}
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ X : Q.FullSubcategory, U (G.obj X.obj))
    (hF' : ∀ X : P.FullSubcategory, Q' (F'.obj X.obj))
    (hG' : ∀ X : Q'.FullSubcategory, U (G'.obj X.obj))
    (θ : F ⋙ G ≅ F' ⋙ G') :
    restrictFunctor F hF ⋙ restrictFunctor G hG ≅ restrictFunctor F' hF' ⋙ restrictFunctor G' hG' :=
  NatIso.ofComponents (fun X => U.isoMk (θ.app X.obj))
    (fun f => U.hom_ext (θ.hom.naturality f.hom))

set_option backward.isDefEq.respectTransparency false in
private theorem restrictSquare_monoidal
    {P : ObjectProperty C} {Q : ObjectProperty D} {Q' : ObjectProperty C'} {U : ObjectProperty E}
    [P.IsMonoidal] [Q.IsMonoidal] [Q'.IsMonoidal] [U.IsMonoidal]
    {F : C ⥤ D} {G : D ⥤ E} {F' : C ⥤ C'} {G' : C' ⥤ E}
    [F.Braided] [G.Braided] [F'.Braided] [G'.Braided]
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ X : Q.FullSubcategory, U (G.obj X.obj))
    (hF' : ∀ X : P.FullSubcategory, Q' (F'.obj X.obj))
    (hG' : ∀ X : Q'.FullSubcategory, U (G'.obj X.obj))
    (θ : F ⋙ G ≅ F' ⋙ G') [θ.hom.IsMonoidal] :
    letI := braidedRestriction P Q F hF
    letI := braidedRestriction Q U G hG
    letI := braidedRestriction P Q' F' hF'
    letI := braidedRestriction Q' U G' hG'
    (restrictSquare hF hG hF' hG' θ).hom.IsMonoidal := by
  letI := braidedRestriction P Q F hF
  letI := braidedRestriction Q U G hG
  letI := braidedRestriction P Q' F' hF'
  letI := braidedRestriction Q' U G' hG'
  change (restrictSquare hF hG hF' hG' θ).hom.IsMonoidal
  refine ⟨?_, fun X Y => ?_⟩
  · apply U.hom_ext
    simp only [comp_ε, ObjectProperty.FullSubcategory.comp_hom]
    change ((ε (restrictFunctor G hG)).hom ≫ G.map (ε (restrictFunctor F hF)).hom) ≫ _ =
      (ε (restrictFunctor G' hG')).hom ≫ G'.map (ε (restrictFunctor F' hF')).hom
    erw [braidedRestriction_ε Q U G hG, braidedRestriction_ε P Q F hF,
      braidedRestriction_ε Q' U G' hG', braidedRestriction_ε P Q' F' hF']
    exact NatTrans.IsMonoidal.unit (τ := θ.hom)
  · apply U.hom_ext
    simp only [comp_μ, ObjectProperty.FullSubcategory.comp_hom]
    change ((μ (restrictFunctor G hG) _ _).hom ≫ G.map (μ (restrictFunctor F hF) X Y).hom) ≫ _ =
      _ ≫ (μ (restrictFunctor G' hG') _ _).hom ≫ G'.map (μ (restrictFunctor F' hF') X Y).hom
    rw [braidedRestriction_μ Q U G hG, braidedRestriction_μ P Q F hF]
    erw [braidedRestriction_μ Q' U G' hG', braidedRestriction_μ P Q' F' hF']
    exact NatTrans.IsMonoidal.tensor (τ := θ.hom) X.obj Y.obj

end MonoidalSquares

section ComparingLifts

variable {R : Type u} {S : Type w} {T : Type z} [CommRing R] [CommRing S] [CommRing T]
  {F : compValue.{a} R ⥤ compValue.{a} S} {G : compValue.{a} S ⥤ compValue.{a} T}

private def compLiftFactors (L : Lift F) (K : Lift G)
    (hF : ∀ P, isKFlat P → isKFlat (F.obj P)) (hG : ∀ P, isKFlat P → isKFlat (G.obj P)) :
    flatQ.{u,a} R ⋙ (L.derived ⋙ K.derived) ≅ flatMap F hF ⋙ flatMap G hG ⋙ flatQ.{z,a} T :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (liftFactors L hF) K.derived ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (flatMap F hF) (liftFactors K hG)

private theorem compLiftFactors_app (L : Lift F) (K : Lift G)
    (hF : ∀ P, isKFlat P → isKFlat (F.obj P)) (hG : ∀ P, isKFlat P → isKFlat (G.obj P))
    (P : compValue.{a} R) (hP : isKFlat P) :
    (compLiftFactors L K hF hG).app ⟨P,hP⟩ =
      K.derived.mapIso (L.model P hP) ≪≫ K.model (F.obj P) (hF P hP) := by
  apply Iso.ext
  simp [compLiftFactors, liftFactors, Lift.model]
  rfl

end ComparingLifts


section DescendedComparisons

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  (J : C ⥤ D) (W : MorphismProperty C) [J.IsLocalization W]
  {F G : D ⥤ E} {F₀ G₀ : C ⥤ E} (i : J ⋙ F ≅ F₀) (j : J ⋙ G ≅ G₀) (θ : F₀ ≅ G₀)

private def descendIso : F ≅ G :=
  letI : Localization.Lifting J W F₀ F := ⟨i⟩
  letI : Localization.Lifting J W G₀ G := ⟨j⟩
  Localization.liftNatIso J W F₀ G₀ F G θ

private theorem descendIso_app_hom (X : C) :
    (descendIso J W i j θ).hom.app (J.obj X) = i.hom.app X ≫ θ.hom.app X ≫ j.inv.app X := by
  unfold descendIso
  rw [Localization.liftNatIso_hom, Localization.liftNatTrans_app]
  rfl

private theorem descendIso_app (X : C) :
    (descendIso J W i j θ).app (J.obj X) ≪≫ j.app X = i.app X ≪≫ θ.app X := by
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.app_hom, descendIso_app_hom, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]

private theorem descendIso_monoidal [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [J.Monoidal] [F.LaxMonoidal] [G.LaxMonoidal] [F₀.LaxMonoidal] [G₀.LaxMonoidal]
    [i.hom.IsMonoidal] [j.hom.IsMonoidal] [θ.hom.IsMonoidal] :
    (descendIso J W i j θ).hom.IsMonoidal := by
  haveI := Localization.essSurj (L := J) W
  apply monoidal_of_whiskerLeft J
  have h : J.whiskerLeft (descendIso J W i j θ).hom = i.hom ≫ θ.hom ≫ j.inv := by
    ext X
    exact descendIso_app_hom J W i j θ X
  rw [h]
  infer_instance

end DescendedComparisons

section DerivedSquares

open Specs.DerivedFormalization.CochainRingTransport (complexFunctorValue derivedFunctorValue
  derivedFactorsValue)
open Specs.DerivedFormalization.ScalarExtensionTransport (MonoidalChange DiagonalComparison
  diagonalExtension)

variable {R : Type u} {S : Type w} {A B : Type a} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B} {f : R →+* S}
  {MR : AdequateModel e} {MS : AdequateModel d}
  {F : MonoidalChange e d f MR MS}
  (D : DiagonalComparison e d f MR MS F) (L : Extension d f) (N : NativeExtension e d f)


private def diagonalSquareOnFlat :
    flatMap (extension d f) L.preservesFlat ⋙
        flatMap (complexFunctorValue d) (fun P => (MS.kFlat P).2) ⋙ flatQ.{a,a} B ≅
      flatMap (complexFunctorValue e) (fun P => (MR.kFlat P).2) ⋙
        flatMap (diagonalExtension e d f) N.preservesFlat ⋙ flatQ.{a,a} B :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (restrictSquare
        (fun P => L.preservesFlat P.obj P.property)
        (fun P => (MS.kFlat P.obj).2 P.property)
        (fun P => (MR.kFlat P.obj).2 P.property)
        (fun P => N.preservesFlat P.obj P.property) D.comparison) _ ≪≫
    Functor.associator _ _ _

private def diagonalDerivedComparison
    [(flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)] :
    L.derived ⋙ derivedFunctorValue d ≅ derivedFunctorValue e ⋙ N.derived :=
  descendIso (flatQ.{u,a} R) (flatChainQuasiIso.{u,a} R)
    (compLiftFactors L.toLift (ringLift (e := d)) L.preservesFlat (fun P => (MS.kFlat P).2))
    (compLiftFactors (ringLift (e := e)) N.toLift (fun P => (MR.kFlat P).2) N.preservesFlat)
    (diagonalSquareOnFlat D L N)

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalDerivedComparison_app
    [(flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)]
    (P : compValue.{a} R) (hP : isKFlat P) :
    (diagonalDerivedComparison D L N).app ((qValue R).obj P) ≪≫
        N.derived.mapIso ((derivedFactorsValue e).app P) ≪≫
        N.toLift.model ((complexFunctorValue e).obj P) ((MR.kFlat P).2 hP) =
      (derivedFunctorValue d).mapIso (L.toLift.model P hP) ≪≫
        (derivedFactorsValue d).app ((extension d f).obj P) ≪≫
        (qValue B).mapIso (D.comparison.app P) := by
  have h := descendIso_app (flatQ.{u,a} R) (flatChainQuasiIso.{u,a} R)
    (compLiftFactors L.toLift (ringLift (e := d)) L.preservesFlat (fun P => (MS.kFlat P).2))
    (compLiftFactors (ringLift (e := e)) N.toLift (fun P => (MR.kFlat P).2) N.preservesFlat)
    (diagonalSquareOnFlat D L N) ⟨P,hP⟩
  have hθ : (diagonalSquareOnFlat D L N).app ⟨P,hP⟩ =
      (qValue B).mapIso (D.comparison.app P) := by
    apply Iso.ext
    change (𝟙 _ ≫ (qValue B).map (D.comparison.hom.app P)) ≫ 𝟙 _ = _
    rw [Category.id_comp, Category.comp_id]
    rfl
  rw [compLiftFactors_app, compLiftFactors_app, hθ] at h
  exact h.trans (Iso.trans_assoc _ _ _)

end DerivedSquares


section ModelUnits

open Specs.DerivedFormalization.DerivedRestriction (restrictScalarsComplexValue
  derivedRestrictScalarsValue derivedRestrictScalarsFactorsValue)
open Specs.DerivedFormalization.CochainRingTransport (adjunctionCompatible)

variable {R : Type u} {S : Type w} {A : Type a} [CommRing R] [CommRing S] [CommRing A]
  {e : R ≃+* A} {f : R →+* S} {F : compValue.{a} R ⥤ compValue.{a} S}
  {adj₀ : F ⊣ restrictScalarsComplexValue.{a} f} (L : AdjointModel f F adj₀)

set_option backward.isDefEq.respectTransparency false in
private theorem unit_on_projective_model (P : compValue.{a} R) (hP : P.IsKProjective) :
    L.adj.unit.app ((qValue R).obj P) ≫
        (derivedRestrictScalarsValue f).map (L.toLift.model P (L.projectiveFlat P hP)).hom =
      (qValue R).map (adj₀.unit.app P) ≫ (derivedRestrictScalarsFactorsValue f).inv.app (F.obj P) := by
  have h := L.adj_on_model P (F.obj P) hP (𝟙 _)
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, (qValue S).map_id,
    Category.comp_id, (restrictScalarsComplexValue f).map_id] at h
  erw [Category.comp_id] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
private theorem unit_on_flat_model (_M : AdequateModel e)
    [(flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)]
    (P : compValue.{a} R) (hP : isKFlat P) :
    L.adj.unit.app ((qValue R).obj P) ≫
        (derivedRestrictScalarsValue f).map (L.toLift.model P hP).hom =
      (qValue R).map (adj₀.unit.app P) ≫ (derivedRestrictScalarsFactorsValue f).inv.app (F.obj P) := by
  let U := derivedRestrictScalarsValue.{a} f
  have hη : L.adj.unit = localizedUnit adj₀ L.toLift := by
    ext X
    obtain ⟨P', hP', ⟨i⟩⟩ := projective_presentations e X
    apply (cancel_epi i.hom).mp
    have hL := L.adj.unit.naturality i.hom
    have h := (localizedUnit adj₀ L.toLift).naturality i.hom
    change i.hom ≫ L.adj.unit.app X = L.adj.unit.app ((qValue R).obj P') ≫
      U.map (L.derived.map i.hom) at hL
    change i.hom ≫ (localizedUnit adj₀ L.toLift).app X =
      (localizedUnit adj₀ L.toLift).app ((qValue R).obj P') ≫ U.map (L.derived.map i.hom) at h
    rw [hL, h]
    congr 1
    apply (cancel_mono (U.map (L.toLift.model P' (L.projectiveFlat P' hP')).hom)).mp
    rw [unit_on_projective_model L P' hP',
      localizedUnit_app adj₀ L.toLift P' (L.projectiveFlat P' hP')]
    simp only [U, Category.assoc, Iso.inv_hom_id_map]
    erw [Category.comp_id]
  rw [hη, localizedUnit_app adj₀ L.toLift P hP]
  simp only [Category.assoc, Iso.inv_hom_id_map]
  erw [Category.comp_id]

private theorem mate_of_unit
    {C D E K : Type*} [Category* C] [Category* D] [Category* E] [Category* K]
    {G : C ⥤ E} {H : D ⥤ K} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ K} {R₂ : K ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (h : ∀ X : C, G.map (adj₁.unit.app X) ≫ β.app (L₁.obj X) =
      adj₂.unit.app (G.obj X) ≫ R₂.map (α.app X)) :
    mateEquiv adj₁ adj₂ α = β := by
  apply (mateEquiv adj₁ adj₂).symm.injective
  rw [Equiv.symm_apply_apply]
  ext X
  apply (adj₂.homEquiv (G.obj X) (H.obj (L₁.obj X))).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact (h X).symm.trans (unit_mateEquiv_symm adj₁ adj₂ β X)

private theorem compatible_of_unit
    {C D E K : Type*} [Category* C] [Category* D] [Category* E] [Category* K]
    {G : C ⥤ E} {H : D ⥤ K} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ K} {R₂ : K ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : G ⋙ L₂ ⟶ L₁ ⋙ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂)
    (h : ∀ X : C, G.map (adj₁.unit.app X) ≫ β.app (L₁.obj X) =
      adj₂.unit.app (G.obj X) ≫ R₂.map (α.app X)) :
    adjunctionCompatible adj₁ adj₂ α β := by
  refine ⟨h, ?_⟩
  intro Y
  rw [← mate_of_unit adj₁ adj₂ α β h]
  exact mateEquiv_counit adj₁ adj₂ α Y

end ModelUnits


section DiagonalAdjunctionCompatibility

open Specs.DerivedFormalization.CochainRingTransport (conjugateValue complexFunctorValue
  derivedFunctorValue derivedFactorsValue complexRestrictionIsoValue derivedRestrictionIsoValue
  adjunctionCompatible)
open Specs.DerivedFormalization.ScalarExtensionTransport (MonoidalChange DiagonalComparison
  diagonalExtension extensionAdjunction diagonalAdjunction)
open Specs.DerivedFormalization.DerivedRestriction (restrictScalarsComplexValue
  derivedRestrictScalarsValue derivedRestrictScalarsFactorsValue)

variable {R : Type u} {S : Type w} {A B : Type a} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B} {f : R →+* S}
  {MR : AdequateModel e} {MS : AdequateModel d}
  {F : MonoidalChange e d f MR MS}
  (D : DiagonalComparison e d f MR MS F) (L : Extension d f) (N : NativeExtension e d f)
  [(flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)]
  [(flatQ.{a,a} A).IsLocalization (flatChainQuasiIso.{a,a} A)]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
private theorem diagonal_unit_on_flat (P : compValue.{a} R) (hP : isKFlat P) :
    (derivedFunctorValue e).map (L.adj.unit.app ((qValue R).obj P)) ≫
        (derivedRestrictionIsoValue e d f).hom.app (L.derived.obj ((qValue R).obj P)) =
      N.adj.unit.app ((derivedFunctorValue e).obj ((qValue R).obj P)) ≫
        (derivedRestrictScalarsValue (conjugateValue e d f)).map
          ((diagonalDerivedComparison D L N).inv.app ((qValue R).obj P)) := by
  let Q := qValue R
  let QA := qValue A
  let QB := qValue B
  let H := complexFunctorValue e
  let K := complexFunctorValue d
  let E := extension d f
  let V := restrictScalarsComplexValue.{a} (conjugateValue e d f)
  let DR := derivedFunctorValue e
  let DS := derivedFunctorValue d
  let U' := derivedRestrictScalarsValue.{a} f
  let V' := derivedRestrictScalarsValue.{a} (conjugateValue e d f)
  let X := Q.obj P
  let Y := E.obj P
  let Z := (diagonalExtension e d f).obj (H.obj P)
  let i := (derivedFactorsValue e).app P
  let j := (derivedFactorsValue d).app Y
  let c := D.comparison.app P
  let l := L.toLift.model P hP
  let n := N.toLift.model (H.obj P) ((MR.kFlat P).2 hP)
  let t := (diagonalDerivedComparison D L N).app X
  let b := (derivedRestrictScalarsFactorsValue (conjugateValue e d f)).app (K.obj Y)
  let b' := (derivedRestrictScalarsFactorsValue (conjugateValue e d f)).app Z
  let r := (complexRestrictionIsoValue e d f).app Y
  let β := (derivedRestrictionIsoValue e d f).hom
  let u := (extensionAdjunction d f).unit.app P
  let v := (diagonalAdjunction e d f).unit.app (H.obj P)
  have hstar : t.inv ≫ DS.map l.hom ≫ j.hom =
      N.derived.map i.hom ≫ n.hom ≫ QB.map c.inv := by
    have ht := congrArg Iso.hom (diagonalDerivedComparison_app D L N P hP)
    change (t.hom ≫ N.derived.map i.hom ≫ n.hom) =
      DS.map l.hom ≫ j.hom ≫ QB.map c.hom at ht
    apply (cancel_epi t.hom).mp
    apply (cancel_mono (QB.map c.hom)).mp
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_map]
    erw [Category.comp_id]
    exact ht.symm
  apply (cancel_mono (V'.map (DS.map l.hom ≫ j.hom) ≫ b.hom)).mp
  have hβ := β.naturality l.hom
  change DR.map (U'.map l.hom) ≫ β.app ((qValue S).obj Y) =
    β.app (L.derived.obj X) ≫ V'.map (DS.map l.hom) at hβ
  have hr := DerivedFormalization.CochainRingTransport.derivedRestrictionComponents e d f Y
  have hl := unit_on_flat_model L MR P hP
  have hn := unit_on_flat_model N (diagonalAdequacy A) (H.obj P) ((MR.kFlat P).2 hP)
  have hc := (derivedRestrictScalarsFactorsValue (conjugateValue e d f)).hom.naturality c.inv
  change V'.map (QB.map c.inv) ≫ b.hom = b'.hom ≫ QA.map (V.map c.inv) at hc
  have hu := (derivedFactorsValue e).hom.naturality u
  change DR.map (Q.map u) ≫ (derivedFactorsValue e).hom.app
    ((restrictScalarsComplexValue f).obj Y) = i.hom ≫ QA.map (H.map u) at hu
  have hi := N.adj.unit.naturality i.hom
  change i.hom ≫ N.adj.unit.app (QA.obj (H.obj P)) =
    N.adj.unit.app (DR.obj X) ≫ V'.map (N.derived.map i.hom) at hi
  change (DR.map (L.adj.unit.app X) ≫ β.app (L.derived.obj X)) ≫
      (V'.map (DS.map l.hom ≫ j.hom) ≫ b.hom) =
    (N.adj.unit.app (DR.obj X) ≫ V'.map t.inv) ≫
      (V'.map (DS.map l.hom ≫ j.hom) ≫ b.hom)
  have hleft :
      (DR.map (L.adj.unit.app X) ≫ β.app (L.derived.obj X)) ≫
        (V'.map (DS.map l.hom ≫ j.hom) ≫ b.hom) =
      i.hom ≫ QA.map (H.map u ≫ r.hom) := by
    rw [V'.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% hβ, ← DR.map_comp_assoc, hl, DR.map_comp]
    erw [hr]
    let w := (derivedRestrictScalarsFactorsValue f).app Y
    change (DR.map (Q.map u) ≫ DR.map w.inv) ≫ DR.map w.hom ≫
      (derivedFactorsValue e).hom.app ((restrictScalarsComplexValue f).obj Y) ≫ QA.map r.hom = _
    rw [Category.assoc, Iso.inv_hom_id_map_assoc, reassoc_of% hu, ← QA.map_comp]
  have hright :
      (N.adj.unit.app (DR.obj X) ≫ V'.map t.inv) ≫
        (V'.map (DS.map l.hom ≫ j.hom) ≫ b.hom) =
      i.hom ≫ QA.map (v ≫ V.map c.inv) := by
    simp only [Category.assoc]
    rw [← V'.map_comp_assoc, hstar, V'.map_comp, V'.map_comp]
    simp only [Category.assoc]
    rw [← reassoc_of% hi, hc]
    erw [reassoc_of% hn]
    change i.hom ≫ QA.map v ≫ b'.inv ≫ b'.hom ≫ QA.map (V.map c.inv) = _
    rw [Iso.inv_hom_id_assoc, ← QA.map_comp]
  have h := D.comparison_adjunction.1 P
  change H.map u ≫ r.hom = v ≫ V.map c.inv at h
  rw [hleft, hright, h]

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalDerived_isMate :
    adjunctionCompatible L.adj N.adj (diagonalDerivedComparison D L N).inv
      (derivedRestrictionIsoValue e d f).hom := by
  apply compatible_of_unit
  let H := derivedFunctorValue e
  let K := derivedFunctorValue d
  let V := derivedRestrictScalarsValue.{a} (conjugateValue e d f)
  let β := (derivedRestrictionIsoValue e d f).hom
  let θ := (diagonalDerivedComparison D L N).inv
  let p : H ⟶ (L.derived ⋙ K) ⋙ V :=
    H.leftUnitor.inv ≫ Functor.whiskerRight L.adj.unit H ≫
       (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft L.derived β ≫
       (Functor.associator _ _ _).inv
  let q : H ⟶ (L.derived ⋙ K) ⋙ V :=
    H.rightUnitor.inv ≫ Functor.whiskerLeft H N.adj.unit ≫
      (Functor.associator _ _ _).inv ≫ Functor.whiskerRight θ V
  have h : p = q := Localization.natTrans_ext (flatQ.{u,a} R) (flatChainQuasiIso.{u,a} R)
    (fun P => by simpa [p, q, H, K, V, β, θ] using diagonal_unit_on_flat D L N P.obj P.property)
  intro X
  simpa [p, q, H, K, V, β, θ] using NatTrans.congr_app h X

end DiagonalAdjunctionCompatibility


section TransportFactorsMonoidal

open Specs.DerivedFormalization.CochainRingTransport (complexFunctorValue derivedFunctorValue
  derivedFactorsValue)
open Specs.DerivedFormalization.CochainTensorTransport (representedUnit)
open Functor.LaxMonoidal
attribute [local instance] CochainTensorMonoidal.cochainMonoidalValue

variable {R : Type u} {A : Type a} [CommRing R] [CommRing A] {e : R ≃+* A}
  {M : AdequateModel e} {D : Descent M}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1200000 in
private theorem ringLift_monoidal (N : RingTensor D) :
    letI := M.chainMonoidal
    letI := M.chainSymmetric
    letI := M.homotopyMonoidal
    letI := M.homotopySymmetric
    letI := M.quotientBraided
    letI := D.flatMonoidal
    letI := D.monoidal
    letI := D.symmetric
    letI := D.braided
    letI := flatComplexes_monoidal M
    letI := flatQBraided R
    letI := M.nativeSymmetric
    letI := M.nativeHomotopyMonoidal
    letI := M.nativeHomotopySymmetric
    letI := M.nativeQuotientBraided
    letI := N.toNativeTensor.flatMonoidal
    letI := N.toNativeTensor.monoidal
    letI := N.toNativeTensor.symmetric
    letI := N.toNativeTensor.braided
    letI := flatComplexes_monoidal (diagonalAdequacy A)
    letI := flatQBraided A
    letI := M.chainTransport
    letI : (ringLift (e := e)).derived.Braided := N.transport
    letI := braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{a,a} A)
      (complexFunctorValue e) (fun X => (M.kFlat X.obj).2 X.property)
    (liftFactors (ringLift (e := e)) (fun P => (M.kFlat P).2)).hom.IsMonoidal := by
  letI := M.chainMonoidal
  letI := M.chainSymmetric
  letI := M.homotopyMonoidal
  letI := M.homotopySymmetric
  letI := M.quotientBraided
  letI := D.flatMonoidal
  letI := D.monoidal
  letI := D.symmetric
  letI := D.braided
  letI := flatComplexes_monoidal M
  letI := flatQBraided R
  letI := M.nativeSymmetric
  letI := M.nativeHomotopyMonoidal
  letI := M.nativeHomotopySymmetric
  letI := M.nativeQuotientBraided
  letI := N.toNativeTensor.flatMonoidal
  letI := N.toNativeTensor.monoidal
  letI := N.toNativeTensor.symmetric
  letI := N.toNativeTensor.braided
  letI := flatComplexes_monoidal (diagonalAdequacy A)
  letI := flatQBraided A
  letI := M.chainTransport
  letI : (ringLift (e := e)).derived.Braided := N.transport
  let H := complexFunctorValue e
  let E := derivedFunctorValue e
  letI : E.Braided := N.transport
  let stable (P : compValue.{a} R) := (M.kFlat P).2
  let G := flatMap H stable
  letI : G.Braided :=
    braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{a,a} A) H
      (fun X => stable X.obj X.property)
  change (liftFactors (ringLift (e := e)) stable).hom.IsMonoidal
  refine ⟨?_, fun X Y => ?_⟩
  · have h := congrArg Iso.hom N.unit_on_model
    simp only [Iso.trans_hom, Functor.Monoidal.εIso_hom, Functor.mapIso_hom, Iso.symm_hom] at h
    erw [unitComparison_ε D, nativeUnitComparison_ε N.toNativeTensor] at h
    simp only [Functor.map_comp, Category.assoc] at h ⊢
    rw [comp_ε, comp_ε]
    change (ε E ≫ E.map (ε (flatQ.{u,a} R))) ≫
      (derivedFactorsValue e).hom.app (𝟙_ (compValue.{a} R)) =
      ε (flatQ.{a,a} A) ≫ (qValue A).map (ε G).hom
    rw [braidedRestriction_ε (flatComplexes.{u,a} R) (flatComplexes.{a,a} A)]
    apply (cancel_mono ((qValue A).map (H.map M.unitModel.inv))).mp
    have hn := (derivedFactorsValue e).hom.naturality M.unitModel.inv
    simp only [Category.assoc]
    erw [← hn]
    exact h
  · have h := congrArg Iso.hom (N.tensor_on_models X.obj Y.obj X.property Y.property)
    have hR := flatComparison_μ D X Y
    have hA := nativeTensorComparison_μ N.toNativeTensor (G.obj X) (G.obj Y)
    simp only [Iso.trans_hom, Functor.Monoidal.μIso_hom, Functor.mapIso_hom, tensorIso_hom,
      Iso.symm_hom] at h
    erw [hR, hA] at h
    simp only [Functor.map_comp, Category.assoc] at h
    rw [comp_μ, comp_μ]
    change (μ E ((qValue R).obj X.obj) ((qValue R).obj Y.obj) ≫
        E.map (μ (flatQ.{u,a} R) X Y)) ≫ (derivedFactorsValue e).hom.app (X.obj ⊗ Y.obj) =
      (((derivedFactorsValue e).app X.obj).hom ⊗ₘ ((derivedFactorsValue e).app Y.obj).hom) ≫
        μ (flatQ.{a,a} A) (G.obj X) (G.obj Y) ≫ (qValue A).map (μ G X Y).hom
    rw [braidedRestriction_μ (flatComplexes.{u,a} R) (flatComplexes.{a,a} A)]
    let x := (M.tensorModel X.obj Y.obj).inv
    apply (cancel_mono ((qValue A).map (H.map x))).mp
    have hn := (derivedFactorsValue e).hom.naturality x
    simp only [Category.assoc]
    erw [← hn]
    exact h

end TransportFactorsMonoidal


section ConstructDiagonal

open Specs.DerivedFormalization.CochainRingTransport (complexFunctorValue)
open Specs.DerivedFormalization.ScalarExtensionTransport (MonoidalChange DiagonalComparison
  diagonalExtension)
open Functor.LaxMonoidal
attribute [local instance] CochainTensorMonoidal.cochainMonoidalValue

variable {R : Type u} {S : Type w} {T : Type z} [CommRing R] [CommRing S] [CommRing T]

set_option backward.isDefEq.respectTransparency false in
private theorem compLiftFactors_isMonoidal
    [MonoidalCategory (compValue.{a} R)] [(flatComplexes.{u,a} R).IsMonoidal]
    [MonoidalCategory (compValue.{a} S)] [(flatComplexes.{w,a} S).IsMonoidal]
    [MonoidalCategory (compValue.{a} T)] [(flatComplexes.{z,a} T).IsMonoidal]
    [MonoidalCategory (derivedValue.{a} R)] [(flatQ.{u,a} R).LaxMonoidal]
    [MonoidalCategory (derivedValue.{a} S)] [(flatQ.{w,a} S).LaxMonoidal]
    [MonoidalCategory (derivedValue.{a} T)] [(flatQ.{z,a} T).LaxMonoidal]
    {F : compValue.{a} R ⥤ compValue.{a} S} {G : compValue.{a} S ⥤ compValue.{a} T}
    (L : Lift F) (K : Lift G)
    (hF : ∀ P, isKFlat P → isKFlat (F.obj P)) (hG : ∀ P, isKFlat P → isKFlat (G.obj P))
    [L.derived.LaxMonoidal] [K.derived.LaxMonoidal]
    [(flatMap F hF).LaxMonoidal] [(flatMap G hG).LaxMonoidal]
    [(liftFactors L hF).hom.IsMonoidal] [(liftFactors K hG).hom.IsMonoidal] :
    (compLiftFactors L K hF hG).hom.IsMonoidal := by
  unfold compLiftFactors
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

variable {A B : Type a} [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B}
    {f : R →+* S} {MR : AdequateModel e} {MS : AdequateModel d}
    {DR : Descent MR} {DS : Descent MS} {F : MonoidalChange e d f MR MS}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2200000 in
private def makeDiagonalExtension (NR : RingTensor DR) (NS : RingTensor DS)
    (D : DiagonalComparison e d f MR MS F) (L : Extension d f) (N : NativeExtension e d f) :
    DiagonalExtension NR NS (makeMonoidalExtension DR DS F L) D := by
  letI := MR.chainMonoidal
  letI := MR.chainSymmetric
  letI := MR.homotopyMonoidal
  letI := MR.homotopySymmetric
  letI := MR.quotientBraided
  letI := DR.flatMonoidal
  letI := DR.monoidal
  letI := DR.symmetric
  letI := DR.braided
  letI := flatComplexes_monoidal MR
  letI := flatQBraided R
  haveI := DR.localization
  haveI := flatQ_isLocalization MR
  letI := MS.chainMonoidal
  letI := MS.chainSymmetric
  letI := MS.homotopyMonoidal
  letI := MS.homotopySymmetric
  letI := MS.quotientBraided
  letI := DS.flatMonoidal
  letI := DS.monoidal
  letI := DS.symmetric
  letI := DS.braided
  letI := flatComplexes_monoidal MS
  letI := flatQBraided S
  letI := MR.nativeSymmetric
  letI := MR.nativeHomotopyMonoidal
  letI := MR.nativeHomotopySymmetric
  letI := MR.nativeQuotientBraided
  letI := NR.toNativeTensor.flatMonoidal
  letI := NR.toNativeTensor.monoidal
  letI := NR.toNativeTensor.symmetric
  letI := NR.toNativeTensor.braided
  letI := flatComplexes_monoidal (diagonalAdequacy A)
  letI := flatQBraided A
  haveI := NR.toNativeTensor.localization
  haveI := flatQ_isLocalization (diagonalAdequacy A)
  letI := MS.nativeSymmetric
  letI := MS.nativeHomotopyMonoidal
  letI := MS.nativeHomotopySymmetric
  letI := MS.nativeQuotientBraided
  letI := NS.toNativeTensor.flatMonoidal
  letI := NS.toNativeTensor.monoidal
  letI := NS.toNativeTensor.symmetric
  letI := NS.toNativeTensor.braided
  letI := flatComplexes_monoidal (diagonalAdequacy B)
  letI := flatQBraided B
  letI := MR.chainTransport
  letI := MS.chainTransport
  letI := F.extensionBraided
  letI := D.nativeBraided
  letI : (ringLift (e := e)).derived.Braided := NR.transport
  letI : (ringLift (e := d)).derived.Braided := NS.transport
  letI : L.toLift.derived.Braided := derivedBraided L.toLift L.preservesFlat
  letI : N.toLift.derived.Braided := derivedBraided N.toLift N.preservesFlat
  refine { native := N
           braided := derivedBraided N.toLift N.preservesFlat
           comparison := diagonalDerivedComparison D L N
           adjunction := diagonalDerived_isMate D L N
           on_models := diagonalDerivedComparison_app D L N
           monoidal := ?_
           native_tensor_on_models := ?_
           native_unit_on_model := ?_ }
  · let hR (P : compValue.{a} R) := (MR.kFlat P).2
    let hS (P : compValue.{a} S) := (MS.kFlat P).2
    letI := braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{w,a} S) (extension d f)
      (fun P => L.preservesFlat P.obj P.property)
    letI := braidedRestriction (flatComplexes.{a,a} A) (flatComplexes.{a,a} B) (diagonalExtension e d f)
      (fun P => N.preservesFlat P.obj P.property)
    letI := braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{a,a} A) (complexFunctorValue e)
      (fun P => hR P.obj P.property)
    letI := braidedRestriction (flatComplexes.{w,a} S) (flatComplexes.{a,a} B) (complexFunctorValue d)
      (fun P => hS P.obj P.property)
    haveI := derivedBraided_factors L.toLift L.preservesFlat
    haveI := derivedBraided_factors N.toLift N.preservesFlat
    haveI := ringLift_monoidal NR
    haveI := ringLift_monoidal NS
    haveI := D.monoidal
    haveI := compLiftFactors_isMonoidal L.toLift (ringLift (e := d)) L.preservesFlat hS
    haveI := compLiftFactors_isMonoidal (ringLift (e := e)) N.toLift hR N.preservesFlat
    let h₁ (P : (flatComplexes.{u,a} R).FullSubcategory) := L.preservesFlat P.obj P.property
    let h₂ (P : (flatComplexes.{w,a} S).FullSubcategory) := hS P.obj P.property
    let h₃ (P : (flatComplexes.{u,a} R).FullSubcategory) := hR P.obj P.property
    let h₄ (P : (flatComplexes.{a,a} A).FullSubcategory) := N.preservesFlat P.obj P.property
    let τ := restrictSquare (P := flatComplexes.{u,a} R) (Q := flatComplexes.{w,a} S)
      (Q' := flatComplexes.{a,a} A) (U := flatComplexes.{a,a} B) h₁ h₂ h₃ h₄ D.comparison
    haveI hτ : τ.hom.IsMonoidal := restrictSquare_monoidal
      (P := flatComplexes.{u,a} R) (Q := flatComplexes.{w,a} S)
      (Q' := flatComplexes.{a,a} A) (U := flatComplexes.{a,a} B) h₁ h₂ h₃ h₄ D.comparison
    let i := Functor.associator (flatMap (extension d f) L.preservesFlat)
      (flatMap (complexFunctorValue d) hS) (flatQ.{a,a} B)
    let j := Functor.associator (flatMap (complexFunctorValue e) hR)
      (flatMap (diagonalExtension e d f) N.preservesFlat) (flatQ.{a,a} B)
    haveI hi : i.inv.IsMonoidal := by
      dsimp only [i]
      infer_instance
    haveI hj : j.hom.IsMonoidal := by
      dsimp only [j]
      infer_instance
    haveI hmid : (Functor.whiskerRight τ.hom (flatQ.{a,a} B)).IsMonoidal := by
      infer_instance
    haveI : (diagonalSquareOnFlat D L N).hom.IsMonoidal :=
      show (i.inv ≫ Functor.whiskerRight τ.hom (flatQ.{a,a} B) ≫ j.hom).IsMonoidal from
        inferInstance
    exact descendIso_monoidal (flatQ.{u,a} R) (flatChainQuasiIso.{u,a} R)
      (compLiftFactors L.toLift (ringLift (e := d)) L.preservesFlat hS)
      (compLiftFactors (ringLift (e := e)) N.toLift hR N.preservesFlat)
      (diagonalSquareOnFlat D L N)
  · intro P Q hP hQ hPQ
    let X : (flatComplexes.{a,a} A).FullSubcategory := ⟨P,hP⟩
    let Y : (flatComplexes.{a,a} A).FullSubcategory := ⟨Q,hQ⟩
    let G := flatMap (diagonalExtension e d f) N.preservesFlat
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.Monoidal.μIso_hom, Functor.mapIso_hom, tensorIso_hom]
    erw [nativeTensorComparison_μ NR.toNativeTensor X Y,
      nativeTensorComparison_μ NS.toNativeTensor (G.obj X) (G.obj Y)]
    exact derivedBraided_μ N.toLift N.preservesFlat X Y
  · intro h
    apply Iso.ext
    simp only [Iso.trans_hom, Functor.Monoidal.εIso_hom, Functor.mapIso_hom]
    erw [nativeUnitComparison_ε NR.toNativeTensor, nativeUnitComparison_ε NS.toNativeTensor]
    exact derivedBraided_ε N.toLift N.preservesFlat

theorem existsExtension : ExistsExtension.{u,w,a} := by
  intro R S A B _ _ _ _ e d f MR MS DR DS NR NS
  obtain ⟨source⟩ := DerivedFormalization.DerivedTensor.existsModel.{u,a} MR
  obtain ⟨stability⟩ := DerivedFormalization.ScalarExtensionTransport.modelStability d f
  obtain ⟨F, ⟨D⟩⟩ := DerivedFormalization.ScalarExtensionTransport.monoidalComparison e d f MR MS
  let L := adjointExtension MS DR source stability
  let N := makeNativeAdjoint NR.toNativeTensor D source stability
  exact ⟨F, D, L, makeMonoidalExtension DR DS F L, ⟨makeDiagonalExtension NR NS D L N⟩⟩

end ConstructDiagonal


section CoherentMates

open TwoSquare
open Specs.DerivedFormalization.CochainRingTransport (adjunctionCompatible compositionCoherent)

set_option backward.isDefEq.respectTransparency false in
private theorem conjugate_leftAdjointUniq_inv
    {C D : Type*} [Category* C] [Category* D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (r : R₁ ≅ R₂) :
    conjugateEquiv a₁ a₂ ((a₁.ofNatIsoRight r).leftAdjointUniq a₂).inv = r.hom := by
  let t := (a₁.ofNatIsoRight r).leftAdjointUniq a₂
  apply (conjugateEquiv a₁ a₂).symm.injective
  rw [Equiv.symm_apply_apply]
  ext X
  apply (a₂.homEquiv X (L₁.obj X)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← unit_conjugateEquiv_symm a₁ a₂]
  have h := Adjunction.unit_leftAdjointUniq_hom_app (a₁.ofNatIsoRight r) a₂ X
  change (a₁.unit.app X ≫ r.hom.app (L₁.obj X)) ≫ R₂.map (t.hom.app X) =
    a₂.unit.app X at h
  apply (cancel_mono (R₂.map (t.hom.app X))).mp
  change (a₂.unit.app X ≫ R₂.map (t.inv.app X)) ≫ R₂.map (t.hom.app X) =
    (a₁.unit.app X ≫ r.hom.app (L₁.obj X)) ≫ R₂.map (t.hom.app X)
  rw [h, Category.assoc, ← R₂.map_comp, Iso.inv_hom_id_app, R₂.map_id]
  erw [Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem mates_preserve_composition
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* D₀] [Category* D₁] [Category* D₂]
    {F₁ : C₀ ⥤ C₁} {F₂ : C₁ ⥤ C₂} {F₃ : C₀ ⥤ C₂}
    {G₁ : C₁ ⥤ C₀} {G₂ : C₂ ⥤ C₁} {G₃ : C₂ ⥤ C₀}
    {F₁' : D₀ ⥤ D₁} {F₂' : D₁ ⥤ D₂} {F₃' : D₀ ⥤ D₂}
    {G₁' : D₁ ⥤ D₀} {G₂' : D₂ ⥤ D₁} {G₃' : D₂ ⥤ D₀}
    {E₀ : C₀ ⥤ D₀} {E₁ : C₁ ⥤ D₁} {E₂ : C₂ ⥤ D₂}
    (a₁ : F₁ ⊣ G₁) (a₂ : F₂ ⊣ G₂) (a₃ : F₃ ⊣ G₃)
    (a₁' : F₁' ⊣ G₁') (a₂' : F₂' ⊣ G₂') (a₃' : F₃' ⊣ G₃')
    (s₁ : F₁ ⋙ E₁ ≅ E₀ ⋙ F₁') (s₂ : F₂ ⋙ E₂ ≅ E₁ ⋙ F₂')
    (s₃ : F₃ ⋙ E₂ ≅ E₀ ⋙ F₃')
    (r₁ : G₁ ⋙ E₀ ≅ E₁ ⋙ G₁') (r₂ : G₂ ⋙ E₁ ≅ E₂ ⋙ G₂')
    (r₃ : G₃ ⋙ E₀ ≅ E₂ ⋙ G₃')
    (i : G₂ ⋙ G₁ ≅ G₃) (j : G₂' ⋙ G₁' ≅ G₃')
    (h₁ : adjunctionCompatible a₁ a₁' s₁.inv r₁.hom)
    (h₂ : adjunctionCompatible a₂ a₂' s₂.inv r₂.hom)
    (h₃ : adjunctionCompatible a₃ a₃' s₃.inv r₃.hom)
    (h : compositionCoherent r₁ r₂ r₃ i j) :
    let t := ((a₁.comp a₂).ofNatIsoRight i).leftAdjointUniq a₃
    let t' := ((a₁'.comp a₂').ofNatIsoRight j).leftAdjointUniq a₃'
    ∀ X : C₀, E₂.mapIso (t.app X) ≪≫ s₃.app X =
      s₂.app (F₁.obj X) ≪≫ F₂'.mapIso (s₁.app X) ≪≫ t'.app (E₀.obj X) := by
  let t := ((a₁.comp a₂).ofNatIsoRight i).leftAdjointUniq a₃
  let t' := ((a₁'.comp a₂').ofNatIsoRight j).leftAdjointUniq a₃'
  have m₁ := mate_of_unit a₁ a₁' s₁.inv r₁.hom h₁.1
  have m₂ := mate_of_unit a₂ a₂' s₂.inv r₂.hom h₂.1
  have m₃ := mate_of_unit a₃ a₃' s₃.inv r₃.hom h₃.1
  have ml := conjugateEquiv_mateEquiv_vcomp (a₁.comp a₂) a₃ a₃' t.inv s₃.inv
  have mr := mateEquiv_conjugateEquiv_vcomp (a₁.comp a₂) (a₁'.comp a₂') a₃'
    (vComp s₁.inv s₂.inv) t'.inv
  rw [m₃, conjugate_leftAdjointUniq_inv] at ml
  rw [mateEquiv_hcomp, m₁, m₂, conjugate_leftAdjointUniq_inv] at mr
  have hr : TwoSquare.whiskerTop r₃.hom i.hom = TwoSquare.whiskerBottom (hComp r₂.hom r₁.hom) j.hom := by
    ext X
    simpa [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp, Category.assoc] using h X
  have hl : TwoSquare.whiskerLeft s₃.inv t.inv = TwoSquare.whiskerRight (vComp s₁.inv s₂.inv) t'.inv :=
    (mateEquiv (a₁.comp a₂) a₃').injective (ml.trans (hr.trans mr.symm))
  change ∀ X : C₀, E₂.mapIso (t.app X) ≪≫ s₃.app X =
    s₂.app (F₁.obj X) ≪≫ F₂'.mapIso (s₁.app X) ≪≫ t'.app (E₀.obj X)
  intro X
  have hh : (E₂.mapIso (t.app X) ≪≫ s₃.app X).symm =
      (s₂.app (F₁.obj X) ≪≫ F₂'.mapIso (s₁.app X) ≪≫ t'.app (E₀.obj X)).symm := by
    apply Iso.ext
    simpa [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp, Category.assoc]
      using NatTrans.congr_app hl X
  exact congrArg Iso.symm hh

open Specs.DerivedFormalization.CochainRingTransport (derivedComp restrictionComp conjugateComp
  derivedFunctorValue derivedRestrictionIsoValue)
open Specs.DerivedFormalization.ScalarExtensionTransport (MonoidalChange DiagonalComparison)

private theorem composition_respects_diagonal :
  ∀ {R : Type u} {S : Type w} {T : Type z} {A B C : Type a}
    [CommRing R] [CommRing S] [CommRing T] [CommRing A] [CommRing B] [CommRing C]
    {e : R ≃+* A} {d : S ≃+* B} {c : T ≃+* C} {f : R →+* S} {g : S →+* T}
    {MR : AdequateModel e} {MS : AdequateModel d} {MT : AdequateModel c}
    {DR : Descent MR} {DS : Descent MS} {DT : Descent MT}
    {NR : RingTensor DR} {NS : RingTensor DS} {NT : RingTensor DT}
    {F : MonoidalChange e d f MR MS} {G : MonoidalChange d c g MS MT}
    {H : MonoidalChange e c (g.comp f) MR MT}
    {DF : DiagonalComparison e d f MR MS F} {DG : DiagonalComparison d c g MS MT G}
    {DH : DiagonalComparison e c (g.comp f) MR MT H}
    {LF : Extension d f} {LG : Extension c g} {LH : Extension c (g.comp f)}
    {MF : MonoidalExtension DR DS F LF} {MG : MonoidalExtension DS DT G LG}
    {MH : MonoidalExtension DR DT H LH}
    (NF : DiagonalExtension NR NS MF DF) (NG : DiagonalExtension NS NT MG DG)
    (NH : DiagonalExtension NR NT MH DH),
    let iso := extensionComp LF LG LH (restrictionComp f g)
    let nativeIso := extensionComp NF.native NG.native NH.native (conjugateComp e d c f g)
    ∀ X : derivedValue.{a} R,
      (derivedFunctorValue c).mapIso (iso.app X) ≪≫ NH.comparison.app X =
        NG.comparison.app (LF.derived.obj X) ≪≫
          NG.native.derived.mapIso (NF.comparison.app X) ≪≫
          nativeIso.app ((derivedFunctorValue e).obj X) := by
  intro R S T A B C _ _ _ _ _ _ e d c f g MR MS MT DR DS DT NR NS NT F G H DF DG DH
    LF LG LH MF MG MH NF NG NH
  exact mates_preserve_composition LF.adj LG.adj LH.adj NF.native.adj NG.native.adj NH.native.adj
    NF.comparison NG.comparison NH.comparison
    (derivedRestrictionIsoValue e d f) (derivedRestrictionIsoValue d c g)
    (derivedRestrictionIsoValue e c (g.comp f))
    (derivedComp (restrictionComp f g)) (derivedComp (conjugateComp e d c f g))
    NF.adjunction NG.adjunction NH.adjunction
    (DerivedFormalization.CochainRingTransport.compositionCoherence e d c f g).2.2

end CoherentMates


section CompositionOnModels

open Specs.DerivedFormalization.CochainRingTransport (derivedComp restrictionComp)
open Specs.DerivedFormalization.CochainTensorTransport (AdequateModel)
open Specs.DerivedFormalization.DerivedRestriction (restrictScalarsComplexValue
  derivedRestrictScalarsValue derivedRestrictScalarsFactorsValue)
open Specs.DerivedFormalization.ScalarExtensionTransport (extensionAdjunction compositionIso)
open private derivedTriangleFactors from MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.CochainRingTransport

set_option backward.isDefEq.respectTransparency false in
private theorem transpose_on_flat {R : Type u} {S : Type w} {A : Type a}
    [CommRing R] [CommRing S] [CommRing A] {e : R ≃+* A}
    {f : R →+* S} {F : compValue.{a} R ⥤ compValue.{a} S}
    {adj₀ : F ⊣ restrictScalarsComplexValue.{a} f} (L : AdjointModel f F adj₀)
    (M : AdequateModel e) [(flatQ.{u,a} R).IsLocalization (flatChainQuasiIso.{u,a} R)]
    (P : compValue.{a} R) (hP : isKFlat P) (Y : compValue.{a} S) (k : F.obj P ⟶ Y) :
    L.adj.homEquiv ((qValue R).obj P) ((qValue S).obj Y)
      ((L.toLift.model P hP).hom ≫ (qValue S).map k) =
      (qValue R).map (adj₀.homEquiv P Y k) ≫ (derivedRestrictScalarsFactorsValue f).inv.app Y := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, unit_on_flat_model L M]
  have h := (derivedRestrictScalarsFactorsValue f).inv.naturality k
  change (qValue R).map ((restrictScalarsComplexValue f).map k) ≫
      (derivedRestrictScalarsFactorsValue f).inv.app Y =
    (derivedRestrictScalarsFactorsValue f).inv.app (F.obj P) ≫
      (derivedRestrictScalarsValue f).map ((qValue S).map k) at h
  rw [Category.assoc, ← h, ← Functor.map_comp_assoc, Adjunction.homEquiv_unit]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1800000 in
private theorem composition_on_models
    {R : Type u} {S : Type w} {T : Type z} [CommRing R] [CommRing S] [CommRing T]
    {A B C : Type a} [CommRing A] [CommRing B] [CommRing C] {e : R ≃+* A}
    {d : S ≃+* B} {c : T ≃+* C} {f : R →+* S} {g : S →+* T}
    {MR : AdequateModel e} {MS : AdequateModel d} (DR : Descent MR) (DS : Descent MS)
    (LF : Extension d f) (LG : Extension c g) (LH : Extension c (g.comp f))
    (P : compValue.{a} R) (hP : isKFlat P) :
    (extensionComp LF LG LH (restrictionComp f g)).app ((qValue R).obj P) ≪≫ LH.toLift.model P hP =
      LG.derived.mapIso (LF.toLift.model P hP) ≪≫
        LG.toLift.model ((extension d f).obj P) (LF.preservesFlat P hP) ≪≫
        (qValue T).mapIso ((compositionIso d f c g).app P) := by
  haveI := DR.localization
  haveI := DS.localization
  haveI := flatQ_isLocalization MR
  haveI := flatQ_isLocalization MS
  let qR := qValue.{a} R
  let qS := qValue.{a} S
  let qT := qValue.{a} T
  let Y := (extension d f).obj P
  let Z := (extension c (g.comp f)).obj P
  let o := (compositionIso d f c g).app P
  let k := o.hom
  let lf := LF.toLift.model P hP
  let lg := LG.toLift.model Y (LF.preservesFlat P hP)
  let lh := LH.toLift.model P hP
  let r := restrictionComp.{a} f g
  let rD := derivedComp r
  let α := (LF.adj.comp LG.adj).ofNatIsoRight rD
  let u := derivedRestrictScalarsValue.{a} f
  let v := derivedRestrictScalarsValue.{a} g
  let w := derivedRestrictScalarsValue.{a} (g.comp f)
  let cu := restrictScalarsComplexValue.{a} f
  let cv := restrictScalarsComplexValue.{a} g
  let iu := derivedRestrictScalarsFactorsValue.{a} f
  let iv := (derivedRestrictScalarsFactorsValue.{a} g).app Z
  let iw := (derivedRestrictScalarsFactorsValue.{a} (g.comp f)).app Z
  let m := (extensionAdjunction c g).homEquiv Y Z k
  let n := (extensionAdjunction d f).homEquiv P (cv.obj Z) m
  let η := (extensionAdjunction c (g.comp f)).unit.app P
  let rk := (Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ)).hom.app Z
  have hr : rD.hom.app (qT.obj Z) ≫ iw.hom =
      u.map iv.hom ≫ iu.hom.app (cv.obj Z) ≫ qR.map rk :=
    derivedTriangleFactors r Z
  have ho : n ≫ rk = η := by
    have hh := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (((extensionAdjunction d f).comp (extensionAdjunction c g)).ofNatIsoRight
        ((Functor.mapHomologicalComplexCompIso (Iso.refl
          (ModuleCat.restrictScalars.{a} g ⋙ ModuleCat.restrictScalars.{a} f)) (.up ℤ)) ≪≫
          NatIso.mapHomologicalComplex r (.up ℤ))) (extensionAdjunction c (g.comp f)) P
    change _ = η at hh
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv] at hh
    exact hh
  apply Iso.ext
  change (α.leftAdjointUniq LH.adj).hom.app (qR.obj P) ≫ lh.hom =
    LG.derived.map lf.hom ≫ lg.hom ≫ qT.map k
  apply (α.homEquiv (qR.obj P) (qT.obj Z)).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [unit_on_flat_model LH MR P hP]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change qR.map η ≫ iw.inv =
    LF.adj.homEquiv (qR.obj P) (v.obj (qT.obj Z))
      (LG.adj.homEquiv (LF.derived.obj (qR.obj P)) (qT.obj Z)
        (LG.derived.map lf.hom ≫ lg.hom ≫ qT.map k)) ≫ rD.hom.app (qT.obj Z)
  rw [Adjunction.homEquiv_naturality_left]
  erw [transpose_on_flat LG MS Y (LF.preservesFlat P hP) Z k]
  change qR.map η ≫ iw.inv =
    LF.adj.homEquiv (qR.obj P) (v.obj (qT.obj Z))
      (lf.hom ≫ qS.map m ≫ iv.inv) ≫ rD.hom.app (qT.obj Z)
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right]
  erw [transpose_on_flat LF MR P hP (cv.obj Z) m]
  apply (cancel_mono iw.hom).mp
  simp only [Category.assoc]
  rw [Iso.inv_hom_id, Category.comp_id, hr, Iso.inv_hom_id_map_assoc, Iso.inv_hom_id_app_assoc,
    ← qR.map_comp, ho]

end CompositionOnModels


section ExtensionFactorsMonoidal

open Functor.LaxMonoidal
open Specs.DerivedFormalization.CochainTensorTransport (representedUnit)
open Specs.DerivedFormalization.ScalarExtensionTransport (MonoidalChange)

variable {R : Type u} {S : Type w} {A B : Type a} [CommRing R] [CommRing S]
  [CommRing A] [CommRing B] {e : R ≃+* A} {d : S ≃+* B} {f : R →+* S}
  {MR : AdequateModel e} {MS : AdequateModel d}
  {DR : Descent MR} {DS : Descent MS}
  {F : MonoidalChange e d f MR MS} {L : Extension d f}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1400000 in
private theorem extensionLift_monoidal (ML : MonoidalExtension DR DS F L) :
    letI := MR.chainMonoidal
    letI := MR.chainSymmetric
    letI := MR.homotopyMonoidal
    letI := MR.homotopySymmetric
    letI := MR.quotientBraided
    letI := DR.flatMonoidal
    letI := DR.monoidal
    letI := DR.symmetric
    letI := DR.braided
    letI := flatComplexes_monoidal MR
    letI := flatQBraided R
    letI := MS.chainMonoidal
    letI := MS.chainSymmetric
    letI := MS.homotopyMonoidal
    letI := MS.homotopySymmetric
    letI := MS.quotientBraided
    letI := DS.flatMonoidal
    letI := DS.monoidal
    letI := DS.symmetric
    letI := DS.braided
    letI := flatComplexes_monoidal MS
    letI := flatQBraided S
    letI := F.extensionBraided
    letI : L.toLift.derived.Braided := ML.braided
    letI := braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{w,a} S) (extension d f)
      (fun P => L.preservesFlat P.obj P.property)
    (liftFactors L.toLift L.preservesFlat).hom.IsMonoidal := by
  letI := MR.chainMonoidal
  letI := MR.chainSymmetric
  letI := MR.homotopyMonoidal
  letI := MR.homotopySymmetric
  letI := MR.quotientBraided
  letI := DR.flatMonoidal
  letI := DR.monoidal
  letI := DR.symmetric
  letI := DR.braided
  letI := flatComplexes_monoidal MR
  letI := flatQBraided R
  letI := MS.chainMonoidal
  letI := MS.chainSymmetric
  letI := MS.homotopyMonoidal
  letI := MS.homotopySymmetric
  letI := MS.quotientBraided
  letI := DS.flatMonoidal
  letI := DS.monoidal
  letI := DS.symmetric
  letI := DS.braided
  letI := flatComplexes_monoidal MS
  letI := flatQBraided S

  letI := F.extensionBraided
  letI : L.toLift.derived.Braided := ML.braided
  let I := L.toLift
  let E := extension d f
  let q := qValue S
  let G := flatMap E L.preservesFlat
  letI := braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{w,a} S) E
    (fun P => L.preservesFlat P.obj P.property)
  change (liftFactors I L.preservesFlat).hom.IsMonoidal
  refine ⟨?_, fun X Y => ?_⟩
  · let X := 𝟙_ ((flatComplexes.{u,a} R).FullSubcategory)
    have hX := flat_of_homotopy_iso MR ((quotientValue R).mapIso MR.unitModel.symm) X.property
    have hh := congrArg Iso.hom (ML.unit_on_model hX)
    simp only [Iso.trans_hom, Functor.Monoidal.εIso_hom, Functor.mapIso_hom, Iso.symm_hom] at hh
    erw [unitComparison_ε DR, unitComparison_ε DS] at hh
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_map_assoc] at hh
    rw [comp_ε, comp_ε]
    change (ε I.derived ≫ I.derived.map (ε (flatQ.{u,a} R))) ≫ (I.model X.obj X.property).hom =
      ε (flatQ.{w,a} S) ≫ q.map (ε G).hom
    rw [braidedRestriction_ε (flatComplexes.{u,a} R) (flatComplexes.{w,a} S)]
    let h := q.map (E.map MR.unitModel.inv)
    apply (cancel_mono h).mp
    simp only [Category.assoc]
    have hs := model_naturality I X.property hX MR.unitModel.inv
    erw [← hs]
    exact hh
  · let P := X.obj
    let Q := Y.obj
    let j := MR.tensorModel P Q
    let i := MS.tensorModel (E.obj P) (E.obj Q)
    have hPQ : isKFlat (CochainTensor.tensor P Q) :=
      flat_of_homotopy_iso MR ((quotientValue R).mapIso j.symm) (X ⊗ Y).property
    have hh := congrArg Iso.hom (ML.tensor_on_models P Q X.property Y.property hPQ)
    simp only [Iso.trans_hom, Functor.Monoidal.μIso_hom, Functor.mapIso_hom, Iso.symm_hom,
      tensorIso_hom] at hh
    erw [flatComparison_μ DR X Y, flatComparison_μ DS (G.obj X) (G.obj Y)] at hh
    simp only [Functor.map_comp, Category.assoc] at hh
    have hh' :
        μ I.derived ((qValue R).obj P) ((qValue R).obj Q) ≫ I.derived.map (μ (flatQ.{u,a} R) X Y) ≫
          I.derived.map ((qValue R).map j.inv) ≫ (I.model (CochainTensor.tensor P Q) hPQ).hom =
        ((I.model P X.property).hom ⊗ₘ (I.model Q Y.property).hom) ≫
          μ (flatQ.{w,a} S) (G.obj X) (G.obj Y) ≫
            q.map i.inv ≫ q.map i.hom ≫ q.map (μ E P Q) ≫ q.map (E.map j.inv) := hh
    rw [Iso.inv_hom_id_map_assoc] at hh'
    rw [comp_μ, comp_μ]
    change (μ I.derived ((qValue R).obj P) ((qValue R).obj Q) ≫
        I.derived.map (μ (flatQ.{u,a} R) X Y)) ≫ (I.model (X ⊗ Y).obj (X ⊗ Y).property).hom =
      ((I.model P X.property).hom ⊗ₘ (I.model Q Y.property).hom) ≫
        μ (flatQ.{w,a} S) (G.obj X) (G.obj Y) ≫ q.map (μ G X Y).hom
    rw [braidedRestriction_μ (flatComplexes.{u,a} R) (flatComplexes.{w,a} S)]
    apply (cancel_mono (q.map (E.map j.inv))).mp
    simp only [Category.assoc]
    have hs := model_naturality I (X ⊗ Y).property hPQ j.inv
    erw [← hs]
    exact hh'

end ExtensionFactorsMonoidal


section MonoidalTransitivity

open Functor.LaxMonoidal
open Specs.DerivedFormalization.CochainRingTransport (restrictionComp)
open Specs.DerivedFormalization.ScalarExtensionTransport (MonoidalChange DiagonalComparison
  compositionIso)

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  {P : ObjectProperty C} {Q : ObjectProperty D} {U : ObjectProperty E}
  {F : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}

private def restrictTransitivity
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ X : Q.FullSubcategory, U (G.obj X.obj))
    (hH : ∀ X : P.FullSubcategory, U (H.obj X.obj))
    (θ : F ⋙ G ≅ H) :
    restrictFunctor F hF ⋙ restrictFunctor G hG ≅ restrictFunctor H hH :=
  NatIso.ofComponents (fun X => U.isoMk (θ.app X.obj))
    (fun f => U.hom_ext (θ.hom.naturality f.hom))

set_option backward.isDefEq.respectTransparency false in
private theorem restrictTransitivity_monoidal
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [BraidedCategory C] [BraidedCategory D] [BraidedCategory E]
    [P.IsMonoidal] [Q.IsMonoidal] [U.IsMonoidal]
    [F.Braided] [G.Braided] [H.Braided]
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ X : Q.FullSubcategory, U (G.obj X.obj))
    (hH : ∀ X : P.FullSubcategory, U (H.obj X.obj))
    (θ : F ⋙ G ≅ H) [θ.hom.IsMonoidal] :
    letI := braidedRestriction P Q F hF
    letI := braidedRestriction Q U G hG
    letI := braidedRestriction P U H hH
    (restrictTransitivity hF hG hH θ).hom.IsMonoidal := by
  letI := braidedRestriction P Q F hF
  letI := braidedRestriction Q U G hG
  letI := braidedRestriction P U H hH
  change (restrictTransitivity hF hG hH θ).hom.IsMonoidal
  refine ⟨?_, fun X Y => ?_⟩
  · apply U.hom_ext
    simp only [comp_ε, ObjectProperty.FullSubcategory.comp_hom]
    change ((ε (restrictFunctor G hG)).hom ≫ G.map (ε (restrictFunctor F hF)).hom) ≫ _ =
      (ε (restrictFunctor H hH)).hom
    erw [braidedRestriction_ε Q U G hG, braidedRestriction_ε P Q F hF,
      braidedRestriction_ε P U H hH]
    exact NatTrans.IsMonoidal.unit (τ := θ.hom)
  · apply U.hom_ext
    simp only [comp_μ, ObjectProperty.FullSubcategory.comp_hom]
    change ((μ (restrictFunctor G hG) _ _).hom ≫ G.map (μ (restrictFunctor F hF) X Y).hom) ≫ _ =
      _ ≫ (μ (restrictFunctor H hH) X Y).hom
    erw [braidedRestriction_μ Q U G hG, braidedRestriction_μ P Q F hF,
      braidedRestriction_μ P U H hH]
    exact NatTrans.IsMonoidal.tensor (τ := θ.hom) X.obj Y.obj

variable {R : Type u} {S : Type w} {T : Type z} [CommRing R] [CommRing S] [CommRing T]
    {A B C' : Type a} [CommRing A] [CommRing B] [CommRing C'] {e : R ≃+* A}
    {d : S ≃+* B} {c : T ≃+* C'} {f : R →+* S} {g : S →+* T}
    {MR : AdequateModel e} {MS : AdequateModel d} {MT : AdequateModel c}
    {DR : Descent MR} {DS : Descent MS} {DT : Descent MT}
    {FF : MonoidalChange e d f MR MS} {GG : MonoidalChange d c g MS MT}
    {HH : MonoidalChange e c (g.comp f) MR MT}
    {LF : Extension d f} {LG : Extension c g} {LH : Extension c (g.comp f)}

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2400000 in
private theorem extensionComp_isMonoidal
    (MF : MonoidalExtension DR DS FF LF) (MG : MonoidalExtension DS DT GG LG)
    (MH : MonoidalExtension DR DT HH LH) :
    letI := DR.monoidal
    letI := DS.monoidal
    letI := DT.monoidal
    letI := DR.symmetric
    letI := DS.symmetric
    letI := DT.symmetric
    letI := MF.braided
    letI := MG.braided
    letI := MH.braided
    (extensionComp LF LG LH (restrictionComp f g)).hom.IsMonoidal := by
  letI := MR.chainMonoidal
  letI := MR.chainSymmetric
  letI := MR.homotopyMonoidal
  letI := MR.homotopySymmetric
  letI := MR.quotientBraided
  letI := DR.flatMonoidal
  letI := DR.monoidal
  letI := DR.symmetric
  letI := DR.braided
  letI := flatComplexes_monoidal MR
  letI := flatQBraided R
  letI := MS.chainMonoidal
  letI := MS.chainSymmetric
  letI := MS.homotopyMonoidal
  letI := MS.homotopySymmetric
  letI := MS.quotientBraided
  letI := DS.flatMonoidal
  letI := DS.monoidal
  letI := DS.symmetric
  letI := DS.braided
  letI := flatComplexes_monoidal MS
  letI := flatQBraided S
  letI := MT.chainMonoidal
  letI := MT.chainSymmetric
  letI := MT.homotopyMonoidal
  letI := MT.homotopySymmetric
  letI := MT.quotientBraided
  letI := DT.flatMonoidal
  letI := DT.monoidal
  letI := DT.symmetric
  letI := DT.braided
  letI := flatComplexes_monoidal MT
  letI := flatQBraided T
  letI := FF.extensionBraided
  letI := GG.extensionBraided
  letI := HH.extensionBraided
  letI : LF.toLift.derived.Braided := MF.braided
  letI : LG.toLift.derived.Braided := MG.braided
  letI : LH.toLift.derived.Braided := MH.braided
  letI := braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{w,a} S) (extension d f)
    (fun P => LF.preservesFlat P.obj P.property)
  letI := braidedRestriction (flatComplexes.{w,a} S) (flatComplexes.{z,a} T) (extension c g)
    (fun P => LG.preservesFlat P.obj P.property)
  letI := braidedRestriction (flatComplexes.{u,a} R) (flatComplexes.{z,a} T) (extension c (g.comp f))
    (fun P => LH.preservesFlat P.obj P.property)
  haveI := extensionLift_monoidal MF
  haveI := extensionLift_monoidal MG
  haveI := extensionLift_monoidal MH
  haveI := DR.localization
  haveI := flatQ_isLocalization MR
  let i := compLiftFactors LF.toLift LG.toLift LF.preservesFlat LG.preservesFlat
  let j := liftFactors LH.toLift LH.preservesFlat
  haveI : i.hom.IsMonoidal :=
    compLiftFactors_isMonoidal LF.toLift LG.toLift LF.preservesFlat LG.preservesFlat
  haveI : j.hom.IsMonoidal := extensionLift_monoidal MH
  let q := flatQ.{z,a} T
  let o := compositionIso d f c g
  haveI : o.hom.IsMonoidal :=
    (DerivedFormalization.ScalarExtensionTransport.composition e d c f g).2.1 MR MS MT FF GG HH
  let hF (P : (flatComplexes.{u,a} R).FullSubcategory) := LF.preservesFlat P.obj P.property
  let hG (P : (flatComplexes.{w,a} S).FullSubcategory) := LG.preservesFlat P.obj P.property
  let hH (P : (flatComplexes.{u,a} R).FullSubcategory) := LH.preservesFlat P.obj P.property
  let θ := restrictTransitivity (P := flatComplexes.{u,a} R) (Q := flatComplexes.{w,a} S)
    (U := flatComplexes.{z,a} T) hF hG hH o
  haveI : θ.hom.IsMonoidal :=
    restrictTransitivity_monoidal (P := flatComplexes.{u,a} R) (Q := flatComplexes.{w,a} S)
      (U := flatComplexes.{z,a} T) hF hG hH o
  let b := Functor.associator (flatMap (extension d f) LF.preservesFlat)
    (flatMap (extension c g) LG.preservesFlat) q
  haveI : b.inv.IsMonoidal := by
    dsimp only [b]
    infer_instance
  let τ := b.symm ≪≫ Functor.isoWhiskerRight θ q
  haveI : τ.hom.IsMonoidal :=
    show (b.inv ≫ Functor.whiskerRight θ.hom q).IsMonoidal from inferInstance
  let J := flatQ.{u,a} R
  let W := flatChainQuasiIso.{u,a} R
  let m := descendIso J W i j τ
  have hm : m.hom.IsMonoidal := descendIso_monoidal J W i j τ
  have eq : (extensionComp LF LG LH (restrictionComp f g)).hom = m.hom := by
    apply Localization.natTrans_ext J W
    intro P
    apply (cancel_mono (j.hom.app P)).mp
    have h := descendIso_app J W i j τ P
    have hτ : (τ.app P).hom = (qValue T).map (o.hom.app P.obj) := by
      change 𝟙 _ ≫ (qValue T).map (o.hom.app P.obj) = _
      erw [Category.id_comp]
    have hi := compLiftFactors_app LF.toLift LG.toLift LF.preservesFlat LG.preservesFlat P.obj P.property
    change m.app (J.obj P) ≪≫ j.app P = i.app P ≪≫ τ.app P at h
    have hx := congrArg Iso.hom h
    have h₀ := congrArg Iso.hom (composition_on_models DR DS LF LG LH P.obj P.property)
    have hi' : (i.app P).hom = LG.derived.map (LF.toLift.model P.obj P.property).hom ≫
        (LG.toLift.model ((extension d f).obj P.obj) (LF.preservesFlat P.obj P.property)).hom :=
      congrArg Iso.hom hi
    simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom] at hx h₀
    simp only [Iso.app_hom] at hi' hτ
    erw [hi', hτ] at hx
    exact h₀.trans (by simpa only [Category.assoc] using hx.symm)
  change (extensionComp LF LG LH (restrictionComp f g)).hom.IsMonoidal
  rw [eq]
  exact hm

open Specs.DerivedFormalization.CochainRingTransport (conjugateComp)

theorem composition : Composition.{u,w,z,a} := by
  intro R S T A B C _ _ _ _ _ _ e d c f g MR MS MT DR DS DT NR NS NT FF GG HH DF DG DH
    LF LG LH MF MG MH NF NG NH
  exact ⟨composition_on_models DR DS LF LG LH, extensionComp_isMonoidal MF MG MH,
    composition_respects_diagonal NF NG NH⟩

end MonoidalTransitivity

end

end DerivedFormalization.DerivedScalarExtension
