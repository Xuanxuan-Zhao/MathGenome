import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.MayerVietoris
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.ShortExactDerivedTriangle

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory AdvancedHomologicalAlgebra.MayerVietorisData
open Specs.AdvancedHomologicalAlgebra.MayerVietoris
universe u

namespace AdvancedHomologicalAlgebra.MayerVietoris

variable {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X)

/-- The underlying set-valued sheaf satisfies two-open gluing. -/
lemma gluing (M : Modules R) :
    (Opens.mayerVietorisSquare V W).SheafCondition
      (M.val.presheaf ⋙ forget AddCommGrpCat.{u}) := by
  exact (Opens.mayerVietorisSquare V W).sheafCondition_of_sheaf
    ((sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat.{u})).obj
      ((SheafOfModules.toSheaf R).obj M))

/-- The section maps are jointly injective. -/
lemma sectionRow_mono (M : Modules R) : Mono (sectionRow R V W M).f := by
  apply (ModuleCat.mono_iff_injective _).mpr
  intro a b hab
  exact (gluing R V W M).ext (congrArg Prod.fst hab) (congrArg Prod.snd hab)

/-- Compatible sections glue, over the original union's ring of sections. -/
lemma sectionRow_exact (M : Modules R) : (sectionRow R V W M).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  have hab : M.val.map (homOfLE (show V ⊓ W ≤ V from inf_le_left)).op x.1 =
      M.val.map (homOfLE (show V ⊓ W ≤ W from inf_le_right)).op x.2 := by
    exact sub_eq_zero.mp hx
  refine ⟨(gluing R V W M).glue x.1 x.2 hab, ?_⟩
  exact Prod.ext ((gluing R V W M).map_f₂₄_op_glue x.1 x.2 hab)
    ((gluing R V W M).map_f₃₄_op_glue x.1 x.2 hab)

/-- A flasque section on the intersection extends to the first open. -/
lemma sectionRow_epi (M : Modules R) (hM : IsFlasque R M) :
    Epi (sectionRow R V W M).g := by
  apply (ModuleCat.epi_iff_surjective _).mpr
  intro x
  obtain ⟨a, ha⟩ := hM (V ⊓ W) V inf_le_left x
  refine ⟨(a, 0), ?_⟩
  simpa [sectionRow, res] using ha

theorem sectionsExact : sectionsExactType.{u} := by
  intro X R V W M hM
  exact ShortComplex.ShortExact.mk' (sectionRow_exact R V W M)
    (sectionRow_mono R V W M) (sectionRow_epi R V W M hM)

end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris
variable {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X)

section Products
variable {S : Type u} [Ring S] {A B C : ModuleCat.{u} S}

lemma lift_product (f : C ⟶ A) (g : C ⟶ B) :
    biprod.lift f g ≫ (ModuleCat.biprodIsoProd A B).hom =
      ModuleCat.ofHom (X := C) (Y := ModuleCat.of S (A × B)) (f.hom.prod g.hom) := by
  apply (cancel_mono (ModuleCat.biprodIsoProd A B).inv).mp
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst,
      ModuleCat.biprodIsoProd_inv_comp_fst]
    rfl
  · simp only [Category.assoc, biprod.lift_snd,
      ModuleCat.biprodIsoProd_inv_comp_snd]
    rfl

lemma product_difference (f : A ⟶ C) (g : B ⟶ C) :
    (ModuleCat.biprodIsoProd A B).hom ≫
      ModuleCat.ofHom (X := ModuleCat.of S (A × B)) (Y := C)
        (f.hom.comp (LinearMap.fst S A B) - g.hom.comp (LinearMap.snd S A B)) =
      biprod.desc f (-g) := by
  apply (cancel_epi (ModuleCat.biprodIsoProd A B).inv).mp
  rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  simp only [biprod.desc_eq, Preadditive.comp_add,
    ← Category.assoc, ModuleCat.biprodIsoProd_inv_comp_fst,
    ModuleCat.biprodIsoProd_inv_comp_snd]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact sub_eq_add_neg _ _
end Products

/-- Evaluation identifies the middle complex with the product of sections. -/
def degreeRowIso (I : CochainComplex (Modules R) ℤ) (q : ℤ) :
    (complexRow R V W I).map
      (HomologicalComplex.eval (ModuleCat.{u} (sectionRing R (V ⊔ W))) (.up ℤ) q) ≅
    sectionRow R V W (I.X q) := by
  let E := HomologicalComplex.eval (ModuleCat.{u} (sectionRing R (V ⊔ W))) (.up ℤ) q
  let A := sectionComplex R (V ⊔ W) V le_sup_left I
  let B := sectionComplex R (V ⊔ W) W le_sup_right I
  refine ShortComplex.isoMk (Iso.refl _)
    (E.mapBiprod A B ≪≫ ModuleCat.biprodIsoProd _ _) (Iso.refl _) ?_ ?_
  · change 𝟙 _ ≫ (sectionRow R V W (I.X q)).f = E.map (complexRow R V W I).f ≫
      ((E.mapBiprod A B).hom ≫ (ModuleCat.biprodIsoProd (E.obj A) (E.obj B)).hom)
    rw [Category.id_comp, ← Category.assoc]
    change (sectionRow R V W (I.X q)).f =
      (E.map (biprod.lift
        (((res R _ _ V le_rfl le_sup_left le_sup_left).mapHomologicalComplex (.up ℤ)).app I)
        (((res R _ _ W le_rfl le_sup_right le_sup_right).mapHomologicalComplex (.up ℤ)).app I)) ≫
          (E.mapBiprod A B).hom) ≫ _
    rw [biprod.map_lift_mapBiprod]
    exact (lift_product _ _).symm
  · change ((E.mapBiprod A B).hom ≫ (ModuleCat.biprodIsoProd (E.obj A) (E.obj B)).hom) ≫
      (sectionRow R V W (I.X q)).g = E.map (complexRow R V W I).g ≫ 𝟙 _
    rw [Category.comp_id, Category.assoc]
    trans (E.mapBiprod A B).hom ≫ biprod.desc
      ((res R _ V _ le_sup_left (inf_le_left.trans le_sup_left) inf_le_left).app (I.X q))
      (-((res R _ W _ le_sup_right (inf_le_left.trans le_sup_left) inf_le_right).app (I.X q)))
    · congr 1
      exact product_difference _ _
    · simpa only [E, HomologicalComplex.eval_map, NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.neg_f_apply, complexRow, Functor.map_neg] using biprod.mapBiprod_hom_desc E A B
        (((res R _ V _ le_sup_left (inf_le_left.trans le_sup_left) inf_le_left).mapHomologicalComplex (.up ℤ)).app I)
        (-(((res R _ W _ le_sup_right (inf_le_left.trans le_sup_left) inf_le_right).mapHomologicalComplex (.up ℤ)).app I))

theorem complexesExact : complexesExactType.{u} := by
  intro X R V W I hI
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  apply ShortComplex.shortExact_of_iso (degreeRowIso R V W I q).symm
  exact sectionsExact R V W (I.X q)
    (SheafInjectivesAndRestriction.Expected.injectives_flasque R (I.X q) (hI q))

theorem longExact : longExactType.{u} := by
  intro X R V W I hI
  refine ⟨complexesExact R V W I hI, fun n => ?_⟩
  exact HomologicalComplex.HomologySequence.composableArrows₅_exact _ n (n + 1) rfl

theorem naturality : naturalityType.{u} := by
  intro X R V W I J hI hJ hS hT φ n
  exact HomologicalComplex.HomologySequence.δ_naturality
    (complexRowMap R V W φ) hS hT n (n + 1) rfl

theorem resolutionModel : resolutionModelType.{u} := by
  intro X R U T h M I hb ι hι hI n
  let G := ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom
  obtain ⟨e⟩ := SheafCohomology.resolution R T M I ι hι hI n
  exact ⟨G.mapIso e ≪≫
    (((((SheafOfModules.evaluation R (op T)).mapHomologicalComplex (.up ℤ)).obj I).sc
      (n : ℤ)).mapHomologyIso G).symm⟩

theorem derivedBoundary : derivedBoundaryType.{u} := by
  intro X R V W I hS
  let A := ModuleCat.{u} (sectionRing R (V ⊔ W))
  letI := HasDerivedCategory.standard A
  dsimp only
  intro n
  exact ShortExactDerivedTriangle.cohomology_boundary A (complexRow R V W I) hS n (n + 1) rfl

end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris
variable {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X)

/-- The displayed sequence is canonically isomorphic to the ordinary
cohomology sequence of the short exact sequence of complexes. -/
def modelSequenceIso (I : CochainComplex (Modules R) ℤ)
    (hS : (complexRow R V W I).ShortExact) (n : ℤ) :
    modelSequence R V W I hS n ≅
      HomologicalComplex.HomologySequence.composableArrows₅ hS n (n + 1) rfl := by
  refine ComposableArrows.isoMk₅ (Iso.refl _) (middleIso R V W I n).symm (Iso.refl _)
    (Iso.refl _) (middleIso R V W I (n + 1)).symm (Iso.refl _) ?_ ?_ ?_ ?_ ?_
  · dsimp [modelSequence, HomologicalComplex.HomologySequence.composableArrows₅, middleIso]
    simp only [Category.id_comp, complexRow, biprod.lift_desc,
      ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_add]
    congr 1
    exact biprod.lift_eq.symm
  · dsimp [modelSequence, HomologicalComplex.HomologySequence.composableArrows₅, middleIso]
    simp only [Category.comp_id, complexRow]
    apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc,
      biprod.inl_desc_assoc, biprod.inr_desc_assoc, ← HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_neg]
  · simp [modelSequence, HomologicalComplex.HomologySequence.composableArrows₅]
  · dsimp [modelSequence, HomologicalComplex.HomologySequence.composableArrows₅, middleIso]
    simp only [Category.id_comp, complexRow, biprod.lift_desc,
      ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_add]
    congr 1
    exact biprod.lift_eq.symm
  · dsimp [modelSequence, HomologicalComplex.HomologySequence.composableArrows₅, middleIso]
    simp only [Category.comp_id, complexRow]
    apply biprod.hom_ext' <;> simp only [biprod.inl_desc, biprod.inr_desc,
      biprod.inl_desc_assoc, biprod.inr_desc_assoc, ← HomologicalComplex.homologyMap_comp,
      HomologicalComplex.homologyMap_neg]

theorem modelExact : modelExactType.{u} := by
  intro X R V W I hI
  refine ⟨complexesExact R V W I hI, fun n => ?_⟩
  exact ComposableArrows.exact_of_iso (modelSequenceIso R V W I _ n).symm
    (HomologicalComplex.HomologySequence.composableArrows₅_exact _ n (n + 1) rfl)

theorem liftDifferential : liftDifferentialType.{u} := by
  intro X R V W I hS n P c hc b hb a ha
  exact hS.δ_eq n (n + 1) rfl c hc b hb a ha (n + 2) (by apply (ComplexShape.up ℤ).next_eq'; change (n + 1) + 1 = n + 2; omega)

end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris

theorem mayerVietoris : mayerVietorisType.{u} := by
  intro X R V W M
  obtain ⟨I, ι, _, hι, hI, hb⟩ := InjectiveComplexReplacement.replacement
    (Modules R) ((CochainComplex.singleFunctor (Modules R) 0).obj M) 0 (by infer_instance)
  letI := hb
  obtain ⟨hS, hseq⟩ := modelExact R V W I hI
  refine ⟨I, hb, ι, hι, hI, hS, hseq, ?_⟩
  intro T h n
  exact resolutionModel R (V ⊔ W) T h M I ι hι hI n

theorem homotopyIndependence : homotopyIndependenceType.{u} := by
  intro X R U T h I J f g H n
  exact ((sectionsFunctor R U T h).mapHomotopy H).homologyMap_eq n

end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris

theorem resolutionLifts : resolutionLiftsType.{u} := by
  intro X R M N I J hbI hbJ ι κ hι hκ hJ f
  letI := HasDerivedCategory.standard (Modules R)
  letI := hJ
  letI := CochainComplex.isKInjective_of_injective J 0
  let Q := HomotopyCategory.quotient (Modules R) (.up ℤ)
  let L := _root_.DerivedCategory.Qh (C := Modules R)
  have hi : IsIso (L.map (Q.map ι)) :=
    Localization.inverts L (HomotopyCategory.quasiIso (Modules R) (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff ι).mpr hι)
  letI := hi
  let a := (CochainComplex.singleFunctor (Modules R) 0).map f ≫ κ
  let d := inv (L.map (Q.map ι)) ≫ L.map (Q.map a)
  obtain ⟨k, hk⟩ := (CochainComplex.IsKInjective.Qh_map_bijective (Q.obj I) J).surjective d
  obtain ⟨φ, hφ⟩ := Q.map_surjective k
  rw [← hφ] at hk
  have he : Q.map (ι ≫ φ) = Q.map a := by
    apply (CochainComplex.IsKInjective.Qh_map_bijective
      (Q.obj ((CochainComplex.singleFunctor (Modules R) 0).obj M)) J).injective
    change L.map (Q.map (ι ≫ φ)) = L.map (Q.map a)
    rw [Q.map_comp, L.map_comp, hk]
    dsimp only [d]
    simp
  refine ⟨φ, ⟨HomotopyCategory.homotopyOfEq _ _ he⟩, ?_⟩
  intro ψ hψ
  obtain ⟨Hψ⟩ := hψ
  refine ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective (Q.obj I) J).injective
  apply (cancel_epi (L.map (Q.map ι))).mp
  have ee : Q.map (ι ≫ φ) = Q.map (ι ≫ ψ) :=
    he.trans (HomotopyCategory.eq_of_homotopy _ _ Hψ).symm
  have ee' := congrArg L.map ee
  simpa only [Q.map_comp, L.map_comp] using ee'

end AdvancedHomologicalAlgebra.MayerVietoris

universe v u' v'
open CategoryTheory.Functor
namespace AdvancedHomologicalAlgebra.MayerVietoris
section Generic
variable {A : Type u} {B : Type u'} [Category.{v} A] [Abelian A]
  [Category.{v'} B] [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B]
  [EnoughInjectives A]

theorem replacementIso_naturality (F : A ⥤ B) [F.Additive]
    (X Y I J : CochainComplex.Plus A)
    (i : X ⟶ I) (j : Y ⟶ J)
    (hi : QuasiIso i.hom) (hj : QuasiIso j.hom)
    (hI : ∀ n : ℤ, Injective (I.obj.X n)) (hJ : ∀ n : ℤ, Injective (J.obj.X n))
    (a : X ⟶ Y) (φ : I ⟶ J)
    (comm : _root_.DerivedCategory.Plus.Q.map i ≫ _root_.DerivedCategory.Plus.Q.map φ =
      _root_.DerivedCategory.Plus.Q.map a ≫ _root_.DerivedCategory.Plus.Q.map j) :
    F.rightDerivedFunctorPlus.map (_root_.DerivedCategory.Plus.Q.map a) ≫
        (replacementIso F Y J j hj hJ).hom =
      (replacementIso F X I i hi hI).hom ≫
        _root_.DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) := by
  letI := resolutionUnitIsIso F I hI
  letI := resolutionUnitIsIso F J hJ
  have hn : inv (F.rightDerivedFunctorPlusUnit.app I) ≫
        _root_.DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) =
      F.rightDerivedFunctorPlus.map (_root_.DerivedCategory.Plus.Q.map φ) ≫
        inv (F.rightDerivedFunctorPlusUnit.app J) := by
    apply (cancel_mono (F.rightDerivedFunctorPlusUnit.app J)).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [show _root_.DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ) ≫
        F.rightDerivedFunctorPlusUnit.app J =
      F.rightDerivedFunctorPlusUnit.app I ≫
        F.rightDerivedFunctorPlus.map (_root_.DerivedCategory.Plus.Q.map φ) from
          F.rightDerivedFunctorPlusUnit.naturality φ]
    simp
  change F.rightDerivedFunctorPlus.map (_root_.DerivedCategory.Plus.Q.map a) ≫
      (F.rightDerivedFunctorPlus.map (_root_.DerivedCategory.Plus.Q.map j) ≫
        inv (F.rightDerivedFunctorPlusUnit.app J)) =
    (F.rightDerivedFunctorPlus.map (_root_.DerivedCategory.Plus.Q.map i) ≫
      inv (F.rightDerivedFunctorPlusUnit.app I)) ≫
      _root_.DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map φ)
  rw [Category.assoc, hn, ← Category.assoc, ← Category.assoc,
    ← F.rightDerivedFunctorPlus.map_comp, ← F.rightDerivedFunctorPlus.map_comp, comm]


open Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues

theorem resolutionComparison_naturality (F : A ⥤ B) [F.Additive] (M N : A)
    (I J : CochainComplex A ℤ) [I.IsStrictlyGE 0] [J.IsStrictlyGE 0]
    (i : (CochainComplex.singleFunctor A 0).obj M ⟶ I)
    (j : (CochainComplex.singleFunctor A 0).obj N ⟶ J)
    (hi : QuasiIso i) (hj : QuasiIso j)
    (hI : ∀ q : ℤ, Injective (I.X q)) (hJ : ∀ q : ℤ, Injective (J.X q))
    (f : M ⟶ N) (φ : I ⟶ J)
    (H : Homotopy (i ≫ φ) ((CochainComplex.singleFunctor A 0).map f ≫ j)) (n : ℕ) :
    (rightValue F n).map f ≫ (resolutionComparison F N J j hj hJ n).hom =
      (resolutionComparison F M I i hi hI n).hom ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ) (n : ℤ) := by
  let XI : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj M, 0, inferInstance⟩
  let YI : CochainComplex.Plus A := ⟨(CochainComplex.singleFunctor A 0).obj N, 0, inferInstance⟩
  let II : CochainComplex.Plus A := ⟨I, 0, inferInstance⟩
  let JI : CochainComplex.Plus A := ⟨J, 0, inferInstance⟩
  let ii : XI ⟶ II := (CochainComplex.plus A).homMk i
  let jj : YI ⟶ JI := (CochainComplex.plus A).homMk j
  let aa : XI ⟶ YI := (CochainComplex.plus A).homMk ((CochainComplex.singleFunctor A 0).map f)
  let pp : II ⟶ JI := (CochainComplex.plus A).homMk φ
  have comm : _root_.DerivedCategory.Plus.Q.map ii ≫ _root_.DerivedCategory.Plus.Q.map pp =
      _root_.DerivedCategory.Plus.Q.map aa ≫ _root_.DerivedCategory.Plus.Q.map jj := by
    apply (_root_.DerivedCategory.Plus.ι (C := A)).map_injective
    change _root_.DerivedCategory.Q.map i ≫ _root_.DerivedCategory.Q.map φ =
      _root_.DerivedCategory.Q.map ((CochainComplex.singleFunctor A 0).map f) ≫
        _root_.DerivedCategory.Q.map j
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact _root_.DerivedCategory.Q_map_eq_of_homotopy A H
  have hn := replacementIso_naturality F XI YI II JI ii jj hi hj hI hJ aa pp comm
  let HH := _root_.DerivedCategory.Plus.homologyFunctor B (n : ℤ)
  let eI := replacementIso F XI II ii hi hI
  let eJ := replacementIso F YI JI jj hj hJ
  have hfactors : HH.map (_root_.DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map pp)) ≫
      (_root_.DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj J) =
    (_root_.DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app
      ((F.mapHomologicalComplex (.up ℤ)).obj I) ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ) (n : ℤ) :=
    (_root_.DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.naturality
      ((F.mapHomologicalComplex (.up ℤ)).map φ)
  change HH.map (F.rightDerivedFunctorPlus.map (_root_.DerivedCategory.Plus.Q.map aa)) ≫
      (HH.map eJ.hom ≫ (_root_.DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj J)) =
      (HH.map eI.hom ≫ (_root_.DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
        HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℤ)).map φ) (n : ℤ)
  rw [← Category.assoc, ← HH.map_comp, hn, HH.map_comp, Category.assoc, hfactors]
  simp [Category.assoc, eI]

end Generic
end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris

set_option maxHeartbeats 2000000 in
/-- The canonical derived-unit comparison commutes with every lifted
coefficient map, including lifts whose augmentation square commutes up to homotopy. -/
theorem canonicalModelIso_naturality {X : TopCat.{u}} (R : RingSheaf X)
    (U T : Opens X) (h : T ≤ U) (M N : Modules R)
    (I J : CochainComplex (Modules R) ℤ)
    (hbI : I.IsStrictlyGE 0) (hbJ : J.IsStrictlyGE 0)
    (ι : (CochainComplex.singleFunctor (Modules R) 0).obj M ⟶ I)
    (κ : (CochainComplex.singleFunctor (Modules R) 0).obj N ⟶ J)
    (hi : QuasiIso ι) (hj : QuasiIso κ)
    (hI : ∀ q : ℤ, Injective (I.X q)) (hJ : ∀ q : ℤ, Injective (J.X q))
    (f : M ⟶ N) (φ : I ⟶ J)
    (H : Homotopy (ι ≫ φ) ((CochainComplex.singleFunctor (Modules R) 0).map f ≫ κ))
    (n : ℕ) :
    (ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom).map
        ((sectionCohomology R T n).map f) ≫
        (canonicalModelIso R U T h N J hbJ κ hj hJ n).hom =
      (canonicalModelIso R U T h M I hbI ι hi hI n).hom ≫
        HomologicalComplex.homologyMap
          (((sectionsFunctor R U T h).mapHomologicalComplex (.up ℤ)).map φ) (n : ℤ) := by
  letI := hbI
  letI := hbJ
  letI := HasDerivedCategory.standard (Modules R)
  letI := HasDerivedCategory.standard (ModuleCat.{u} (sectionRing R T))
  let E := SheafOfModules.evaluation R (op T)
  let G := ModuleCat.restrictScalars (R.obj.map (homOfLE h).op).hom
  let K := (E.mapHomologicalComplex (.up ℤ)).obj I
  let L := (E.mapHomologicalComplex (.up ℤ)).obj J
  let eI := resolutionComparison E M I ι hi hI n
  let eJ := resolutionComparison E N J κ hj hJ n
  let zI := (K.sc (n : ℤ)).mapHomologyIso G
  let zJ := (L.sc (n : ℤ)).mapHomologyIso G
  have hn := resolutionComparison_naturality E M N I J ι κ hi hj hI hJ f φ H n
  have hg : G.map (HomologicalComplex.homologyMap
        ((E.mapHomologicalComplex (.up ℤ)).map φ) (n : ℤ)) ≫ zJ.inv =
      zI.inv ≫ HomologicalComplex.homologyMap
        (((sectionsFunctor R U T h).mapHomologicalComplex (.up ℤ)).map φ) (n : ℤ) :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} (sectionRing R T)) (.up ℤ) (n : ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map φ)) G
  change G.map ((Specs.AdvancedHomologicalAlgebra.ClassicalDerivedValues.rightValue E n).map f) ≫ (G.map eJ.hom ≫ zJ.inv) =
    (G.map eI.hom ≫ zI.inv) ≫ HomologicalComplex.homologyMap
      (((sectionsFunctor R U T h).mapHomologicalComplex (.up ℤ)).map φ) (n : ℤ)
  rw [← Category.assoc, ← G.map_comp, hn, G.map_comp, Category.assoc, hg]
  simp [Category.assoc, eI]


theorem naturalModels : naturalModelsType.{u} := by
  intro X R U T h
  exact ⟨canonicalModelIso R U T h, canonicalModelIso_naturality R U T h⟩

end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris
variable {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X)
/-- The two-open cohomology sequence begins with an injection in degree zero. -/
lemma modelDegreeZeroMono (I : CochainComplex (Modules R) ℤ) [I.IsStrictlyGE 0]
    (hS : (complexRow R V W I).ShortExact) :
    Mono (HomologicalComplex.homologyMap (complexRow R V W I).f (0 : ℤ)) := by
  have hz : IsZero ((complexRow R V W I).X₃.homology (-1)) := by
    let K := sectionComplex R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) I
    haveI : CochainComplex.IsStrictlyGE K 0 := by
      dsimp [K, sectionComplex]
      infer_instance
    exact CochainComplex.isZero_of_isGE K 0 (-1) (by decide)
  exact ((ShortComplex.mk _ _ (hS.δ_comp (-1) 0 (by decide))).exact_iff_mono
    (hz.eq_of_src _ _)).mp (hS.homology_exact₁ (-1) 0 (by decide))
end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris
/-- The maps induced by restriction on resolution cohomology commute with
all cochain comparison maps. -/
lemma modelRestriction_naturality {X : TopCat.{u}} (R : RingSheaf X)
    (U T S : Opens X) (hT : T ≤ U) (hS : S ≤ U) (h : S ≤ T)
    (I J : CochainComplex (Modules R) ℤ) (φ : I ⟶ J) (n : ℤ) :
    HomologicalComplex.homologyMap
        (((sectionsFunctor R U T hT).mapHomologicalComplex (.up ℤ)).map φ) n ≫
      HomologicalComplex.homologyMap
        (((res R U T S hT hS h).mapHomologicalComplex (.up ℤ)).app J) n =
    HomologicalComplex.homologyMap
        (((res R U T S hT hS h).mapHomologicalComplex (.up ℤ)).app I) n ≫
      HomologicalComplex.homologyMap
        (((sectionsFunctor R U S hS).mapHomologicalComplex (.up ℤ)).map φ) n := by
  simpa only [Functor.map_comp, HomologicalComplex.homologyFunctor_map,
    HomologicalComplex.homologyFunctor_obj, HomologicalComplex.homologyMap_comp] using congrArg
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} (sectionRing R U)) (.up ℤ) n).map
    (((res R U T S hT hS h).mapHomologicalComplex (.up ℤ)).naturality φ)
end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris.TransportHelpers

variable {C : Type u} [Category.{v} C]

/-- Transport of a naturality square through four comparison isomorphisms. -/
lemma transport_naturality
    {A B D E A' B' D' E' : C}
    (eA : A ≅ A') (eB : B ≅ B') (eD : D ≅ D') (eE : E ≅ E')
    (a : A ⟶ D) (b : B ⟶ E) (f : A' ⟶ B') (g : D' ⟶ E')
    (u : A' ⟶ D') (v : B' ⟶ E')
    (ha : a ≫ eD.hom = eA.hom ≫ u)
    (hb : b ≫ eE.hom = eB.hom ≫ v)
    (h : u ≫ g = f ≫ v) :
    a ≫ (eD.hom ≫ g ≫ eE.inv) = (eA.hom ≫ f ≫ eB.inv) ≫ b := by
  apply (cancel_mono eE.hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hb, Iso.inv_hom_id_assoc]
  rw [← Category.assoc a eD.hom g, ha, Category.assoc, h]

/-- The five-arrow sequence obtained by transporting each arrow. -/
def transportSequence₅
    {A₀ A₁ A₂ A₃ A₄ A₅ B₀ B₁ B₂ B₃ B₄ B₅ : C}
    (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂)
    (e₃ : A₃ ≅ B₃) (e₄ : A₄ ≅ B₄) (e₅ : A₅ ≅ B₅)
    (f₀ : B₀ ⟶ B₁) (f₁ : B₁ ⟶ B₂) (f₂ : B₂ ⟶ B₃)
    (f₃ : B₃ ⟶ B₄) (f₄ : B₄ ⟶ B₅) : ComposableArrows C 5 :=
  ComposableArrows.mk₅ (e₀.hom ≫ f₀ ≫ e₁.inv) (e₁.hom ≫ f₁ ≫ e₂.inv)
    (e₂.hom ≫ f₂ ≫ e₃.inv) (e₃.hom ≫ f₃ ≫ e₄.inv) (e₄.hom ≫ f₄ ≫ e₅.inv)

/-- Six object isomorphisms give the comparison with the original sequence. -/
def transportSequenceIso₅
    {A₀ A₁ A₂ A₃ A₄ A₅ B₀ B₁ B₂ B₃ B₄ B₅ : C}
    (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂)
    (e₃ : A₃ ≅ B₃) (e₄ : A₄ ≅ B₄) (e₅ : A₅ ≅ B₅)
    (f₀ : B₀ ⟶ B₁) (f₁ : B₁ ⟶ B₂) (f₂ : B₂ ⟶ B₃)
    (f₃ : B₃ ⟶ B₄) (f₄ : B₄ ⟶ B₅) :
    transportSequence₅ e₀ e₁ e₂ e₃ e₄ e₅ f₀ f₁ f₂ f₃ f₄ ≅
      ComposableArrows.mk₅ f₀ f₁ f₂ f₃ f₄ :=
  ComposableArrows.isoMk₅ e₀ e₁ e₂ e₃ e₄ e₅
    (by simp [transportSequence₅]) (by simp [transportSequence₅])
    (by simp [transportSequence₅]) (by simp [transportSequence₅])
    (by simp [transportSequence₅])

lemma transport_exact₅ [HasZeroMorphisms C]
    {A₀ A₁ A₂ A₃ A₄ A₅ B₀ B₁ B₂ B₃ B₄ B₅ : C}
    (e₀ : A₀ ≅ B₀) (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂)
    (e₃ : A₃ ≅ B₃) (e₄ : A₄ ≅ B₄) (e₅ : A₅ ≅ B₅)
    (f₀ : B₀ ⟶ B₁) (f₁ : B₁ ⟶ B₂) (f₂ : B₂ ⟶ B₃)
    (f₃ : B₃ ⟶ B₄) (f₄ : B₄ ⟶ B₅)
    (h : (ComposableArrows.mk₅ f₀ f₁ f₂ f₃ f₄).Exact) :
    (transportSequence₅ e₀ e₁ e₂ e₃ e₄ e₅ f₀ f₁ f₂ f₃ f₄).Exact :=
  ComposableArrows.exact_of_iso
    (transportSequenceIso₅ e₀ e₁ e₂ e₃ e₄ e₅ f₀ f₁ f₂ f₃ f₄).symm h

end AdvancedHomologicalAlgebra.MayerVietoris.TransportHelpers

namespace AdvancedHomologicalAlgebra.MayerVietoris.TransportHelpers
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
lemma transport_lift {A B D A' B' D' : C}
    (eA : A ≅ A') (eB : B ≅ B') (eD : D ≅ D') (f : A' ⟶ B') (g : A' ⟶ D') :
    biprod.lift (eA.hom ≫ f ≫ eB.inv) (eA.hom ≫ g ≫ eD.inv) =
      eA.hom ≫ biprod.lift f g ≫ (biprod.mapIso eB eD).inv := by
  apply biprod.hom_ext <;> simp [Category.assoc]
lemma transport_desc {A B D A' B' D' : C}
    (eA : A ≅ A') (eB : B ≅ B') (eD : D ≅ D') (f : A' ⟶ D') (g : B' ⟶ D') :
    biprod.desc (eA.hom ≫ f ≫ eD.inv) (eB.hom ≫ g ≫ eD.inv) =
      (biprod.mapIso eA eB).hom ≫ biprod.desc f g ≫ eD.inv := by
  apply biprod.hom_ext' <;> simp
end AdvancedHomologicalAlgebra.MayerVietoris.TransportHelpers

namespace AdvancedHomologicalAlgebra.MayerVietoris
variable {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X)
    (m : ∀ M : Modules R, ResolutionModel R M)
    (hS : ∀ M : Modules R, (complexRow R V W (m M).complex).ShortExact)

def cohomologySequenceIso (M : Modules R) (n : ℕ) :
    cohomologySequence R V W m hS M n ≅
      modelSequence R V W (m M).complex (hS M) (n : ℤ) := by
  let e := cohomologyComparison R V W m
  refine ComposableArrows.isoMk₅
    (e (V ⊔ W) le_rfl M n)
    (biprod.mapIso (e V le_sup_left M n) (e W le_sup_right M n))
    (e (V ⊓ W) (inf_le_left.trans le_sup_left) M n)
    (e (V ⊔ W) le_rfl M (n + 1))
    (biprod.mapIso (e V le_sup_left M (n + 1)) (e W le_sup_right M (n + 1)))
    (e (V ⊓ W) (inf_le_left.trans le_sup_left) M (n + 1)) ?_ ?_ ?_ ?_ ?_
  · dsimp [cohomologySequence, cohomologyAlpha, cohomologyRestriction, modelSequence, e]
    apply biprod.hom_ext <;> simp [Category.assoc]
  · dsimp [cohomologySequence, cohomologyBeta, cohomologyRestriction, modelSequence, e]
    apply biprod.hom_ext' <;> simp [Category.assoc]
  · simp [cohomologySequence, cohomologyDelta, modelSequence, e, Category.assoc]
  · dsimp [cohomologySequence, cohomologyAlpha, cohomologyRestriction, modelSequence, e]
    apply biprod.hom_ext <;> simp [Category.assoc]
  · dsimp [cohomologySequence, cohomologyBeta, cohomologyRestriction, modelSequence, e]
    apply biprod.hom_ext' <;> simp [Category.assoc]

lemma cohomologySequence_exact (M : Modules R) (n : ℕ) :
    (cohomologySequence R V W m hS M n).Exact :=
  ComposableArrows.exact_of_iso (cohomologySequenceIso R V W m hS M n).symm
    ((modelExact R V W (m M).complex (m M).injective).choose_spec (n : ℤ))

end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris
open AdvancedHomologicalAlgebra.MayerVietorisData
open TransportHelpers
variable {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X)
  (m : ∀ M : Modules R, ResolutionModel R M)

lemma cohomologyRestriction_naturality
    (T S : Opens X) (hT : T ≤ V ⊔ W) (hS : S ≤ V ⊔ W) (h : S ≤ T)
    (M N : Modules R) (f : M ⟶ N) (n : ℕ) :
    (localCohomology R (V ⊔ W) T hT n).map f ≫
      cohomologyRestriction R V W m T S hT hS h N n =
    cohomologyRestriction R V W m T S hT hS h M n ≫
      (localCohomology R (V ⊔ W) S hS n).map f := by
  letI := (m M).bounded
  letI := (m N).bounded
  obtain ⟨φ, ⟨H⟩, _⟩ := resolutionLifts R M N (m M).complex (m N).complex
    (m M).augmentation (m N).augmentation
    (m M).quasiIso (m N).quasiIso (m N).injective f
  exact transport_naturality
    (cohomologyComparison R V W m T hT M n)
    (cohomologyComparison R V W m S hS M n)
    (cohomologyComparison R V W m T hT N n)
    (cohomologyComparison R V W m S hS N n)
    ((localCohomology R (V ⊔ W) T hT n).map f)
    ((localCohomology R (V ⊔ W) S hS n).map f) _ _ _ _
    (canonicalModelIso_naturality R (V ⊔ W) T hT M N _ _
      (m M).bounded (m N).bounded _ _ (m M).quasiIso (m N).quasiIso
      (m M).injective (m N).injective f φ H n)
    (canonicalModelIso_naturality R (V ⊔ W) S hS M N _ _
      (m M).bounded (m N).bounded _ _ (m M).quasiIso (m N).quasiIso
      (m M).injective (m N).injective f φ H n)
    (modelRestriction_naturality R (V ⊔ W) T S hT hS h _ _ φ (n : ℤ))

lemma cohomologyAlpha_naturality (M N : Modules R) (f : M ⟶ N) (n : ℕ) :
    (localCohomology R (V ⊔ W) (V ⊔ W) le_rfl n).map f ≫
      cohomologyAlpha R V W m N n =
    cohomologyAlpha R V W m M n ≫
      biprod.map ((localCohomology R (V ⊔ W) V le_sup_left n).map f)
        ((localCohomology R (V ⊔ W) W le_sup_right n).map f) := by
  apply biprod.hom_ext
  · simpa only [Category.assoc, cohomologyAlpha, biprod.lift_fst,
      biprod.lift_fst_assoc, biprod.map_fst, biprod.lift_fst_assoc] using
      cohomologyRestriction_naturality R V W m (V ⊔ W) V le_rfl le_sup_left le_sup_left M N f n
  · simpa only [Category.assoc, cohomologyAlpha, biprod.lift_snd,
      biprod.lift_snd_assoc, biprod.map_snd, biprod.lift_snd_assoc] using
      cohomologyRestriction_naturality R V W m (V ⊔ W) W le_rfl le_sup_right le_sup_right M N f n

lemma cohomologyBeta_naturality (M N : Modules R) (f : M ⟶ N) (n : ℕ) :
    biprod.map ((localCohomology R (V ⊔ W) V le_sup_left n).map f)
        ((localCohomology R (V ⊔ W) W le_sup_right n).map f) ≫
      cohomologyBeta R V W m N n =
    cohomologyBeta R V W m M n ≫
      (localCohomology R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) n).map f := by
  apply biprod.hom_ext'
  · simpa only [cohomologyBeta, biprod.inl_map_assoc, biprod.inl_desc,
      biprod.inl_desc_assoc, Category.assoc] using
      cohomologyRestriction_naturality R V W m V (V ⊓ W) le_sup_left
        (inf_le_left.trans le_sup_left) inf_le_left M N f n
  · simpa only [cohomologyBeta, biprod.inr_map_assoc, biprod.inr_desc,
      biprod.inr_desc_assoc, Category.assoc, Preadditive.comp_neg, Preadditive.neg_comp] using
      congrArg Neg.neg (cohomologyRestriction_naturality R V W m W (V ⊓ W) le_sup_right
        (inf_le_left.trans le_sup_left) inf_le_right M N f n)

variable (hS : ∀ M : Modules R, (complexRow R V W (m M).complex).ShortExact)

lemma cohomologyDelta_naturality (M N : Modules R) (f : M ⟶ N) (n : ℕ) :
    (localCohomology R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) n).map f ≫
      cohomologyDelta R V W m hS N n =
    cohomologyDelta R V W m hS M n ≫
      (localCohomology R (V ⊔ W) (V ⊔ W) le_rfl (n + 1)).map f := by
  letI := (m M).bounded
  letI := (m N).bounded
  obtain ⟨φ, ⟨H⟩, _⟩ := resolutionLifts R M N (m M).complex (m N).complex
    (m M).augmentation (m N).augmentation
    (m M).quasiIso (m N).quasiIso (m N).injective f
  exact transport_naturality
    (cohomologyComparison R V W m (V ⊓ W) (inf_le_left.trans le_sup_left) M n)
    (cohomologyComparison R V W m (V ⊔ W) le_rfl M (n + 1))
    (cohomologyComparison R V W m (V ⊓ W) (inf_le_left.trans le_sup_left) N n)
    (cohomologyComparison R V W m (V ⊔ W) le_rfl N (n + 1))
    ((localCohomology R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) n).map f)
    ((localCohomology R (V ⊔ W) (V ⊔ W) le_rfl (n + 1)).map f) _ _ _ _
    (canonicalModelIso_naturality R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) M N _ _
      (m M).bounded (m N).bounded _ _ (m M).quasiIso (m N).quasiIso
      (m M).injective (m N).injective f φ H n)
    (canonicalModelIso_naturality R (V ⊔ W) (V ⊔ W) le_rfl M N _ _
      (m M).bounded (m N).bounded _ _ (m M).quasiIso (m N).quasiIso
      (m M).injective (m N).injective f φ H (n + 1))
    (naturality R V W _ _ (m M).injective (m N).injective (hS M) (hS N) φ (n : ℤ)).symm

end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris
variable {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X)
    (m : ∀ M : Modules R, ResolutionModel R M)
    (hS : ∀ M : Modules R, (complexRow R V W (m M).complex).ShortExact)

include hS in
lemma cohomologyAlpha_zero_mono (M : Modules R) :
    Mono (cohomologyAlpha R V W m M 0) := by
  letI := (m M).bounded
  haveI := modelDegreeZeroMono R V W (m M).complex (hS M)
  have hmodel : (modelSequence R V W (m M).complex (hS M) 0).map' 0 1 ≫
      (middleIso R V W (m M).complex 0).inv =
      HomologicalComplex.homologyMap (complexRow R V W (m M).complex).f 0 := by
    simpa [modelSequenceIso, HomologicalComplex.HomologySequence.composableArrows₅] using
      ComposableArrows.naturality' (modelSequenceIso R V W (m M).complex (hS M) 0).hom 0 1
  haveI : Mono ((modelSequence R V W (m M).complex (hS M) 0).map' 0 1) :=
    mono_of_mono_fac hmodel
  have hcoh := ComposableArrows.naturality'
    (cohomologySequenceIso R V W m hS M 0).hom 0 1
  have : Mono ((cohomologySequence R V W m hS M 0).map' 0 1) :=
    mono_of_mono_fac hcoh
  exact this
end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris
variable {X : TopCat.{u}} (R : RingSheaf X) (V W : Opens X)
  (m : ∀ M : Modules R, ResolutionModel R M)
  (hS : ∀ M : Modules R, (complexRow R V W (m M).complex).ShortExact)

/-- Removing the identity restriction of scalars changes no arrows. -/
def directSequenceIso (M : Modules R) (n : ℕ) :
    directSequence R V W m hS M n ≅ cohomologySequence R V W m hS M n := by
  refine ComposableArrows.isoMk₅
    ((sameOpenCohomologyIso R (V ⊔ W) n).symm.app M) (Iso.refl _) (Iso.refl _)
    ((sameOpenCohomologyIso R (V ⊔ W) (n + 1)).symm.app M) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_ ?_
  · simp [directSequence, cohomologySequence, directAlpha]
  · simp [directSequence, cohomologySequence]
  · simp [directSequence, cohomologySequence, directDelta, localCohomology]
  · simp [directSequence, cohomologySequence, directAlpha]
  · simp [directSequence, cohomologySequence]

lemma directAlpha_naturality (M N : Modules R) (f : M ⟶ N) (n : ℕ) :
    (sectionCohomology R (V ⊔ W) n).map f ≫ directAlpha R V W m N n =
    directAlpha R V W m M n ≫
      biprod.map ((localCohomology R (V ⊔ W) V le_sup_left n).map f)
        ((localCohomology R (V ⊔ W) W le_sup_right n).map f) := by
  have hn : (sectionCohomology R (V ⊔ W) n).map f ≫
      (sameOpenCohomologyIso R (V ⊔ W) n).inv.app N =
      (sameOpenCohomologyIso R (V ⊔ W) n).inv.app M ≫
        (localCohomology R (V ⊔ W) (V ⊔ W) le_rfl n).map f := by
    simpa only [localCohomology] using (sameOpenCohomologyIso R (V ⊔ W) n).inv.naturality f
  dsimp only [directAlpha]
  rw [← Category.assoc, hn, Category.assoc, cohomologyAlpha_naturality]
  simp [Category.assoc]

lemma directDelta_naturality (M N : Modules R) (f : M ⟶ N) (n : ℕ) :
    (localCohomology R (V ⊔ W) (V ⊓ W) (inf_le_left.trans le_sup_left) n).map f ≫
      directDelta R V W m hS N n =
    directDelta R V W m hS M n ≫ (sectionCohomology R (V ⊔ W) (n + 1)).map f := by
  have hn : (localCohomology R (V ⊔ W) (V ⊔ W) le_rfl (n + 1)).map f ≫
      (sameOpenCohomologyIso R (V ⊔ W) (n + 1)).hom.app N =
      (sameOpenCohomologyIso R (V ⊔ W) (n + 1)).hom.app M ≫
        (sectionCohomology R (V ⊔ W) (n + 1)).map f := by
    simpa only [localCohomology] using
      (sameOpenCohomologyIso R (V ⊔ W) (n + 1)).hom.naturality f
  dsimp only [directDelta]
  rw [← Category.assoc, cohomologyDelta_naturality, Category.assoc, hn]
  simp [Category.assoc]

end AdvancedHomologicalAlgebra.MayerVietoris

namespace AdvancedHomologicalAlgebra.MayerVietoris

/-- The natural Mayer–Vietoris sequence on HA-H01 cohomology, including its
initial zero, for every ringed space and every pair of opens. -/
theorem naturalLongExact : naturalLongExactType.{u} := by
  intro X R V W
  have hm : ∀ M : Modules R, Nonempty (ResolutionModel R M) := by
    intro M
    obtain ⟨I, ι, _, hι, hI, hb⟩ := InjectiveComplexReplacement.replacement
      (Modules R) ((CochainComplex.singleFunctor (Modules R) 0).obj M) 0 (by infer_instance)
    exact ⟨⟨I, hb, ι, hι, hI⟩⟩
  let m : ∀ M : Modules R, ResolutionModel R M := fun M => Classical.choice (hm M)
  let hS : ∀ M : Modules R, (complexRow R V W (m M).complex).ShortExact :=
    fun M => complexesExact R V W (m M).complex (m M).injective
  refine ⟨m, hS, ?_, ?_, ?_⟩
  · intro M
    haveI := cohomologyAlpha_zero_mono R V W m hS M
    dsimp only [directAlpha]
    infer_instance
  · intro M n
    exact ComposableArrows.exact_of_iso (directSequenceIso R V W m hS M n).symm
      (cohomologySequence_exact R V W m hS M n)
  · intro M N f n
    exact ⟨directAlpha_naturality R V W m M N f n,
      cohomologyBeta_naturality R V W m M N f n,
      directDelta_naturality R V W m hS M N f n⟩

end AdvancedHomologicalAlgebra.MayerVietoris
