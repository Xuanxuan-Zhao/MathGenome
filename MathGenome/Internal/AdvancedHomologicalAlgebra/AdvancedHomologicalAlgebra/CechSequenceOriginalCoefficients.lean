import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CechToCohomology
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
import Batteries.Tactic.OpenPrivate
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import Mathlib.Algebra.Category.ModuleCat.Subobject
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AdvancedHomologicalAlgebra.Cech AdvancedHomologicalAlgebra.SheafTheory
open AdvancedHomologicalAlgebra.CechOriginal AdvancedHomologicalAlgebra.SheafUniverseTransport

universe u r a v b

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000

namespace AdvancedHomologicalAlgebra.CechSequenceOriginal

variable {X : TopCat.{u}} (R : X.Sheaf RingCat.{r})
variable {U : Opens X} {A : Type v} (c : Cover U A)

/-- Raising the coefficient carrier commutes with the unrestricted tuple product. -/
def orderedCochainLiftEquiv (F : PresheafOfModules.{a} R.obj) (p : ℕ) :
    ULift.{b} (Cochains R F c p) ≃ₗ[sectionRing R U]
      Cochains R ((liftCoefficients.{b,u,r,a} R.obj).obj F) c p where
  toFun s t := ULift.up (s.down t)
  invFun s := ULift.up (fun t ↦ (s t).down)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Use the same full tuple cochains before and after raising coefficient carriers. -/
def orderedCochainLiftIso :
    orderedCochainFunctor.{u,r,a,v} R c ⋙
        (ModuleCat.uliftFunctor.{b,max a v} (sectionRing R U)).mapHomologicalComplex (.up ℕ) ≅
      liftCoefficients.{b,u,r,a} R.obj ⋙ orderedCochainFunctor.{u,r,max a b,v} R c :=
  NatIso.ofComponents (fun F ↦ HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ (orderedCochainLiftEquiv.{u,r,a,v,b} R c F p).toModuleIso) (by
      intro p q hpq
      have h : p + 1 = q := hpq
      subst q
      let S := ModuleCat.uliftFunctor.{b,max a v} (sectionRing R U)
      let L := liftCoefficients.{b,u,r,a} R.obj
      change _ ≫ (orderedCochainComplex.{u,r,max a b,v} R c (L.obj F)).d p (p + 1) =
        S.map ((orderedCochainComplex.{u,r,a,v} R c F).d p (p + 1)) ≫ _
      rw [orderedCochainComplex_d, orderedCochainComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      let e (n : ℕ) := orderedCochainLiftEquiv.{u,r,a,v,b} R c F n
      change differential R (L.obj F) c p (e p s) =
        e (p + 1) (ULift.up (differential R F c p s.down))
      let j : Cochains R F c (p + 1) ≃+ Cochains R (L.obj F) c (p + 1) :=
        (ULift.moduleEquiv (R := sectionRing R U)).symm.toAddEquiv.trans (e (p + 1)).toAddEquiv
      change differential R (L.obj F) c p (e p s) = j (differential R F c p s.down)
      simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
      apply Finset.sum_congr rfl
      intro i _
      rfl)) (by
    intro F G f
    apply HomologicalComplex.hom_ext
    intro p
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    rfl)

abbrev coefficientCochainLinearEquiv := orderedCochainLiftEquiv.{u,r,a,v,max u r} R c

abbrev coefficientCochainIso := orderedCochainLiftIso.{u,r,a,v,max u r} R c

theorem coefficient_carrier_comparison :
    _root_.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.coefficientCarrierComparison.{u,r,a,v} := by
  intro X R U A c
  exact ⟨coefficientCochainIso.{u,r,a,v} R c, fun _ _ _ _ ↦ rfl, fun _ _ ↦ rfl⟩

def cochainLinearEquiv (F : AmbientSheaves.{a} R) (p : ℕ) :
    (cochainComplex.{u,r,a,v} R c F.val).X p ≃ₗ[sectionRing R U]
      (((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj
        (CechToCohomology.cechComplex (liftedRing.{a} R)
          (liftCover.{u,a,r,v} c) ((transport.{a} R).obj F).val)).X p where
  toAddEquiv := cochainComparison.{u,r,a,v} R F c p
  map_smul' s x := InjectiveCechOriginalCoefficients.cochain_scalars.{u,r,a,v} R F c s p x

/-- The chain comparison is the prescribed full product of section identifications. -/
def cochainIso (F : AmbientSheaves.{a} R) :
    cochainComplex.{u,r,a,v} R c F.val ≅
      ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj
        (CechToCohomology.cechComplex (liftedRing.{a} R)
          (liftCover.{u,a,r,v} c) ((transport.{a} R).obj F).val) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ (cochainLinearEquiv.{u,r,a,v} R c F p).toModuleIso) (by
      intro p q hpq
      have h : p + 1 = q := hpq
      subst q
      change _ ≫ (originalScalars.{u,r,a,v} R c).map
        ((CechToCohomology.cechComplex (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
          ((transport.{a} R).obj F).val).d p (p + 1)) = _
      rw [cochainComplex_d, CechToCohomology.cechComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact (InjectiveCechOriginalCoefficients.cochain_comparison.{u,r,a,v} R F c).2 p s |>.symm)

theorem cochains_transport :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.cochainsTransport.{u,r,a,v} := by
  intro X R U A c F
  exact ⟨cochainIso.{u,r,a,v} R c F, fun _ _ ↦ rfl⟩

open private sectionAt_map from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.InjectiveCechOriginalCoefficients

lemma cochainIso_naturality {F G : AmbientSheaves.{a} R} (f : F ⟶ G) :
    cochainMap.{u,r,a,v} R c f.val ≫ (cochainIso.{u,r,a,v} R c G).hom =
      (cochainIso.{u,r,a,v} R c F).hom ≫ ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).map
        (CechToCohomology.cochainComplexMap (liftedRing.{a} R)
          (liftCover.{u,a,r,v} c) ((transport.{a} R).map f).val) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext t
  exact sectionAt_map.{u,r,a} R f _ _ (liftCover_tuple.{u,r,a,v} c t) (s t)

/-- The comparison of both differentials uses the same component on each tuple. -/
def doubleIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    doubleComplex.{u,r,a,v} R c K ≅
      (mapDouble (originalScalars.{u,r,a,v} R c)).obj (raisedDouble.{u,r,a,v} R c K) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p ↦
    HomologicalComplex.Hom.isoOfComponents (fun q ↦
      (cochainLinearEquiv.{u,r,a,v} R c (K.X q) p).toModuleIso) ?_) ?_
  · intro q q' _
    exact congrArg (fun f ↦ f.f p) (cochainIso_naturality.{u,r,a,v} R c (K.d q q')).symm
  · intro p p' _
    apply HomologicalComplex.hom_ext
    intro q
    change (cochainIso.{u,r,a,v} R c (K.X q)).hom.f p ≫
       (originalScalars.{u,r,a,v} R c).map ((CechToCohomology.cechComplex
          (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ((transport.{a} R).obj (K.X q)).val).d p p') =
       (cochainComplex.{u,r,a,v} R c (K.X q).val).d p p' ≫
         (cochainIso.{u,r,a,v} R c (K.X q)).hom.f p'
    exact (cochainIso.{u,r,a,v} R c (K.X q)).hom.comm p p' 

theorem double_transport :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.doubleTransport.{u,r,a,v} := by
  intro X R U A c K
  exact ⟨doubleIso.{u,r,a,v} R c K, fun _ _ _ ↦ rfl⟩

private lemma sectionAt_smul (M : AmbientSheaves.{a} R) {V : Opens X}
    {W : Opens (liftedSpace.{max a u r} X)} (h : opensEquiv X W = V)
    (b : sectionRing R V) (s : M.val.obj (op V)) :
    sectionAt.{u,r,a} R M W V h (b • s) =
      ringAt.{u,r,a} R W V h b • sectionAt.{u,r,a} R M W V h s := by
  subst V
  rfl

private def liftedSectionLinearEquiv (K : CochainComplex (AmbientSheaves.{a} R) ℕ) (q : ℕ) :
    (liftedSections.{u,r,a,v} R c K).X q ≃ₗ[sectionRing R U]
      (((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj (raisedLiftedSections.{u,r,a,v} R c K)).X q where
  toFun s := ULift.up (sectionAtCover.{u,r,a} R (U := U) (K.X q) s.down)
  invFun s := ULift.up ((sectionAtCover.{u,r,a} R (U := U) (K.X q)).symm s.down)
  left_inv s := ULift.ext ((sectionAtCover.{u,r,a} R (U := U) (K.X q)).symm_apply_apply s.down)
  right_inv s := ULift.ext ((sectionAtCover.{u,r,a} R (U := U) (K.X q)).apply_symm_apply s.down)
  map_add' s t := congrArg ULift.up (map_add (sectionAtCover.{u,r,a} R (U := U) (K.X q)) s.down t.down)
  map_smul' b s := congrArg ULift.up (sectionAt_smul.{u,r,a} R (K.X q)
    ((opensEquiv.{max a u r} X).apply_symm_apply U) b s.down)

private def liftedSectionsIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    liftedSections.{u,r,a,v} R c K ≅
      ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj (raisedLiftedSections.{u,r,a,v} R c K) :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦ (liftedSectionLinearEquiv.{u,r,a,v} R c K q).toModuleIso) (by
    intro q q' _
    apply ModuleCat.hom_ext
    ext ⟨s⟩ : 1
    exact congrArg ULift.up (sectionAt_map.{u,r,a} R (K.d q q') _ _
      ((opensEquiv.{max a u r} X).apply_symm_apply U) s).symm)

theorem augmentations_transport :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.augmentationTransport.{u,r,a,v} := by
  intro X R U A c M J
  refine ⟨doubleIso.{u,r,a,v} R c J.cocomplex, liftedSectionsIso.{u,r,a,v} R c J.cocomplex, cochainIso.{u,r,a,v} R c M,
    fun _ _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl, ?_, ?_⟩
  · apply HomologicalComplex.hom_ext
    intro q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨s⟩
    exact (InjectiveCechOriginalCoefficients.cochain_comparison.{u,r,a,v}
      R (J.cocomplex.X q) c).1 s
  · exact cochainIso_naturality.{u,r,a,v} R c (J.ι.f 0)

lemma raisedResolution_ι_zero {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    (raisedResolution.{u,r,a} R J).ι.f 0 = (transport.{a} R).map (J.ι.f 0) := by
  simp only [raisedResolution, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Functor.mapHomologicalComplex_map_f]
  rfl

section ExactProducts

variable {S : Type r} [Ring S] (J : Type v)

/-- Take the full product of a family of modules, allowing the ring, the
carriers, and the indexing type to have independent universes. -/
private def fullProduct :
    (Discrete J ⥤ ModuleCat.{a} S) ⥤ ModuleCat.{max a v} S where
  obj F := ModuleCat.of S (∀ j : J, F.obj ⟨j⟩)
  map f := ModuleCat.ofHom (LinearMap.pi fun j ↦ (f.app ⟨j⟩).hom.comp (LinearMap.proj j))

private instance : (fullProduct.{r,a,v} (S := S) J).Additive where
  map_add := by intros; ext; rfl

private instance : (fullProduct.{r,a,v} (S := S) J).PreservesHomology := by
  apply ((Functor.exact_tfae _).out 2 3).1
  intro C hC
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro z hz
  have component (j : J) : ∃ x : C.X₁.obj ⟨j⟩, C.f.app ⟨j⟩ x = z j :=
    (ShortComplex.moduleCat_exact_iff _).1 (hC.map ((evaluation _ _).obj ⟨j⟩))
      (z j) (congrFun hz j)
  choose x hx using component
  exact ⟨x, funext hx⟩

private instance : PreservesFiniteLimits (fullProduct.{r,a,v} (S := S) J) :=
  Functor.preservesFiniteLimits_of_preservesHomology _

private instance : PreservesFiniteColimits (fullProduct.{r,a,v} (S := S) J) :=
  Functor.preservesFiniteColimits_of_preservesHomology _

end ExactProducts

private def tupleDiagram (p : ℕ) : AmbientPresheaves.{a} R ⥤
    Discrete (Fin (p + 1) → A) ⥤ ModuleCat.{max a u r} (sectionRing R U) where
  obj F := Discrete.functor fun t ↦ localSections R F U (tupleOpen c t) (tupleOpen_le c t)
  map f := Discrete.natTrans fun t ↦
    (ModuleCat.restrictScalars (R.obj.map (homOfLE (tupleOpen_le c t.as)).op).hom).map
      (f.app (op (tupleOpen c t.as)))

private instance (p : ℕ) : PreservesFiniteLimits (tupleDiagram.{u,r,a,v} R c p) where
  preservesFiniteLimits J _ _ := by
    apply preservesLimitsOfShape_of_evaluation
    intro t
    let f := (R.obj.map (homOfLE (tupleOpen_le c t.as)).op).hom
    let F := ModuleCat.restrictScalars.{max a u r} f
    have h : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
      ((Functor.exact_tfae F).out 2 4).1 (ModuleCat.restrictScalars_map_exact.{max a u r} f)
    letI := h.1
    change PreservesLimitsOfShape J
      (PresheafOfModules.evaluation R.obj (op (tupleOpen c t.as)) ⋙ F)
    infer_instance

private instance (p : ℕ) : PreservesFiniteColimits (tupleDiagram.{u,r,a,v} R c p) where
  preservesFiniteColimits J _ _ := by
    apply preservesColimitsOfShape_of_evaluation
    intro t
    let f := (R.obj.map (homOfLE (tupleOpen_le c t.as)).op).hom
    let F := ModuleCat.restrictScalars.{max a u r} f
    have h : PreservesFiniteLimits F ∧ PreservesFiniteColimits F :=
      ((Functor.exact_tfae F).out 2 4).1 (ModuleCat.restrictScalars_map_exact.{max a u r} f)
    letI : PreservesColimitsOfShape J F := h.2.preservesFiniteColimits J
    let E := PresheafOfModules.evaluation R.obj (op (tupleOpen c t.as))
    change PreservesColimitsOfShape J (E ⋙ F)
    exact comp_preservesColimitsOfShape E F

instance : PreservesFiniteLimits (cochainFunctor.{u,r,a,v} R c) where
  preservesFiniteLimits J _ _ := by
    apply HomologicalComplex.preservesLimitsOfShape_of_eval
    intro p
    change PreservesLimitsOfShape J
      (tupleDiagram.{u,r,a,v} R c p ⋙ fullProduct.{r,max a u r,v} (S := sectionRing R U) (Fin (p+1) → A))
    infer_instance

instance : PreservesFiniteColimits (cochainFunctor.{u,r,a,v} R c) where
  preservesFiniteColimits J _ _ := by
    apply HomologicalComplex.preservesColimitsOfShape_of_eval
    intro p
    change PreservesColimitsOfShape J
      (tupleDiagram.{u,r,a,v} R c p ⋙ fullProduct.{r,max a u r,v} (S := sectionRing R U) (Fin (p+1) → A))
    infer_instance

theorem cochain_exactness :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.cochainExactness.{u,r,a,v} := by
  intro X R U A c
  infer_instance

open CechToCohomology (ColumnSpectralData columnSpectralData columnSpectralData_firstQuadrant
  natToIntDoubleComplex_finiteDiagonals natToIntDoubleComplex_inQuadrant
  natToIntDoubleComplexVerticalHomologyIso verticalHomologyNatIso
  natToIntDoubleComplexVerticalHomologyIso_hom_f mapHomologyIso_comp_hom)
open DoubleComplexFirstPages (page verticalHomology)

section HorizontalAugmentation

private lemma liftedAugmentation_closed (F : AmbientPresheaves.{a} R) :
    liftedAugmentation.{u,r,a,v} R c F ≫ (cochainComplex.{u,r,a,v} R c F).d 0 1 = 0 := by
  rw [cochainComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  change differential R F c 0 (augmentation R F c s.down) = 0
  exact congr($(CechCochains.augmentation_closed R F c) s.down)

private def augmentedRow (M : AmbientSheaves.{a} R) :
    (CochainComplex.single₀ (CochainModules.{u,r,a,v} R (U := U))).obj
        ((sectionLift.{u,r,a,v} R c).obj (M.val.obj (op U))) ⟶
      cochainComplex.{u,r,a,v} R c M.val :=
  HomologicalComplex.mkHomFromSingle (j := 0) (liftedAugmentation.{u,r,a,v} R c M.val)
    (fun q hq ↦ by
      have h : 0 + 1 = q := hq
      subst q
      exact liftedAugmentation_closed.{u,r,a,v} R c M.val)

private lemma augmentedRow_quasiIso (M : AmbientSheaves.{a} R) [Injective M] :
    QuasiIso (augmentedRow.{u,r,a,v} R c M) := by
  obtain ⟨ha, hz, hp⟩ :=
    InjectiveCechOriginalCoefficients.injective_exact.{u,r,a,v} R c M inferInstance
  rw [quasiIso_iff]
  intro q
  cases q with
  | zero =>
    rw [quasiIsoAt_iff]
    let f := (HomologicalComplex.shortComplexFunctor _ (.up ℕ) 0).map (augmentedRow.{u,r,a,v} R c M)
    change ShortComplex.QuasiIso f
    rw [ShortComplex.quasiIso_iff_of_zeros f (by simp) (by simp) (by simp)]
    constructor
    · apply (ShortComplex.moduleCat_exact_iff _).2
      intro z hz'
      change (cochainComplex.{u,r,a,v} R c M.val).d 0 ((ComplexShape.up ℕ).next 0) z = 0 at hz'
      rw [CochainComplex.next, cochainComplex_d] at hz'
      obtain ⟨s, hs⟩ := hz z hz'
      exact ⟨ULift.up s, hs⟩
    · apply (ModuleCat.mono_iff_injective _).2
      intro s t h
      exact ULift.ext (ha h)
  | succ q =>
    apply (quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj _ q)).2
    apply (HomologicalComplex.exactAt_iff' _ q (q + 1) (q + 2) (by simp) (by simp)).2
    apply (ShortComplex.moduleCat_exact_iff _).2
    intro z hz'
    change (cochainComplex.{u,r,a,v} R c M.val).d (q + 1) (q + 2) z = 0 at hz'
    rw [cochainComplex_d] at hz'
    obtain ⟨y, hy⟩ := hp q z hz'
    refine ⟨y, ?_⟩
    change (cochainComplex.{u,r,a,v} R c M.val).d q (q + 1) y = z
    rwa [cochainComplex_d]

open DoubleTotalization
open CechToCohomology (natToIntDoubleComplexRowIso natToIntDoubleComplexRowIso_hom_f)

private abbrev embedding := ComplexShape.embeddingUpIntGE 0

private lemma intHorizontal_closed (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (q p : ℤ) (hp : (ComplexShape.up ℤ).Rel 0 p) :
    (intHorizontalAugmentation.{u,r,a,v} R c K).f q ≫
      ((doubleComplexInt.{u,r,a,v} R c K).d 0 p).f q = 0 := by
  have h : 0 + 1 = p := hp
  subst p
  let D := doubleComplex.{u,r,a,v} R c K
  let E := ((embedding.extendFunctor _).mapHomologicalComplex (.up ℕ)).obj D
  have hz : horizontalAugmentation.{u,r,a,v} R c K ≫ D.d 0 1 = 0 :=
    HomologicalComplex.hom_ext _ _ (fun i ↦ liftedAugmentation_closed.{u,r,a,v} R c (K.X i).val)
  have he : intHorizontalAugmentation.{u,r,a,v} R c K ≫
      (doubleComplexInt.{u,r,a,v} R c K).d 0 (0 + 1) = 0 := by
    change (HomologicalComplex.extendMap (horizontalAugmentation.{u,r,a,v} R c K) embedding ≫
      (E.extendXIso embedding (by simp [embedding] : embedding.f 0 = 0)).inv) ≫
        (E.extend embedding).d 0 1 = 0
    rw [E.extend_d_eq embedding
      (by simp [embedding] : embedding.f 0 = 0) (by simp [embedding] : embedding.f 1 = 1)]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    change HomologicalComplex.extendMap _ embedding ≫
      HomologicalComplex.extendMap (D.d 0 1) embedding ≫ _ = 0
    rw [← Category.assoc, ← HomologicalComplex.extendMap_comp, hz,
      HomologicalComplex.extendMap_zero, zero_comp]
  exact congrArg (fun f => f.f q) he

private def intAugmentedRow (K : CochainComplex (AmbientSheaves.{a} R) ℕ) (q : ℤ) :
    (HomologicalComplex.single (CochainModules.{u,r,a,v} R (U := U)) (.up ℤ) 0).obj
        ((intSections.{u,r,a,v} R c K).X q) ⟶ (doubleComplexInt.{u,r,a,v} R c K).flip.X q :=
  HomologicalComplex.mkHomFromSingle (j := 0)
    ((intHorizontalAugmentation.{u,r,a,v} R c K).f q) (intHorizontal_closed.{u,r,a,v} R c K q)

private lemma intHorizontal_rowIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) (q : ℕ) :
    let hq : embedding.f q = (q : ℤ) := by simp [embedding]
    let h0 : embedding.f (0 : ℕ) = (0 : ℤ) := by simp [embedding]
    (intHorizontalAugmentation.{u,r,a,v} R c K).f (q : ℤ) ≫
      (natToIntDoubleComplexRowIso (doubleComplex.{u,r,a,v} R c K) q).hom.f 0 =
    ((liftedSections.{u,r,a,v} R c K).extendXIso embedding hq).hom ≫
      liftedAugmentation.{u,r,a,v} R c (K.X q).val ≫
      ((cochainComplex.{u,r,a,v} R c (K.X q).val).extendXIso embedding h0).inv := by
  dsimp only
  apply (cancel_mono ((cochainComplex.{u,r,a,v} R c (K.X q).val).extendXIso
    embedding (by simp [embedding] : embedding.f 0 = 0)).hom).1
  rw [Category.assoc]
  erw [natToIntDoubleComplexRowIso_hom_f (doubleComplex.{u,r,a,v} R c K) 0 q]
  change (intHorizontalAugmentation.{u,r,a,v} R c K).f (q : ℤ) ≫
    (zeroColumnIso.{u,r,a,v} R c K).hom.f (q : ℤ) ≫
    (((doubleComplex.{u,r,a,v} R c K).X 0).extendXIso
      embedding (by simp [embedding] : embedding.f q = (q : ℤ))).hom = _
  have h : intHorizontalAugmentation.{u,r,a,v} R c K ≫ (zeroColumnIso.{u,r,a,v} R c K).hom =
      HomologicalComplex.extendMap (horizontalAugmentation.{u,r,a,v} R c K) embedding := by
    simp [intHorizontalAugmentation]
  have hq := congrArg (fun f => f.f (q : ℤ)) h
  simp only [HomologicalComplex.comp_f] at hq
  rw [← Category.assoc, hq, HomologicalComplex.extendMap_f _ _ (by simp [embedding] :
    embedding.f q = (q : ℤ))]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

private lemma intAugmentedRow_comp (K : CochainComplex (AmbientSheaves.{a} R) ℕ) (q : ℕ) :
    intAugmentedRow.{u,r,a,v} R c K (q : ℤ) ≫
        (natToIntDoubleComplexRowIso (doubleComplex.{u,r,a,v} R c K) q).hom =
      (HomologicalComplex.single (CochainModules.{u,r,a,v} R (U := U)) (.up ℤ) 0).map
        (((liftedSections.{u,r,a,v} R c K).extendXIso embedding
          (by simp [embedding] : embedding.f q = (q : ℤ))).hom) ≫
      (HomologicalComplex.extendSingleIso embedding
        ((sectionLift.{u,r,a,v} R c).obj ((K.X q).val.obj (op U))) 0 0 (by simp [embedding])).inv ≫
      HomologicalComplex.extendMap (augmentedRow.{u,r,a,v} R c (K.X q)) embedding := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [intAugmentedRow, HomologicalComplex.comp_f, HomologicalComplex.mkHomFromSingle_f,
    HomologicalComplex.single_map_f_self, HomologicalComplex.extendSingleIso_inv_f,
    HomologicalComplex.extendMap_f _ _ (by simp [embedding] : embedding.f 0 = 0)]
  rw [Category.assoc, intHorizontal_rowIso]
  simp only [augmentedRow, HomologicalComplex.mkHomFromSingle_f, Category.assoc, Iso.inv_hom_id_assoc]
  rfl

private lemma intAugmentedRow_quasiIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (hK : ∀ q, Injective (K.X q)) (q : ℤ) :
    QuasiIso (intAugmentedRow.{u,r,a,v} R c K q) := by
  by_cases hq : 0 ≤ q
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hq
    letI := hK q
    letI := augmentedRow_quasiIso.{u,r,a,v} R c (K.X q)
    apply (quasiIso_iff_comp_right _ (natToIntDoubleComplexRowIso
      (doubleComplex.{u,r,a,v} R c K) q).hom).1
    rw [intAugmentedRow_comp]
    infer_instance
  · have hZ : IsZero ((intSections.{u,r,a,v} R c K).X q) :=
      (liftedSections.{u,r,a,v} R c K).isZero_extend_X embedding q
        (by intro n hn; simp [embedding] at hn; omega)
    have hS := (HomologicalComplex.single (CochainModules.{u,r,a,v} R (U := U)) (.up ℤ) 0).map_isZero hZ
    rw [quasiIso_iff]
    intro p
    apply (quasiIsoAt_iff_isIso_homologyMap _ _).2
    have hT : IsZero (((doubleComplexInt.{u,r,a,v} R c K).flip.X q).homology p) :=
      (HomologicalComplex.ExactAt.of_isZero
        (K := (doubleComplexInt.{u,r,a,v} R c K).flip.X q) (i := p)
        (natToIntDoubleComplex_inQuadrant (doubleComplex.{u,r,a,v} R c K) p q (by omega))).isZero_homology
    exact ((HomologicalComplex.homologyFunctor _ (.up ℤ) p).map_isZero hS).isIso hT _

theorem total_augmentation :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.totalAugmentation.{u,r,a,v} := by
  intro X R U A c M J
  let K := doubleComplex.{u,r,a,v} R c J.cocomplex
  apply AugmentedDoubleComplexComparison.cochain_row_assembly
    (doubleComplexInt.{u,r,a,v} R c J.cocomplex)
    (natToIntDoubleComplex_finiteDiagonals K)
    (fun p q hp ↦ natToIntDoubleComplex_inQuadrant K p q (by omega))
    (intSections.{u,r,a,v} R c J.cocomplex)
    (intHorizontalAugmentation.{u,r,a,v} R c J.cocomplex)
    (intHorizontal_closed.{u,r,a,v} R c J.cocomplex)
  · intro q
    haveI := intAugmentedRow_quasiIso.{u,r,a,v} R c J.cocomplex (fun _ => inferInstance) q
    exact inferInstanceAs (IsIso (HomologicalComplex.homologyMap (intAugmentedRow.{u,r,a,v} R c J.cocomplex q) 0))
  · intro q p hp
    haveI := intAugmentedRow_quasiIso.{u,r,a,v} R c J.cocomplex (fun _ => inferInstance) q
    exact (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0
      ((intSections.{u,r,a,v} R c J.cocomplex).X q) p hp).of_iso
      (asIso (HomologicalComplex.homologyMap (intAugmentedRow.{u,r,a,v} R c J.cocomplex q) p)).symm

end HorizontalAugmentation

variable [EnoughInjectives (AmbientSheaves.{a} R)]

/-- The original bicomplex has finite diagonals and hence the actual column pages. -/
def spectralData {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    ColumnSpectralData (doubleComplexInt.{u,r,a,v} R c J.cocomplex) :=
  columnSpectralData _ (natToIntDoubleComplex_finiteDiagonals (doubleComplex.{u,r,a,v} R c J.cocomplex))

/-- Vertical cohomology with the ordinary alternating differential in the horizontal degree. -/
def verticalIso {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (q : ℕ) :
    verticalHomology (doubleComplexInt.{u,r,a,v} R c J.cocomplex) (q : ℤ) ≅
      localCechComplexInt.{u,r,a,v} R c M q :=
  natToIntDoubleComplexVerticalHomologyIso (doubleComplex.{u,r,a,v} R c J.cocomplex) q ≪≫
    ((ComplexShape.embeddingUpIntGE 0).extendFunctor _).mapIso
      (verticalHomologyNatIso (doubleComplex.{u,r,a,v} R c J.cocomplex) q ≪≫ verticalComparison.{u,r,a,v} R c J q)

lemma verticalIso_component {M : AmbientSheaves.{a} R} (J : InjectiveResolution M)
    (p q : ℕ) :
    (verticalIso.{u,r,a,v} R c J q).hom.f (p : ℤ) ≫
      ((cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)).extendXIso
        (ComplexShape.embeddingUpIntGE 0) (by simp :
          (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))).hom =
      (verticalComponent.{u,r,a,v} R c J p q).hom := by
  rw [verticalIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.comp_f,
    ComplexShape.Embedding.extendFunctor_map]
  rw [HomologicalComplex.extendMap_f _ _ (by simp :
    (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, natToIntDoubleComplexVerticalHomologyIso_hom_f]
  simp only [Category.assoc, verticalComponent, Iso.trans_hom,
    verticalComparison, HomologicalComplex.comp_f, Functor.mapIso_hom]
  let F := cochainFunctor.{u,r,a,v} R c
  let E := HomologicalComplex.eval (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) p
  let S := (underlyingComplex.{u,r,a} R J.cocomplex).sc q
  have he := mapHomologyIso_comp_hom S F E
  simp only [verticalHomologyNatIso, HomologicalComplex.Hom.isoOfComponents_hom_f]
  rw [he]
  rfl

theorem second_page :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.secondPage.{u,r,a,v} := by
  intro X R U A c _ M J
  refine ⟨spectralData.{u,r,a,v} R c J, verticalIso.{u,r,a,v} R c J, fun _ ↦ inferInstance,
    verticalIso_component.{u,r,a,v} R c J, ?_, ?_⟩
  · exact columnSpectralData_firstQuadrant _ _
      (fun p q hpq ↦ natToIntDoubleComplex_inQuadrant (doubleComplex.{u,r,a,v} R c J.cocomplex) p q hpq)
  · intro p q
    exact ⟨secondPageComparison.{u,r,a,v} R c J _ _ p q, rfl⟩

open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (cohomologyValue sectionsValue)
open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomology (resolutionModelMap)
open DoubleTotalization
open CechToCohomology (abutmentPiece_finite columnAbutmentLimitIso
  columnAbutmentLimitIso_representative)

instance sectionModelMap_isIso (V : Opens X) {M : AmbientSheaves.{a} R}
    (J : InjectiveResolution M) (n : ℕ) : IsIso (sectionModelMap.{u,r,a} R V J n) := by
  haveI : IsIso (resolutionModelMap (sectionsValue.{a,u,r} R V) J.ι'
      (by infer_instance) n) :=
    SheafCohomologyOriginalCoefficients.resolution.{a,u,r} R V M J.cochainComplex
      J.ι' (by infer_instance) (fun _ ↦ inferInstance) n
  unfold sectionModelMap
  infer_instance

instance liftedSectionModelMap_isIso {M : AmbientSheaves.{a} R}
    (J : InjectiveResolution M) (n : ℕ) :
    IsIso (liftedSectionModelMap.{u,r,a,v} R c J n) := by
  unfold liftedSectionModelMap
  infer_instance

section LocalSections

attribute [local instance] HasDerivedCategory.standard

open CechToCohomology (mapExtendIso mapExtendXIso natComputationIso natComputationIso_naturality
  intComputationIso intComputationDerivedIso natResolutionPlus natResolutionPlusι)
open private sectionExtendComponent from MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

lemma sectionModelMap_eq (V : Opens X) {M : AmbientSheaves.{a} R}
    (J : InjectiveResolution M) (n : ℕ) :
    sectionModelMap.{u,r,a} R V J n = (natComputationIso (sectionsValue.{a,u,r} R V) M J n).inv := by
  have h : mapExtendIso (sectionsValue.{a,u,r} R V) J.cocomplex ComplexShape.embeddingUpNat =
      sectionExtendIso.{u,r,a} R V J.cocomplex := by
    apply Iso.ext
    apply HomologicalComplex.hom_ext
    intro i
    let e := ComplexShape.embeddingUpNat.r i
    change (mapExtendXIso (sectionsValue.{a,u,r} R V) J.cocomplex e).hom =
      (sectionExtendComponent.{u,r,a} R V J.cocomplex e).hom
    cases e <;> rfl
  simp only [sectionModelMap, natComputationIso, intComputationIso, intComputationDerivedIso,
    h, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
  unfold resolutionModelMap
  simp [natResolutionPlus, natResolutionPlusι, Functor.map_comp, Category.assoc]

lemma sectionModelMap_naturality (V : Opens X) {M N : AmbientSheaves.{a} R}
    (f : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex) (h : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    sectionModelMap.{u,r,a} R V I q ≫ (cohomologyValue.{a,u,r} R V q).map f =
      HomologicalComplex.homologyMap (((sectionsValue.{a,u,r} R V).mapHomologicalComplex (.up ℕ)).map φ) q ≫
        sectionModelMap.{u,r,a} R V J q := by
  rw [sectionModelMap_eq, sectionModelMap_eq]
  apply (cancel_epi (natComputationIso (sectionsValue.{a,u,r} R V) M I q).hom).1
  apply (cancel_mono (natComputationIso (sectionsValue.{a,u,r} R V) N J q).hom).1
  simpa only [cohomologyValue, Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
    using natComputationIso_naturality (sectionsValue.{a,u,r} R V) M N f I J φ h q

@[reassoc]
lemma localEvaluationIso_naturality (V : Opens X) {M N : AmbientSheaves.{a} R}
    (f : M ⟶ N) (I : InjectiveResolution M) (J : InjectiveResolution N)
    (φ : I.cocomplex ⟶ J.cocomplex) (h : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    ((localCohomology.{u,r,a} R q).map f).app (op V) ≫ (localEvaluationIso.{u,r,a} R V J q).hom =
      (localEvaluationIso.{u,r,a} R V I q).hom ≫
        HomologicalComplex.homologyMap (((sectionsValue.{a,u,r} R V).mapHomologicalComplex (.up ℕ)).map φ) q := by
  let E := PresheafOfModules.evaluation R.obj (op V)
  have h₁ := I.isoRightDerivedObj_hom_naturality f J φ h (SheafOfModules.forget R) q
  have h₂ := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map
      (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ)) E
  change (localCohomology.{u,r,a} R q).map f ≫ _ = _ at h₁
  dsimp only [localEvaluationIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  change E.map ((localCohomology.{u,r,a} R q).map f) ≫ (E.map _ ≫ _) =
    (E.map _ ≫ _) ≫ _
  change E.map (HomologicalComplex.homologyMap
      (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ) q) ≫
      (((underlyingComplex.{u,r,a} R J.cocomplex).sc q).mapHomologyIso E).inv =
    (((underlyingComplex.{u,r,a} R I.cocomplex).sc q).mapHomologyIso E).inv ≫
      HomologicalComplex.homologyMap (((sectionsValue.{a,u,r} R V).mapHomologicalComplex (.up ℕ)).map φ) q at h₂
  rw [← Category.assoc, ← Functor.map_comp, h₁, Functor.map_comp, Category.assoc]
  erw [h₂]
  simp only [Category.assoc]
  rfl

/-- Identify the original presheaf of local cohomology with the original
derived sections, using one resolution and the comparison for all lifts. -/
def originalLocalSectionsIso (V : Opens X) (q : ℕ) :
    localCohomology.{u,r,a} R q ⋙ PresheafOfModules.evaluation R.obj (op V) ≅
      cohomologyValue.{a,u,r} R V q :=
  NatIso.ofComponents (fun M ↦ localEvaluationIso.{u,r,a} R V (injectiveResolution M) q ≪≫
    asIso (sectionModelMap.{u,r,a} R V (injectiveResolution M) q)) (by
      intro M N f
      let I := injectiveResolution M
      let J := injectiveResolution N
      let φ := InjectiveResolution.desc f J I
      have h := InjectiveResolution.desc_commutes_zero f J I
      change ((localCohomology.{u,r,a} R q).map f).app (op V) ≫
          (localEvaluationIso.{u,r,a} R V J q).hom ≫ sectionModelMap.{u,r,a} R V J q =
        ((localEvaluationIso.{u,r,a} R V I q).hom ≫ sectionModelMap.{u,r,a} R V I q) ≫
          (cohomologyValue.{a,u,r} R V q).map f
      rw [← Category.assoc, localEvaluationIso_naturality.{u,r,a} R V f I J φ h,
        Category.assoc, ← sectionModelMap_naturality.{u,r,a} R V f I J φ h q,
        Category.assoc])

lemma originalLocalSectionsIso_model (V : Opens X) (q : ℕ) {M : AmbientSheaves.{a} R}
    (J : InjectiveResolution M) :
    (originalLocalSectionsIso.{u,r,a} R V q).hom.app M =
      (localEvaluationIso.{u,r,a} R V J q).hom ≫ sectionModelMap.{u,r,a} R V J q := by
  let I := injectiveResolution M
  let φ := InjectiveResolution.desc (𝟙 M) J I
  have h := InjectiveResolution.desc_commutes_zero (𝟙 M) J I
  have h₁ := localEvaluationIso_naturality.{u,r,a} R V (𝟙 M) I J φ h q
  have h₂ := sectionModelMap_naturality.{u,r,a} R V (𝟙 M) I J φ h q
  have he : (localCohomology.{u,r,a} R q).map (𝟙 M) = 𝟙 _ := CategoryTheory.Functor.map_id _ _
  have hv : (cohomologyValue.{a,u,r} R V q).map (𝟙 M) = 𝟙 _ := CategoryTheory.Functor.map_id _ _
  rw [he] at h₁
  rw [hv] at h₂
  simp only [PresheafOfModules.id_app, Category.id_comp] at h₁
  simp only [Category.comp_id] at h₂
  change (localEvaluationIso.{u,r,a} R V I q).hom ≫ sectionModelMap.{u,r,a} R V I q = _
  rw [h₂, ← Category.assoc, ← h₁]

lemma localEvaluationIso_restriction {W V : Opens X} (j : op W ⟶ op V)
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (q : ℕ) :
    let H := ModuleCat.restrictScalars.{max a u r} (R.obj.map j).hom
    ((localCohomology.{u,r,a} R q).obj M).map j ≫ H.map (localEvaluationIso.{u,r,a} R V J q).hom =
      (localEvaluationIso.{u,r,a} R W J q).hom ≫
        restrictionOnModel.{u,r,a} R j (underlyingComplex.{u,r,a} R J.cocomplex) q := by
  let H := ModuleCat.restrictScalars.{max a u r} (R.obj.map j).hom
  let K := underlyingComplex.{u,r,a} R J.cocomplex
  let E := PresheafOfModules.evaluation R.obj (op V)
  let τ := PresheafOfModules.restriction R.obj j
  have h := congrArg (fun f ↦ f ≫ H.map ((K.sc q).mapHomologyIso E).inv)
    (τ.app_homology (K.sc q))
  simp only [Category.assoc] at h
  have hn := PresheafOfModules.Hom.naturality (J.isoRightDerivedObj (SheafOfModules.forget R) q).hom j
  dsimp only [localEvaluationIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Functor.map_comp, Category.assoc, PresheafOfModules.evaluation_map]
  change ((localCohomology.{u,r,a} R q).obj M).map j ≫ _ = _ at hn
  rw [← Category.assoc, hn, Category.assoc]
  exact congrArg (fun f ↦ (J.isoRightDerivedObj (SheafOfModules.forget R) q).hom.app (op W) ≫ f) h

theorem local_sections :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.localSectionComparison.{u,r,a} := by
  intro X R _
  exact ⟨originalLocalSectionsIso.{u,r,a} R, fun V q _ J ↦ originalLocalSectionsIso_model.{u,r,a} R V q J,
    fun j _ J q ↦ localEvaluationIso_restriction.{u,r,a} R j J q⟩

end LocalSections

/-- The normalized horizontal comparison from the sections of the original model. -/
def totalAugmentationMap {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    intSections.{u,r,a,v} R c J.cocomplex ⟶ sumTotal (doubleComplexInt.{u,r,a,v} R c J.cocomplex) :=
  (total_augmentation.{u,r,a,v} R c M J).choose

instance totalAugmentationMap_quasiIso {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    QuasiIso (totalAugmentationMap.{u,r,a,v} R c J) :=
  (total_augmentation.{u,r,a,v} R c M J).choose_spec.1

omit [EnoughInjectives (AmbientSheaves.{a} R)] in
lemma totalAugmentationMap_f {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℤ) :
    (totalAugmentationMap.{u,r,a,v} R c J).f n =
      (intHorizontalAugmentation.{u,r,a,v} R c J.cocomplex).f n ≫
        sumInjection (doubleComplexInt.{u,r,a,v} R c J.cocomplex) 0 n n (zero_add n) :=
  (total_augmentation.{u,r,a,v} R c M J).choose_spec.2 n

def abutmentIso {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℕ) :
    (sumTotal (doubleComplexInt.{u,r,a,v} R c J.cocomplex)).homology (n : ℤ) ≅
      (sectionLift.{u,r,a,v} R c).obj ((cohomologyValue.{a,u,r} R U n).obj M) :=
  (asIso (HomologicalComplex.homologyMap (totalAugmentationMap.{u,r,a,v} R c J) (n : ℤ))).symm ≪≫
    asIso (liftedSectionModelMap.{u,r,a,v} R c J n)

theorem abutment :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.abutment.{u,r,a,v} := by
  intro X R U A c _ M J
  let D := spectralData.{u,r,a,v} R c J
  let e := abutmentIso.{u,r,a,v} R c J
  refine ⟨D, totalAugmentationMap.{u,r,a,v} R c J, e, inferInstance,
    totalAugmentationMap_f.{u,r,a,v} R c J, ?_, ?_, ?_⟩
  · intro n
    dsimp [e, abutmentIso]
    simp
  · intro n
    exact abutmentPiece_finite D.filtration (n : ℤ) (e n) D.converges.target
  · intro n r p h
    exact ⟨columnAbutmentLimitIso D (n : ℤ) (e n) r p h,
      columnAbutmentLimitIso_representative D (n : ℤ) (e n) r p h⟩

section PageMaps

open CechToCohomology (columnFilteredMap columnFilteredMap_hom columnPageMapData
  columnPageMap_lift_independent columnPageMap_id columnPageMap_comp
  natToIntDoubleComplexMap_id natToIntDoubleComplexMap_comp natToIntDoubleComplexMap_homology_eq)

variable {M N L : AmbientSheaves.{a} R} (I : InjectiveResolution M)
  (J : InjectiveResolution N) (K : InjectiveResolution L)

private lemma doubleComplexIntMap_id (B : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    doubleComplexIntMap.{u,r,a,v} R c (𝟙 B) = 𝟙 _ := by
  simp [doubleComplexIntMap, doubleComplexMap, doubleComplexInt, doubleComplex]

private lemma doubleComplexIntMap_comp (φ : I.cocomplex ⟶ J.cocomplex)
    (ψ : J.cocomplex ⟶ K.cocomplex) :
    doubleComplexIntMap.{u,r,a,v} R c (φ ≫ ψ) =
      doubleComplexIntMap.{u,r,a,v} R c φ ≫ doubleComplexIntMap.{u,r,a,v} R c ψ := by
  simp [doubleComplexIntMap, doubleComplexMap]

/-- A filtered map on the actual column filtration of the signed total. -/
def filteredMap (φ : I.cocomplex ⟶ J.cocomplex) :=
  columnFilteredMap (spectralData.{u,r,a,v} R c I) (spectralData.{u,r,a,v} R c J)
    (doubleComplexIntMap.{u,r,a,v} R c φ)

def pageMap (φ : I.cocomplex ⟶ J.cocomplex) :=
  columnPageMapData (spectralData.{u,r,a,v} R c I) (spectralData.{u,r,a,v} R c J)
    (doubleComplexIntMap.{u,r,a,v} R c φ)

lemma pageMap_id (r p n : ℤ) (h : 0 ≤ r) :
    (pageMap.{u,r,a,v} R c I I (𝟙 _)).map r p n = 𝟙 _ := by
  unfold pageMap
  rw [doubleComplexIntMap_id]
  exact columnPageMap_id _ r p n

lemma pageMap_comp (φ : I.cocomplex ⟶ J.cocomplex) (ψ : J.cocomplex ⟶ K.cocomplex)
    (r p n : ℤ) (h : 0 ≤ r) :
    (pageMap.{u,r,a,v} R c I K (φ ≫ ψ)).map r p n =
      (pageMap.{u,r,a,v} R c I J φ).map r p n ≫ (pageMap.{u,r,a,v} R c J K ψ).map r p n := by
  unfold pageMap
  rw [doubleComplexIntMap_comp.{u,r,a,v} R c I J K φ ψ]
  exact columnPageMap_comp _ _ _ _ _ r p n

lemma pageMap_lift_independent (f : M ⟶ N) (φ ψ : I.cocomplex ⟶ J.cocomplex)
    (hf : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (hg : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0)
    (r p n : ℤ) (hr : 1 ≤ r) :
    (pageMap.{u,r,a,v} R c I J φ).map r p n = (pageMap.{u,r,a,v} R c I J ψ).map r p n := by
  apply columnPageMap_lift_independent _ _ _ _ _ r hr p n
  apply natToIntDoubleComplexMap_homology_eq
  intro p q
  have h : Homotopy φ ψ := by
    apply InjectiveResolution.descHomotopy f
    · apply HomologicalComplex.from_single_hom_ext
      simpa using hf
    · apply HomologicalComplex.from_single_hom_ext
      simpa using hg
  let F := SheafOfModules.forget R ⋙ cochainFunctor.{u,r,a,v} R c ⋙
    HomologicalComplex.eval (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) p
  exact (Functor.mapHomotopy F h).homologyMap_eq q

lemma pageMap_isIso (J : InjectiveResolution M) (φ : I.cocomplex ⟶ J.cocomplex)
    (h : I.ι.f 0 ≫ φ.f 0 = J.ι.f 0) (r p n : ℤ) (hr : 1 ≤ r) :
    IsIso ((pageMap.{u,r,a,v} R c I J φ).map r p n) := by
  let ψ := InjectiveResolution.desc (𝟙 M) I J
  have hψ : J.ι.f 0 ≫ ψ.f 0 = I.ι.f 0 := by
    simpa only [Category.id_comp, ψ] using InjectiveResolution.desc_commutes_zero (𝟙 M) I J
  have h₁ : I.ι.f 0 ≫ (φ ≫ ψ).f 0 = (𝟙 M) ≫ I.ι.f 0 := by
    simp only [HomologicalComplex.comp_f, ← Category.assoc, h, hψ, Category.id_comp]
  have h₂ : J.ι.f 0 ≫ (ψ ≫ φ).f 0 = (𝟙 M) ≫ J.ι.f 0 := by
    simp only [HomologicalComplex.comp_f, ← Category.assoc, h, hψ, Category.id_comp]
  refine ⟨⟨(pageMap.{u,r,a,v} R c J I ψ).map r p n, ?_, ?_⟩⟩
  · rw [← pageMap_comp.{u,r,a,v} R c I J I φ ψ r p n (by omega),
      pageMap_lift_independent.{u,r,a,v} R c I I (𝟙 M) (φ ≫ ψ) (𝟙 _) h₁ (by simp) r p n hr]
    exact pageMap_id.{u,r,a,v} R c I r p n (by omega)
  · rw [← pageMap_comp.{u,r,a,v} R c J I J ψ φ r p n (by omega),
      pageMap_lift_independent.{u,r,a,v} R c J J (𝟙 M) (ψ ≫ φ) (𝟙 _) h₂ (by simp) r p n hr]
    exact pageMap_id.{u,r,a,v} R c J r p n (by omega)

theorem page_maps :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.pageMaps.{u,r,a,v} := by
  intro X R U A c _
  exact ⟨fun J ↦ spectralData.{u,r,a,v} R c J, fun I J φ ↦ filteredMap.{u,r,a,v} R c I J φ,
    fun I J φ ↦ pageMap.{u,r,a,v} R c I J φ, fun I J φ ↦ columnFilteredMap_hom _ _ _,
    fun f I J φ ψ hf hg r p n hr ↦ pageMap_lift_independent.{u,r,a,v} R c I J f φ ψ hf hg r p n hr,
    fun I ↦ pageMap_id.{u,r,a,v} R c I,
    fun I J K ↦ pageMap_comp.{u,r,a,v} R c I J K,
    fun I J ↦ pageMap_isIso.{u,r,a,v} R c I J⟩

end PageMaps


section ModuleCarrier

variable (S : Type r) [Ring S]

/-- The module lift preserves coproducts indexed in the source carrier universe. -/
private theorem moduleLiftPreservesColimits :
    PreservesColimitsOfSize.{max a r,max a r} (ModuleCat.uliftFunctor.{b,max a r} S) := by
  let F := ModuleCat.uliftFunctor.{b,max a r} S
  let G := forget₂ (ModuleCat.{max a b r} S) AddCommGrpCat.{max a b r}
  let _ : ReflectsColimitsOfSize.{max a r,max a r} G :=
    reflectsColimits_of_reflectsIsomorphisms
  have : PreservesColimitsOfSize.{max a r,max a r} (F ⋙ G) := by
    change PreservesColimitsOfSize.{max a r,max a r}
      (forget₂ (ModuleCat.{max a r} S) AddCommGrpCat.{max a r} ⋙ AddCommGrpCat.uliftFunctor.{b,max a r})
    infer_instance
  exact preservesColimits_of_reflects_of_preserves F G

private instance moduleLiftPreservesSmallColimits :
    PreservesColimitsOfSize.{0,0} (ModuleCat.uliftFunctor.{b,max a r} S) := by
  let _ := moduleLiftPreservesColimits.{r,a,b} S
  exact preservesColimitsOfSize_shrink (ModuleCat.uliftFunctor.{b,max a r} S)

private def moduleLiftSubobjects (X : ModuleCat.{a} S) :
    Subobject X ≃o Subobject ((ModuleCat.uliftFunctor.{b,a} S).obj X) :=
  (ModuleCat.subobjectModule X).trans
    ((Submodule.orderIsoMapComap (ULift.moduleEquiv.symm :
      X ≃ₗ[S] (ModuleCat.uliftFunctor.{b,a} S).obj X)).trans
      (ModuleCat.subobjectModule ((ModuleCat.uliftFunctor.{b,a} S).obj X)).symm)

private lemma moduleSubobject_mk {X Y : ModuleCat.{a} S} (f : X ⟶ Y) [Mono f] :
    ModuleCat.subobjectModule Y (Subobject.mk f) = LinearMap.range f.hom := by
  change LinearMap.range (Subobject.mk f).arrow.hom = _
  calc
    _ = LinearMap.range ((Subobject.underlyingIso f).hom ≫ f).hom :=
      congrArg (fun g => LinearMap.range (ModuleCat.Hom.hom g))
        (Subobject.underlyingIso_hom_comp_eq_mk f).symm
    _ = _ := LinearEquiv.range_comp (Subobject.underlyingIso f).toLinearEquiv f.hom

set_option maxHeartbeats 2100000 in
private lemma moduleLiftSubobjects_mk {X Y : ModuleCat.{a} S} (f : X ⟶ Y) [Mono f] :
    moduleLiftSubobjects.{r,a,b} S Y (Subobject.mk f) =
      Subobject.mk ((ModuleCat.uliftFunctor.{b,a} S).map f) := by
  let G := ModuleCat.uliftFunctor.{b,a} S
  let e : Y ≃ₗ[S] G.obj Y := ULift.moduleEquiv.symm
  let g : G.obj X ⟶ G.obj Y := G.map f
  have hg : ModuleCat.subobjectModule (G.obj Y) (Subobject.mk g) = LinearMap.range g.hom :=
    moduleSubobject_mk S g
  apply (ModuleCat.subobjectModule (G.obj Y)).injective
  calc
    _ = Submodule.map e.toLinearMap (ModuleCat.subobjectModule Y (Subobject.mk f)) :=
      (ModuleCat.subobjectModule (G.obj Y)).apply_symm_apply _
    _ = LinearMap.range g.hom := by
      rw [moduleSubobject_mk S f]
      ext x
      constructor
      · rintro ⟨_, ⟨s, rfl⟩, rfl⟩
        exact ⟨ULift.up s, rfl⟩
      · rintro ⟨s, rfl⟩
        exact ⟨f.hom s.down, ⟨s.down, rfl⟩, rfl⟩
    _ = _ := hg.symm

end ModuleCarrier

section FilteredTransport

open FiniteDiagonalFiltrations

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesColimitsOfSize.{0,0} F]
  {K : Bicomplex D} {L : Bicomplex C} [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)]

/-- If a total comparison has the given summand coordinates, it takes each
column slice to the image of the same slice under the coefficient equivalence. -/
lemma filtration_piece_transport
    (P : Filtration (sumTotal K)) (Q : Filtration (sumTotal L))
    (hP : HasFiltrationFormula K Prod.fst P) (hQ : HasFiltrationFormula L Prod.fst Q)
    (t : sumTotal K ≅ (F.mapHomologicalComplex (.up ℤ)).obj (sumTotal L))
    (e : ∀ p q : ℤ, (K.X p).X q ≅ F.obj ((L.X p).X q))
    (ht : ∀ (p q n : ℤ) (h : p + q = n),
      sumInjection K p q n h ≫ t.hom.f n = (e p q).hom ≫ F.map (sumInjection L p q n h))
    (p n : ℤ) :
    Subobject.mk ((P.piece p n).arrow ≫ t.hom.f n) = Subobject.mk (F.map ((Q.piece p n).arrow)) := by
  obtain ⟨b, hb, ι, hι, eι, hbi⟩ := hP p n
  obtain ⟨c, hc, κ, hκ, eκ, hci⟩ := hQ p n
  let cι := fun i => F.map (c.ι i)
  let hc' := isColimitCofanMkObjOfIsColimit F _ c.ι hc.isColimit
  calc
    Subobject.mk ((P.piece p n).arrow ≫ t.hom.f n) = Subobject.mk (ι ≫ t.hom.f n) := by
      rw [← Subobject.map_mk, ← Subobject.map_mk, Subobject.mk_arrow, eι]
    _ = Subobject.mk (F.map κ) := by
      apply le_antisymm
      · let g := hb.isColimit.desc (Cofan.mk (F.obj c.pt) (fun i =>
          (e i.val.val.1 i.val.val.2).hom ≫ cι i))
        apply Subobject.mk_le_mk_of_comm g
        apply hb.isColimit.hom_ext
        rintro ⟨i⟩
        change b.ι i ≫ (g ≫ F.map κ) = b.ι i ≫ (ι ≫ t.hom.f n)
        rw [← Category.assoc, show b.ι i ≫ g = (e i.val.val.1 i.val.val.2).hom ≫ cι i from
          hb.isColimit.fac _ ⟨i⟩,
          Category.assoc, ← Functor.map_comp, hci i, ← Category.assoc, hbi i]
        exact (ht _ _ n i.val.property).symm
      · let g := hc'.desc (Cofan.mk b.pt (fun i =>
          (e i.val.val.1 i.val.val.2).inv ≫ b.ι i))
        apply Subobject.mk_le_mk_of_comm g
        apply hc'.hom_ext
        rintro ⟨i⟩
        change cι i ≫ (g ≫ (ι ≫ t.hom.f n)) = cι i ≫ F.map κ
        rw [← Category.assoc, show cι i ≫ g = (e i.val.val.1 i.val.val.2).inv ≫ b.ι i from
          hc'.fac _ ⟨i⟩,
          Category.assoc, ← Category.assoc (b.ι i), hbi i, ht _ _ n i.val.property]
        dsimp only [cι]
        rw [Iso.inv_hom_id_assoc, ← Functor.map_comp, hci i]
    _ = Subobject.mk (F.map (Q.piece p n).arrow) := by
      rw [← eκ]
      apply Subobject.mk_eq_mk_of_comm _ _ (F.mapIso (Subobject.underlyingIso κ).symm)
      rw [Functor.mapIso_hom, ← Functor.map_comp]
      simp

end FilteredTransport

section LimitTransport

open HomologicalComplex FiniteFiltrationConvergence
open AdvancedHomologicalAlgebra.FiniteFiltrationConvergence
open AdvancedHomologicalAlgebra.CechToCohomology

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

private abbrev complexMap := G.mapHomologicalComplex (.up ℤ)

variable {K : CochainComplex D ℤ} {L : CochainComplex C ℤ}

def transportedHomology (e : K ≅ (complexMap G).obj L) (n : ℤ) :
    K.homology n ≅ G.obj (L.homology n) :=
  homologyMapIso e n ≪≫ (L.sc n).mapHomologyIso G

private def transportedCycles (e : K ≅ (complexMap G).obj L) (n : ℤ) :
    K.cycles n ≅ G.obj (L.cycles n) :=
  cyclesMapIso e n ≪≫ (L.sc n).mapCyclesIso G

@[reassoc] private lemma transportedCycles_i (e : K ≅ (complexMap G).obj L) (n : ℤ) :
    (transportedCycles G e n).hom ≫ G.map (L.iCycles n) =
      K.iCycles n ≫ e.hom.f n := by
  dsimp only [transportedCycles, Iso.trans_hom, cyclesMapIso_hom]
  rw [Category.assoc]
  exact (congrArg (fun b ↦ cyclesMap e.hom n ≫ b)
    ((L.sc n).mapCyclesIso_hom_iCycles G)).trans (cyclesMap_i e.hom n)

private lemma transportedHomology_natural
    {K' : CochainComplex D ℤ} {L' : CochainComplex C ℤ}
    (e : K ≅ (complexMap G).obj L) (e' : K' ≅ (complexMap G).obj L')
    (f : K ⟶ K') (g : L ⟶ L')
    (h : f ≫ e'.hom = e.hom ≫ (complexMap G).map g) (n : ℤ) :
    homologyMap f n ≫ (transportedHomology G e' n).hom =
      (transportedHomology G e n).hom ≫ G.map (homologyMap g n) := by
  have hG := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor C (.up ℤ) n).map g) G
  change homologyMap ((complexMap G).map g) n ≫ ((L'.sc n).mapHomologyIso G).hom =
    ((L.sc n).mapHomologyIso G).hom ≫ G.map (homologyMap g n) at hG
  dsimp only [transportedHomology, Iso.trans_hom, homologyMapIso_hom]
  rw [← Category.assoc, ← homologyMap_comp, h, homologyMap_comp, Category.assoc,
    hG, Category.assoc]

private def transportedImage {X Y : D} {X' Y' : C}
    (f : X ⟶ Y) (g : X' ⟶ Y') (ex : X ≅ G.obj X') (ey : Y ≅ G.obj Y')
    (h : f ≫ ey.hom = ex.hom ≫ G.map g) :
    (imageSubobject f : D) ≅ G.obj (imageSubobject g : C) :=
  let e : Arrow.mk f ≅ Arrow.mk (G.map g) := Arrow.isoMk ex ey h.symm
  (imageSubobjectIso f) ≪≫
    (im (C := D)).mapIso e ≪≫
    (PreservesImage.iso G g) ≪≫
    G.mapIso (imageSubobjectIso g).symm

omit [G.Additive] in
private lemma transportedImage_arrow {X Y : D} {X' Y' : C}
    (f : X ⟶ Y) (g : X' ⟶ Y') (ex : X ≅ G.obj X') (ey : Y ≅ G.obj Y')
    (h : f ≫ ey.hom = ex.hom ≫ G.map g) :
    (transportedImage G f g ex ey h).hom ≫ G.map (imageSubobject g).arrow =
      (imageSubobject f).arrow ≫ ey.hom := by
  dsimp only [transportedImage, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc, ← G.map_comp, imageSubobject_arrow',
    PreservesImage.hom_comp_map_image_ι, im_map]
  let e : Arrow.mk f ≅ Arrow.mk (G.map g) := Arrow.isoMk ex ey h.symm
  change (imageSubobjectIso f).hom ≫ image.map e.hom ≫ image.ι (G.map g) =
    (imageSubobject f).arrow ≫ ey.hom
  have hh : image.map e.hom ≫ image.ι (G.map g) = image.ι f ≫ ey.hom := image.map_ι e.hom
  rw [hh, imageSubobject_arrow_assoc]



private lemma transportedHomology_π (e : K ≅ (complexMap G).obj L) (n : ℤ) :
    K.homologyπ n ≫ (transportedHomology G e n).hom =
      (transportedCycles G e n).hom ≫ G.map (L.homologyπ n) := by
  have h := homologyπ_mapHomologyIso (L.sc n) G
  change ((complexMap G).obj L).homologyπ n ≫ ((L.sc n).mapHomologyIso G).hom =
    ((L.sc n).mapCyclesIso G).hom ≫ G.map (L.homologyπ n) at h
  dsimp only [transportedHomology, transportedCycles, Iso.trans_hom,
    homologyMapIso_hom, cyclesMapIso_hom]
  rw [← Category.assoc, homologyπ_naturality, Category.assoc, h, Category.assoc]

variable (P : Filtration K) (Q : Filtration L)
  (e : K ≅ (complexMap G).obj L)
  (he : ∀ p n : ℤ, Subobject.mk ((P.piece p n).arrow ≫ e.hom.f n) =
    Subobject.mk (G.map (Q.piece p n).arrow))

private def transportedPiece (p n : ℤ) :
    (P.piece p n : D) ≅ G.obj (Q.piece p n : C) :=
  Subobject.isoOfMkEqMk ((P.piece p n).arrow ≫ e.hom.f n)
    (G.map (Q.piece p n).arrow) (he p n)

@[reassoc] private lemma transportedPiece_arrow (p n : ℤ) :
    (transportedPiece G P Q e he p n).hom ≫ G.map (Q.piece p n).arrow =
      (P.piece p n).arrow ≫ e.hom.f n := by
  simp [transportedPiece, Subobject.isoOfMkEqMk]

private def transportedStep (p : ℤ) : P.step p ≅ (complexMap G).obj (Q.step p) :=
  HomologicalComplex.Hom.isoOfComponents (transportedPiece G P Q e he p) (by
    intro i j _
    apply (cancel_mono (G.map (Q.piece p j).arrow)).1
    simp only [Category.assoc]
    change (transportedPiece G P Q e he p i).hom ≫ G.map ((Q.step p).d i j) ≫ _ =
      (P.step p).d i j ≫ (transportedPiece G P Q e he p j).hom ≫ _
    rw [← Functor.map_comp, show (Q.step p).d i j ≫ (Q.piece p j).arrow =
      (Q.piece p i).arrow ≫ L.d i j from Q.differential_arrow p i j,
      Functor.map_comp, transportedPiece_arrow_assoc, transportedPiece_arrow,
      ← Category.assoc ((P.step p).d i j), show (P.step p).d i j ≫ (P.piece p j).arrow =
      (P.piece p i).arrow ≫ K.d i j from P.differential_arrow p i j,
      Category.assoc]
    exact congrArg (fun f ↦ (P.piece p i).arrow ≫ f) (e.hom.comm i j))

private lemma transportedStep_inclusion (p : ℤ) :
    P.inclusion p ≫ e.hom = (transportedStep G P Q e he p).hom ≫
      (complexMap G).map (Q.inclusion p) := by
  ext n
  exact (transportedPiece_arrow G P Q e he p n).symm

private def transportedCohomologyPiece (p n : ℤ) :
    (cohomologyPiece P p n : D) ≅ G.obj (cohomologyPiece Q p n : C) :=
  transportedImage G (homologyMap (P.inclusion p) n) (homologyMap (Q.inclusion p) n)
    (transportedHomology G (transportedStep G P Q e he p) n) (transportedHomology G e n)
    (transportedHomology_natural G (transportedStep G P Q e he p) e _ _
      (transportedStep_inclusion G P Q e he p) n)

@[reassoc] private lemma transportedCohomologyPiece_arrow (p n : ℤ) :
    (transportedCohomologyPiece G P Q e he p n).hom ≫ G.map (cohomologyPiece Q p n).arrow =
      (cohomologyPiece P p n).arrow ≫ (transportedHomology G e n).hom :=
  transportedImage_arrow G _ _ _ _ _

@[reassoc] private lemma closedCycles_arrow (p n : ℤ) :
    closedCycles P p n ≫ (P.step p).iCycles n ≫ (P.piece p n).arrow =
      (closed P p n).arrow := by
  simp [closedCycles]

private def closedCyclesIso (p n : ℤ) : (closed P p n : D) ≅ (P.step p).cycles n := by
  have h : Mono (closedCycles P p n ≫ (P.step p).iCycles n ≫ (P.piece p n).arrow) := by
    rw [closedCycles_arrow]
    infer_instance
  have : Mono (closedCycles P p n) := mono_of_mono _ ((P.step p).iCycles n ≫ (P.piece p n).arrow)
  letI := isIso_of_mono_of_epi (closedCycles P p n)
  exact asIso (closedCycles P p n)

private def transportedClosed (p n : ℤ) :
    (closed P p n : D) ≅ G.obj (closed Q p n : C) :=
  closedCyclesIso P p n ≪≫ transportedCycles G (transportedStep G P Q e he p) n ≪≫
    G.mapIso (closedCyclesIso Q p n).symm

@[reassoc] private lemma transportedClosed_arrow (p n : ℤ) :
    (transportedClosed G P Q e he p n).hom ≫ G.map (closed Q p n).arrow =
      (closed P p n).arrow ≫ e.hom.f n := by
  dsimp only [transportedClosed, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  have hQ : (closedCyclesIso Q p n).inv ≫ (closed Q p n).arrow =
      (Q.step p).iCycles n ≫ (Q.piece p n).arrow := by
    apply (cancel_epi (closedCyclesIso Q p n).hom).1
    rw [Iso.hom_inv_id_assoc]
    exact (closedCycles_arrow Q p n).symm
  simp only [Category.assoc]
  rw [← Functor.map_comp, hQ, Functor.map_comp,
    transportedCycles_i_assoc]
  change closedCycles P p n ≫ (P.step p).iCycles n ≫
    (transportedPiece G P Q e he p n).hom ≫ G.map (Q.piece p n).arrow = _
  rw [transportedPiece_arrow, ← closedCycles_arrow_assoc]

private lemma transportedClosedClass (p n : ℤ) :
    closedClass P p n ≫ (transportedCohomologyPiece G P Q e he p n).hom =
      (transportedClosed G P Q e he p n).hom ≫ G.map (closedClass Q p n) := by
  let x := K.liftCycles (closed P p n).arrow (n+1) (by simp) (closed_d P p n)
  let y := L.liftCycles (closed Q p n).arrow (n+1) (by simp) (closed_d Q p n)
  have hxy : x ≫ (transportedCycles G e n).hom =
      (transportedClosed G P Q e he p n).hom ≫ G.map y := by
    apply (cancel_mono (G.map (L.iCycles n))).1
    simp only [Category.assoc, transportedCycles_i, ← Functor.map_comp,
      x, y, liftCycles_i_assoc, liftCycles_i, transportedClosed_arrow]
  apply (cancel_mono (G.map (cohomologyPiece Q p n).arrow)).1
  simp only [Category.assoc, transportedCohomologyPiece_arrow, ← G.map_comp]
  rw [← Category.assoc, closedClass_arrow P p n, Category.assoc, transportedHomology_π,
    closedClass_arrow Q p n]
  change x ≫ (transportedCycles G e n).hom ≫ G.map (L.homologyπ n) =
    (transportedClosed G P Q e he p n).hom ≫ G.map (y ≫ L.homologyπ n)
  rw [← Category.assoc, hxy, Category.assoc, ← G.map_comp]

variable {H : D} {H' : C} (n : ℤ)
  (a : K.homology n ≅ H) (a' : L.homology n ≅ H')

private def transportedAbutment : H ≅ G.obj H' :=
  a.symm ≪≫ transportedHomology G e n ≪≫ G.mapIso a'

private def abutmentPieceIso (p : ℤ) :
    (abutmentPiece P n a p : D) ≅ (cohomologyPiece P p n : D) :=
  Subobject.underlyingIso ((cohomologyPiece P p n).arrow ≫ a.hom)

private def transportedAbutmentPiece (p : ℤ) :
    (abutmentPiece P n a p : D) ≅ G.obj (abutmentPiece Q n a' p : C) :=
  abutmentPieceIso P n a p ≪≫ transportedCohomologyPiece G P Q e he p n ≪≫
    G.mapIso (abutmentPieceIso Q n a' p).symm

@[reassoc] private lemma abutmentPieceIso_arrow (p : ℤ) :
    (abutmentPieceIso P n a p).hom ≫ (cohomologyPiece P p n).arrow =
      (abutmentPiece P n a p).arrow ≫ a.inv := by
  apply (cancel_mono a.hom).1
  dsimp only [abutmentPieceIso, abutmentPiece]
  simp [Category.assoc]

@[reassoc] private lemma abutmentPieceIso_inv_arrow (p : ℤ) :
    (abutmentPieceIso P n a p).inv ≫ (abutmentPiece P n a p).arrow =
      (cohomologyPiece P p n).arrow ≫ a.hom :=
  Subobject.underlyingIso_arrow _

@[reassoc] private lemma transportedAbutmentPiece_arrow (p : ℤ) :
    (transportedAbutmentPiece G P Q e he n a a' p).hom ≫ G.map (abutmentPiece Q n a' p).arrow =
      (abutmentPiece P n a p).arrow ≫ (transportedAbutment G e n a a').hom := by
  dsimp only [transportedAbutmentPiece, transportedAbutment, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom]
  simp only [Category.assoc]
  rw [← G.map_comp, abutmentPieceIso_inv_arrow, G.map_comp, transportedCohomologyPiece_arrow_assoc,
    abutmentPieceIso_arrow_assoc]

private abbrev adjacent (p : ℤ) :=
  Subobject.ofLE _ _ (abutmentPiece_decreasing P n a p)

private lemma transportedAbutmentPiece_adjacent (p : ℤ) :
    adjacent P n a p ≫ (transportedAbutmentPiece G P Q e he n a a' p).hom =
      (transportedAbutmentPiece G P Q e he n a a' (p+1)).hom ≫ G.map (adjacent Q n a' p) := by
  apply (cancel_mono (G.map (abutmentPiece Q n a' p).arrow)).1
  simp only [Category.assoc]
  rw [transportedAbutmentPiece_arrow, ← G.map_comp]
  simp only [adjacent, Subobject.ofLE_arrow_assoc, Subobject.ofLE_arrow]
  exact (transportedAbutmentPiece_arrow G P Q e he n a a' (p+1)).symm

private def transportedAbutmentGraded (p : ℤ) :
    cokernel (adjacent P n a p) ≅ G.obj (cokernel (adjacent Q n a' p)) :=
  cokernel.mapIso _ _
      (transportedAbutmentPiece G P Q e he n a a' (p+1))
      (transportedAbutmentPiece G P Q e he n a a' p)
      (transportedAbutmentPiece_adjacent G P Q e he n a a' p) ≪≫
    (PreservesCokernel.iso G (adjacent Q n a' p)).symm

@[reassoc] private lemma transportedAbutmentGraded_π (p : ℤ) :
    cokernel.π (adjacent P n a p) ≫ (transportedAbutmentGraded G P Q e he n a a' p).hom =
      (transportedAbutmentPiece G P Q e he n a a' p).hom ≫ G.map (cokernel.π (adjacent Q n a' p)) := by
  apply (cancel_mono (PreservesCokernel.iso G (adjacent Q n a' p)).hom).1
  dsimp only [transportedAbutmentGraded, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, PreservesCokernel.π_iso_hom]
  dsimp [cokernel.mapIso, cokernel.map]
  simp



open Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
  (limitClass limitQuotient)

private lemma transportedLimitClass (p : ℤ) :
    limitClass P n a p ≫ (transportedAbutmentGraded G P Q e he n a a' p).hom =
      (transportedClosed G P Q e he p n).hom ≫ G.map (limitClass Q n a' p) := by
  change (closedClass P p n ≫ (abutmentPieceIso P n a p).inv ≫
      cokernel.π (adjacent P n a p)) ≫ _ =
    _ ≫ G.map (closedClass Q p n ≫ (abutmentPieceIso Q n a' p).inv ≫
      cokernel.π (adjacent Q n a' p))
  rw [Category.assoc, Category.assoc, transportedAbutmentGraded_π]
  dsimp only [transportedAbutmentPiece, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (closedClass P p n), transportedClosedClass,
    Category.assoc, ← Functor.map_comp, ← Functor.map_comp]

open Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients (comparesLimits)

include he in
/-- The stabilized page comparison is determined by the same closed
representatives on both sides of the filtered total comparison. -/
theorem limiting_transport (D : F03Specs.PageData P) (E : F03Specs.PageData Q) :
    comparesLimits G P Q D E e := by
  intro n H H' a a'
  let z := (transportedClosed G P Q e he · n)
  let f := transportedAbutmentPiece G P Q e he n a a'
  let g := transportedAbutmentGraded G P Q e he n a a'
  have hc (p : ℤ) : limitClass P n a p ≫ (g p).hom =
      (z p).hom ≫ G.map (limitClass Q n a' p) :=
    transportedLimitClass G P Q e he n a a' p
  refine ⟨z, f, g, fun p ↦ transportedClosed_arrow G P Q e he p n,
    fun p ↦ ?_, transportedAbutmentGraded_π G P Q e he n a a', hc, ?_⟩
  · simpa only [f, transportedAbutment, transportedHomology, Iso.trans_hom, Category.assoc]
      using transportedAbutmentPiece_arrow G P Q e he n a a' p
  · intro r p _ _ l l' hl hl'
    let i := l ≪≫ g p ≪≫ G.mapIso l'.symm
    have comm : i.hom ≫ G.map l'.hom = l.hom ≫ (g p).hom := by
      change (l.hom ≫ (g p).hom ≫ (G.mapIso l').inv) ≫ (G.mapIso l').hom = _
      simp [Category.assoc]
    refine ⟨i, ?_, comm⟩
    apply (cancel_mono (G.map l'.hom)).1
    rw [Category.assoc, comm, ← Category.assoc, hl, hc, Category.assoc,
      ← Functor.map_comp, hl']

/-- The map on subobjects is bijective for equivalences and for carrier lifts of modules. -/
private class SubobjectComparison {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.PreservesMonomorphisms] where
  orderIso (X : C) : Subobject X ≃o Subobject (F.obj X)
  mk_eq {X Y : C} (f : X ⟶ Y) [Mono f] :
    orderIso Y (Subobject.mk f) = Subobject.mk (F.map f)

private instance equivalenceSubobjectComparison {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.IsEquivalence] : SubobjectComparison F where
  orderIso X := (Subobject.lowerEquivalence (MonoOver.congr X F.asEquivalence)).toOrderIso
  mk_eq _ := rfl

private instance moduleLiftSubobjectComparison (S : Type r) [Ring S] :
    SubobjectComparison (ModuleCat.uliftFunctor.{b,a} S) where
  orderIso := moduleLiftSubobjects S
  mk_eq := moduleLiftSubobjects_mk S

section PageTransport
open FilteredPage

variable [SubobjectComparison G]

private def scalarSubobjects (X : C) : Subobject X ≃o Subobject (G.obj X) :=
  SubobjectComparison.orderIso (F := G) X

private lemma scalarSubobjects_mk {X Y : C} (f : X ⟶ Y) [Mono f] :
    scalarSubobjects G Y (Subobject.mk f) = Subobject.mk (G.map f) :=
  SubobjectComparison.mk_eq (F := G) f

private lemma scalarSubobjects_arrow {X : C} (S : Subobject X) :
    scalarSubobjects G X S = Subobject.mk (G.map S.arrow) := by
  conv_lhs => rw [← Subobject.mk_arrow S]
  exact scalarSubobjects_mk G S.arrow

private lemma scalarSubobjects_pullback {X Y : C} (g : X ⟶ Y) (S : Subobject Y) :
    scalarSubobjects G X ((Subobject.pullback g).obj S) =
      (Subobject.pullback (G.map g)).obj (scalarSubobjects G Y S) := by
  rw [scalarSubobjects_arrow, scalarSubobjects_arrow G S]
  symm
  exact Subobject.pullback_obj_mk ((Subobject.isPullback g S).map G)

private def subobjectTransport {X : D} {Y : C} (e : X ≅ G.obj Y) :
    Subobject Y ≃o Subobject X :=
  (scalarSubobjects G Y).trans (Subobject.mapIsoToOrderIso e).symm

private lemma subobjectTransport_iff {X : D} {Y : C} (e : X ≅ G.obj Y)
    (S : Subobject X) (T : Subobject Y) :
    S = subobjectTransport G e T ↔
      Subobject.mk (S.arrow ≫ e.hom) = Subobject.mk (G.map T.arrow) := by
  change S = (Subobject.mapIsoToOrderIso e).symm (scalarSubobjects G Y T) ↔ _
  rw [OrderIso.eq_symm_apply, scalarSubobjects_arrow]
  change (Subobject.map e.hom).obj S = _ ↔ _
  rw [← Subobject.map_mk, Subobject.mk_arrow]

private lemma subobjectTransport_pullback {X X' : D} {Y Y' : C}
    (e : X ≅ G.obj Y) (e' : X' ≅ G.obj Y') (f : X ⟶ X') (g : Y ⟶ Y')
    (h : f ≫ e'.hom = e.hom ≫ G.map g) (S : Subobject Y') :
    (Subobject.pullback f).obj (subobjectTransport G e' S) =
      subobjectTransport G e ((Subobject.pullback g).obj S) := by
  apply (Subobject.mapIsoToOrderIso e).injective
  change (Subobject.map e.hom).obj ((Subobject.pullback f).obj
      (subobjectTransport G e' S)) =
      (Subobject.mapIsoToOrderIso e) (subobjectTransport G e ((Subobject.pullback g).obj S))
  have hPb : IsPullback f e.hom e'.hom (G.map g) := IsPullback.of_vert_isIso ⟨h⟩
  rw [Subobject.map_pullback h hPb.isLimit]
  change (Subobject.pullback (G.map g)).obj ((Subobject.mapIsoToOrderIso e')
      ((Subobject.mapIsoToOrderIso e').symm (scalarSubobjects G Y' S))) =
    (Subobject.mapIsoToOrderIso e) ((Subobject.mapIsoToOrderIso e).symm
      (scalarSubobjects G Y ((Subobject.pullback g).obj S)))
  rw [OrderIso.apply_symm_apply, OrderIso.apply_symm_apply, scalarSubobjects_pullback]

include he in
private lemma subobjectTransport_almost (r p n : ℤ) :
    almost P r p n = subobjectTransport G (asIso (e.hom.f n)) (almost Q r p n) := by
  have h₁ := (subobjectTransport_iff G (asIso (e.hom.f n)) (P.piece p n) (Q.piece p n)).2
    (he p n)
  have h₂ := (subobjectTransport_iff G (asIso (e.hom.f (n+1)))
    (P.piece (p+r) (n+1)) (Q.piece (p+r) (n+1))).2 (he (p+r) (n+1))
  have h := (e.hom.comm n (n+1)).symm
  dsimp only [almost]
  rw [h₁, h₂, subobjectTransport_pullback G (asIso (e.hom.f n)) (asIso (e.hom.f (n+1))) _
    (L.d n (n+1)) h, OrderIso.map_inf]


private def transportedSubobject {X : D} {Y : C} (e : X ≅ G.obj Y)
    {S : Subobject X} {T : Subobject Y} (h : S = subobjectTransport G e T) :
    (S : D) ≅ G.obj (T : C) :=
  Subobject.isoOfMkEqMk (S.arrow ≫ e.hom) (G.map T.arrow)
    ((subobjectTransport_iff G e S T).1 h)

@[reassoc] private lemma transportedSubobject_arrow {X : D} {Y : C} (e : X ≅ G.obj Y)
    {S : Subobject X} {T : Subobject Y} (h : S = subobjectTransport G e T) :
    (transportedSubobject G e h).hom ≫ G.map T.arrow = S.arrow ≫ e.hom := by
  simp [transportedSubobject, Subobject.isoOfMkEqMk]

def almostCycleTransportIso (r p n : ℤ) :
    (almost P r p n : D) ≅ G.obj (almost Q r p n : C) :=
  transportedSubobject G _ (subobjectTransport_almost G P Q e he r p n)

@[reassoc] lemma almostCycleTransportIso_arrow (r p n : ℤ) :
    ( almostCycleTransportIso G P Q e he r p n).hom ≫ G.map (almost Q r p n).arrow =
      (almost P r p n).arrow ≫ e.hom.f n :=
  transportedSubobject_arrow G _ _

include he in
private lemma subobjectTransport_denominator (r p n : ℤ) :
    denominator P r p n = subobjectTransport G (asIso (e.hom.f n)) (denominator Q r p n) := by
  let f := (almost P (r-1) (p-r+1) (n-1)).arrow ≫ K.d (n-1) n
  let g := (almost Q (r-1) (p-r+1) (n-1)).arrow ≫ L.d (n-1) n
  let s := almostCycleTransportIso G P Q e he (r-1) (p-r+1) (n-1)
  have hfg : f ≫ e.hom.f n = s.hom ≫ G.map g := by
    dsimp only [f, g]
    rw [Category.assoc, (e.hom.comm (n-1) n).symm, G.map_comp]
    rw [ almostCycleTransportIso_arrow_assoc]
    rfl
  have hi : imageSubobject f = subobjectTransport G (asIso (e.hom.f n)) (imageSubobject g) := by
    apply (subobjectTransport_iff G (asIso (e.hom.f n)) _ _).2
    exact Subobject.mk_eq_mk_of_comm _ _ (transportedImage G f g s (asIso (e.hom.f n)) hfg)
      (transportedImage_arrow G f g s (asIso (e.hom.f n)) hfg)
  change almost P (r-1) (p+1) n ⊔ imageSubobject f =
    subobjectTransport G (asIso (e.hom.f n)) (almost Q (r-1) (p+1) n ⊔ imageSubobject g)
  rw [subobjectTransport_almost G P Q e he, hi, OrderIso.map_sup]

private def transportedDenominator (r p n : ℤ) :
    (denominator P r p n : D) ≅ G.obj (denominator Q r p n : C) :=
  transportedSubobject G _ (subobjectTransport_denominator G P Q e he r p n)

@[reassoc] private lemma transportedDenominator_arrow (r p n : ℤ) :
    (transportedDenominator G P Q e he r p n).hom ≫ G.map (denominator Q r p n).arrow =
      (denominator P r p n).arrow ≫ e.hom.f n :=
  transportedSubobject_arrow G _ _

private def transportedCokernel {X Y : D} {X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (ex : X ≅ G.obj X') (ey : Y ≅ G.obj Y') (h : f ≫ ey.hom = ex.hom ≫ G.map g) :
    cokernel f ≅ G.obj (cokernel g) :=
  cokernel.mapIso f (G.map g) ex ey h ≪≫ (PreservesCokernel.iso G g).symm

@[reassoc] private lemma transportedCokernel_π
    {X Y : D} {X' Y' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (ex : X ≅ G.obj X') (ey : Y ≅ G.obj Y') (h : f ≫ ey.hom = ex.hom ≫ G.map g) :
    cokernel.π f ≫ (transportedCokernel G f g ex ey h).hom = ey.hom ≫ G.map (cokernel.π g) := by
  apply (cancel_mono (PreservesCokernel.iso G g).hom).1
  dsimp only [transportedCokernel, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, PreservesCokernel.π_iso_hom]
  dsimp [cokernel.mapIso, cokernel.map]
  simp

variable (D : F03Specs.PageData P) (E : F03Specs.PageData Q)

private lemma transportedDenominator_inclusion (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    Subobject.ofLE _ _ (D.denominator_le r hr p n) ≫ ( almostCycleTransportIso G P Q e he r p n).hom =
      (transportedDenominator G P Q e he r p n).hom ≫
        G.map (Subobject.ofLE _ _ (E.denominator_le r hr p n)) := by
  apply (cancel_mono (G.map (almost Q r p n).arrow)).1
  simp only [Category.assoc]
  rw [ almostCycleTransportIso_arrow, ← G.map_comp]
  simp only [Subobject.ofLE_arrow_assoc, Subobject.ofLE_arrow]
  exact (transportedDenominator_arrow G P Q e he r p n).symm

private def transportedPageQuotient (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    cokernel (Subobject.ofLE _ _ (D.denominator_le r hr p n)) ≅
      G.obj (cokernel (Subobject.ofLE _ _ (E.denominator_le r hr p n))) :=
  transportedCokernel G _ _
    (transportedDenominator G P Q e he r p n) ( almostCycleTransportIso G P Q e he r p n)
    (transportedDenominator_inclusion G P Q e he D E r hr p n)

/-- Scalar transport on the actual page objects in every positive degree. -/
def pageTransportIso (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    PageCohomology.object P D r p n ≅ G.obj (PageCohomology.object Q E r p n) :=
  (D.quotientIso r hr p n).symm ≪≫ transportedPageQuotient G P Q e he D E r hr p n ≪≫
    G.mapIso (E.quotientIso r hr p n)

lemma pageTransportIso_representative (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    toPage P r p n (D.containment r p n) ≫ (pageTransportIso G P Q e he D E r hr p n).hom =
      ( almostCycleTransportIso G P Q e he r p n).hom ≫ G.map (toPage Q r p n (E.containment r p n)) := by
  conv_lhs => rw [← D.quotientIso_formula r hr p n]
  dsimp only [pageTransportIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  unfold transportedPageQuotient
  rw [← Category.assoc, transportedCokernel_π, Category.assoc, ← G.map_comp,
    E.quotientIso_formula r hr p n]


private lemma transportedAlmost_restriction (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    D.restriction r hr p n ≫ (almostCycleTransportIso G P Q e he r (p+r) (n+1)).hom =
      (almostCycleTransportIso G P Q e he r p n).hom ≫ G.map (E.restriction r hr p n) := by
  apply (cancel_mono (G.map (almost Q r (p+r) (n+1)).arrow)).1
  simp only [Category.assoc, almostCycleTransportIso_arrow, ← Functor.map_comp,
    (reassoc_of% D.restriction_arrow r hr p n), E.restriction_arrow]
  rw [G.map_comp, almostCycleTransportIso_arrow_assoc]
  exact congrArg (fun t ↦ (almost P r p n).arrow ≫ t) (e.hom.comm n (n+1)).symm

lemma pageTransportIso_differential (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    D.differential r (by omega) p n ≫ (pageTransportIso G P Q e he D E r hr (p+r) (n+1)).hom =
      (pageTransportIso G P Q e he D E r hr p n).hom ≫ G.map (E.differential r (by omega) p n) := by
  apply (cancel_epi (toPage P r p n (D.containment r p n))).1
  rw [← Category.assoc, D.representative_formula, Category.assoc,
    pageTransportIso_representative, ← Category.assoc, transportedAlmost_restriction,
    Category.assoc, ← G.map_comp, ← E.representative_formula,
    G.map_comp, ← Category.assoc, ← pageTransportIso_representative, Category.assoc]


/-- Transport of the three terms computing the cohomology of a page. -/
def pageShortTransportIso (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    PageCohomology.shortComplex P D r (by omega) p n ≅
      (PageCohomology.shortComplex Q E r (by omega) p n).map G :=
  ShortComplex.isoMk (pageTransportIso G P Q e he D E r hr p n)
    (pageTransportIso G P Q e he D E r hr (p+r) (n+1))
    (pageTransportIso G P Q e he D E r hr (p+r+r) (n+1+1))
    (pageTransportIso_differential G P Q e he D E r hr p n).symm
    (pageTransportIso_differential G P Q e he D E r hr (p+r) (n+1)).symm

private lemma transportedNextRepresentative (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    PageCohomology.nextRepresentative P D r p n ≫ (pageTransportIso G P Q e he D E r hr p n).hom =
      (almostCycleTransportIso G P Q e he (r+1) p n).hom ≫
        G.map (PageCohomology.nextRepresentative Q E r p n) := by
  have hinc : Subobject.ofLE _ _ (PageCohomology.almost_succ_le P r p n) ≫
      (almostCycleTransportIso G P Q e he r p n).hom =
    (almostCycleTransportIso G P Q e he (r+1) p n).hom ≫
      G.map (Subobject.ofLE _ _ (PageCohomology.almost_succ_le Q r p n)) := by
    apply (cancel_mono (G.map (almost Q r p n).arrow)).1
    simp only [Category.assoc]
    rw [almostCycleTransportIso_arrow, Subobject.ofLE_arrow_assoc, ← G.map_comp,
      Subobject.ofLE_arrow, almostCycleTransportIso_arrow]
  dsimp only [PageCohomology.nextRepresentative]
  rw [Category.assoc, pageTransportIso_representative, ← Category.assoc, hinc,
    Category.assoc, ← G.map_comp]

/-- Transport commutes with the representative-normalized passage to the next page. -/
lemma pageTransportIso_next (DP : PageCohomology.Data P D) (EQ : PageCohomology.Data Q E)
    (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    (pageTransportIso G P Q e he D E (r+1) (by omega) (p+r) (n+1)).hom ≫
      G.map (EQ.nextIso r (by omega) p n).hom =
    (DP.nextIso r (by omega) p n).hom ≫
      (ShortComplex.homologyMapIso (pageShortTransportIso G P Q e he D E r hr p n)).hom ≫
      ((PageCohomology.shortComplex Q E r (by omega) p n).mapHomologyIso G).hom := by
  let S := PageCohomology.shortComplex P D r (by omega) p n
  let T := PageCohomology.shortComplex Q E r (by omega) p n
  let s := pageShortTransportIso G P Q e he D E r hr p n
  let f := almostCycleTransportIso G P Q e he (r+1) (p+r) (n+1)
  let x := S.liftCycles (PageCohomology.nextRepresentative P D r (p+r) (n+1))
    (DP.next_cycle r (by omega) p n)
  let y := T.liftCycles (PageCohomology.nextRepresentative Q E r (p+r) (n+1))
    (EQ.next_cycle r (by omega) p n)
  have hxy : x ≫ ShortComplex.cyclesMap s.hom ≫ (T.mapCyclesIso G).hom =
      f.hom ≫ G.map y := by
    apply (cancel_mono (G.map T.iCycles)).1
    simp only [Category.assoc, ShortComplex.mapCyclesIso_hom_iCycles,
      ← Functor.map_comp, x, y, ShortComplex.liftCycles_i]
    rw [ShortComplex.cyclesMap_i s.hom, ShortComplex.liftCycles_i_assoc]
    exact transportedNextRepresentative G P Q e he D E r hr (p+r) (n+1)
  apply (cancel_epi (toPage P (r+1) (p+r) (n+1) (D.containment (r+1) (p+r) (n+1)))).1
  rw [← Category.assoc, pageTransportIso_representative, Category.assoc, ← G.map_comp,
    EQ.nextIso_formula, ← Category.assoc, DP.nextIso_formula]
  change f.hom ≫ G.map (y ≫ T.homologyπ) =
    (x ≫ S.homologyπ) ≫ ShortComplex.homologyMap s.hom ≫ (T.mapHomologyIso G).hom
  rw [Category.assoc, ShortComplex.homologyπ_naturality_assoc,
    homologyπ_mapHomologyIso, ← Category.assoc (ShortComplex.cyclesMap s.hom),
    ← Category.assoc x, hxy, Category.assoc, ← G.map_comp]


open Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients (comparesPages)

include he in
/-- Scalar equivalence identifies the actual page classes in all positive
page degrees using representatives of the original filtered total. -/
theorem pages_transport : comparesPages G P Q D E e := by
  exact ⟨almostCycleTransportIso G P Q e he, pageTransportIso G P Q e he D E,
    almostCycleTransportIso_arrow G P Q e he, pageTransportIso_representative G P Q e he D E,
    pageTransportIso_differential G P Q e he D E⟩

end PageTransport

section ColumnTransport

variable [SubobjectComparison G]

open DoubleTotalization DoubleComplexFirstPages FiniteDiagonalFiltrations FilteredPage

variable {K : Bicomplex D} {L : Bicomplex C} [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)]
  (DK : ColumnSpectralData K) (DL : ColumnSpectralData L)
  (e : K ≅ (mapIntDouble G).obj L)
  (t : sumTotal K ≅ (complexMap G).obj (sumTotal L))
  (h : ∀ p n : ℤ, Subobject.mk ((DK.filtration.piece p n).arrow ≫ t.hom.f n) =
    Subobject.mk (G.map (DL.filtration.piece p n).arrow))
  (ht : ∀ p q n : ℤ, ∀ hpq : p + q = n,
      sumInjection K p q n hpq ≫ t.hom.f n =
        (e.hom.f p).f q ≫ G.map (sumInjection L p q n hpq))

include ht in
/-- Compare the unsigned vertical cycle classes with the first page of the
same filtered total comparison. -/
lemma columnFirstIso_transport (p q : ℤ) :
    (pageTransportIso G DK.filtration DL.filtration t h DK.pages DL.pages 1 (by omega) p (p+q)).hom ≫
      G.map (columnFirstIso L DL.filtration DL.formula DL.pages p q).hom =
    (columnFirstIso K DK.filtration DK.formula DK.pages p q).hom ≫ (transportedHomology G (asIso (e.hom.f p)) q).hom := by
  let c := asIso (e.hom.f p)
  let z := transportedCycles G c q
  let x := (K.X p).iCycles q
  let y := (L.X p).iCycles q
  let a := columnAlmostCycle K DK.filtration DK.formula p q x ((K.X p).iCycles_d q (q+1))
  let b := columnAlmostCycle L DL.filtration DL.formula p q y ((L.X p).iCycles_d q (q+1))
  let u := almostCycleTransportIso G DK.filtration DL.filtration t h 1 p (p+q)
  have hab : a ≫ u.hom = z.hom ≫ G.map b := by
    apply (cancel_mono (G.map (almost DL.filtration 1 p (p+q)).arrow)).1
    simp only [Category.assoc]
    change a ≫ u.hom ≫ G.map (almost DL.filtration 1 p (p+q)).arrow =
      z.hom ≫ G.map b ≫ G.map (almost DL.filtration 1 p (p+q)).arrow
    rw [almostCycleTransportIso_arrow, columnAlmostCycle_arrow_assoc, ht,
      ← G.map_comp, columnAlmostCycle_arrow, G.map_comp, transportedCycles_i_assoc]
    rfl
  have ha := columnCyclesToPage_firstIso K DK.filtration DK.formula DK.pages p q
  have hb := columnCyclesToPage_firstIso L DL.filtration DL.formula DL.pages p q
  change (a ≫ toPage DK.filtration 1 p (p+q) (DK.pages.containment 1 p (p+q))) ≫ _ = _ at ha
  change (b ≫ toPage DL.filtration 1 p (p+q) (DL.pages.containment 1 p (p+q))) ≫ _ = _ at hb
  rw [Category.assoc] at hb
  apply (cancel_epi (columnCyclesToPage K DK.filtration DK.formula DK.pages p q)).1
  change (a ≫ toPage DK.filtration 1 p (p+q) (DK.pages.containment 1 p (p+q))) ≫ _ =
    (a ≫ toPage DK.filtration 1 p (p+q) (DK.pages.containment 1 p (p+q))) ≫ _
  rw [Category.assoc, ← Category.assoc (toPage DK.filtration 1 p (p+q) _),
    pageTransportIso_representative]
  change a ≫ (u.hom ≫ G.map (toPage DL.filtration 1 p (p+q) _)) ≫
      G.map (columnFirstIso L DL.filtration DL.formula DL.pages p q).hom =
    (a ≫ toPage DK.filtration 1 p (p+q) _) ≫ _ ≫ (transportedHomology G c q).hom
  simp only [Category.assoc]
  rw [(reassoc_of% hab), ← G.map_comp, ← G.map_comp, hb]
  calc
    z.hom ≫ G.map ((L.X p).homologyπ q) =
        (K.X p).homologyπ q ≫ (transportedHomology G c q).hom :=
      (transportedHomology_π G c q).symm
    _ = _ := by
      simpa only [Category.assoc] using
        congrArg (fun f ↦ f ≫ (transportedHomology G c q).hom) ha.symm


/-- Termwise unsigned vertical cohomology comparison over the original scalars. -/
def verticalHomologyTransportIso (q : ℤ) :
    verticalHomology K q ≅ (complexMap G).obj (verticalHomology L q) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ transportedHomology G (asIso (e.hom.f p)) q) (by
      intro p p' _
      exact (transportedHomology_natural G (asIso (e.hom.f p)) (asIso (e.hom.f p'))
        (K.d p p') (L.d p p') (e.hom.comm p p').symm q).symm)

include ht in
private lemma columnFirstIsoAt_transport (p q n : ℤ) (hn : p+q=n) :
    (pageTransportIso G DK.filtration DL.filtration t h DK.pages DL.pages 1 (by omega) p n).hom ≫
      G.map (columnFirstIsoAt L DL.filtration DL.formula DL.pages p q n hn).hom =
    (columnFirstIsoAt K DK.filtration DK.formula DK.pages p q n hn).hom ≫
      (verticalHomologyTransportIso G e q).hom.f p := by
  subst n
  simpa only [columnFirstIsoAt_self, verticalHomologyTransportIso, Hom.isoOfComponents_hom_f]
    using columnFirstIso_transport G DK DL e t h ht p q

include ht in
private lemma columnFirstShortIso_transport (p q : ℤ) :
    (pageShortTransportIso G DK.filtration DL.filtration t h DK.pages DL.pages 1 (by omega) p (p+q)).hom ≫
      G.mapShortComplex.map (columnFirstShortIso L DL.filtration DL.formula DL.pages p q).hom =
    (columnFirstShortIso K DK.filtration DK.formula DK.pages p q).hom ≫
      (HomologicalComplex.shortComplexFunctor' D (ComplexShape.up ℤ) p (p+1) (p+1+1)).map
        (verticalHomologyTransportIso G e q).hom := by
  ext
  · exact columnFirstIsoAt_transport G DK DL e t h ht p q (p+q) rfl
  · exact columnFirstIsoAt_transport G DK DL e t h ht (p+1) q (p+q+1) (by omega)
  · exact columnFirstIsoAt_transport G DK DL e t h ht (p+1+1) q (p+q+1+1) (by omega)

omit [PreservesFiniteLimits G] [PreservesFiniteColimits G] [SubobjectComparison G] in
private lemma map_isoSc'_transport {K₀ : CochainComplex D ℤ} {L₀ : CochainComplex C ℤ}
    (g : K₀ ⟶ (complexMap G).obj L₀) (i j k : ℤ)
    (hi : (ComplexShape.up ℤ).prev j = i) (hk : (ComplexShape.up ℤ).next j = k) :
    (HomologicalComplex.shortComplexFunctor D (.up ℤ) j).map g ≫
      G.mapShortComplex.map (L₀.isoSc' i j k hi hk).hom =
    (K₀.isoSc' i j k hi hk).hom ≫
      (HomologicalComplex.shortComplexFunctor' D (.up ℤ) i j k).map g := by
  subst i k
  ext <;> simp [HomologicalComplex.isoSc']

include ht in
private lemma columnFirstCohomologyShortIso_transport (p q : ℤ) :
    (pageShortTransportIso G DK.filtration DL.filtration t h DK.pages DL.pages 1 (by omega) p (p+q)).hom ≫
      G.mapShortComplex.map
        (columnFirstShortIso L DL.filtration DL.formula DL.pages p q ≪≫
          ((verticalHomology L q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm).hom =
    (columnFirstShortIso K DK.filtration DK.formula DK.pages p q ≪≫
        ((verticalHomology K q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm).hom ≫
      (HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℤ) (p+1)).map
        (verticalHomologyTransportIso G e q).hom := by
  let j := (verticalHomology K q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)
  let j' := (verticalHomology L q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)
  change _ ≫ G.mapShortComplex.map (_ ≫ j'.inv) = (_ ≫ j.inv) ≫ _
  apply (cancel_mono (G.mapShortComplex.map j'.hom)).1
  have hr := map_isoSc'_transport G (verticalHomologyTransportIso G e q).hom
    p (p+1) (p+1+1) (by simp) (by simp)
  change _ ≫ G.mapShortComplex.map j'.hom = j.hom ≫ _ at hr
  rw [Category.assoc, ← G.mapShortComplex.map_comp, Category.assoc, Iso.inv_hom_id,
    Category.comp_id, Category.assoc, hr]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  exact columnFirstShortIso_transport G DK DL e t h ht p q

include ht in
private lemma columnFirstShortHomologyIso_transport (p q : ℤ) :
    (ShortComplex.homologyMapIso
      (pageShortTransportIso G DK.filtration DL.filtration t h DK.pages DL.pages 1 (by omega) p (p+q))).hom ≫
      ((PageCohomology.shortComplex DL.filtration DL.pages 1 (by omega) p (p+q)).mapHomologyIso G).hom ≫
      G.map (ShortComplex.homologyMapIso
        (columnFirstShortIso L DL.filtration DL.formula DL.pages p q ≪≫
          ((verticalHomology L q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom =
    (ShortComplex.homologyMapIso (columnFirstShortIso K DK.filtration DK.formula DK.pages p q ≪≫
        ((verticalHomology K q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom ≫
      (transportedHomology G (verticalHomologyTransportIso G e q) (p+1)).hom := by
  let f := (columnFirstShortIso L DL.filtration DL.formula DL.pages p q ≪≫
    ((verticalHomology L q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm).hom
  dsimp only [ShortComplex.homologyMapIso_hom]
  rw [← ShortComplex.mapHomologyIso_hom_naturality f G]
  have hs := congrArg (fun g ↦ ShortComplex.homologyMap g)
    (columnFirstCohomologyShortIso_transport G DK DL e t h ht p q)
  simp only [ShortComplex.homologyMap_comp] at hs
  dsimp only [transportedHomology, Iso.trans_hom, homologyMapIso_hom, ShortComplex.homologyMapIso_hom]
  rw [← Category.assoc, ← Category.assoc, hs]
  rfl


include ht in
private lemma columnSecondCoreIso_transport (p q : ℤ) :
    (pageTransportIso G DK.filtration DL.filtration t h DK.pages DL.pages
      2 (by omega) (p+1) (p+q+1)).hom ≫
      G.map ((PageCohomology.nextIso DL.filtration DL.pages 1 (by omega) p (p+q)).hom ≫
        (ShortComplex.homologyMapIso
          (columnFirstShortIso L DL.filtration DL.formula DL.pages p q ≪≫
            ((verticalHomology L q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom) =
    ((PageCohomology.nextIso DK.filtration DK.pages 1 (by omega) p (p+q)).hom ≫
      (ShortComplex.homologyMapIso
        (columnFirstShortIso K DK.filtration DK.formula DK.pages p q ≪≫
          ((verticalHomology K q).isoSc' p (p+1) (p+1+1) (by simp) (by simp)).symm)).hom) ≫
      (transportedHomology G (verticalHomologyTransportIso G e q) (p+1)).hom := by
  have hn := pageTransportIso_next G DK.filtration DL.filtration t h DK.pages DL.pages
    (PageCohomology.data DK.filtration DK.pages) (PageCohomology.data DL.filtration DL.pages)
    1 (by omega) p (p+q)
  dsimp only [PageCohomology.data] at hn
  change (pageTransportIso G DK.filtration DL.filtration t h DK.pages DL.pages
    2 (by omega) (p+1) (p+q+1)).hom ≫
      G.map (PageCohomology.nextIso DL.filtration DL.pages 1 (by omega) p (p+q)).hom = _ at hn
  rw [Functor.map_comp, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [columnFirstShortHomologyIso_transport G DK DL e t h ht]

@[reassoc] private lemma pageTransportIso_reindex (r : ℤ) (hr : 1 ≤ r)
    (p p' n n' : ℤ) (hp : p = p') (hn : n = n') :
    (pageTransportIso G DK.filtration DL.filtration t h DK.pages DL.pages r hr p n).hom ≫
      G.map (eqToHom (congrArg₂ (PageCohomology.object DL.filtration DL.pages r) hp hn)) =
    eqToHom (congrArg₂ (PageCohomology.object DK.filtration DK.pages r) hp hn) ≫
      (pageTransportIso G DK.filtration DL.filtration t h DK.pages DL.pages r hr p' n').hom := by
  subst p' n'
  simp

omit [K.HasTotal (.up ℤ)] [L.HasTotal (.up ℤ)] in
@[reassoc] private lemma transportedVerticalHomology_reindex (q i j : ℤ) (hij : i = j) :
    (transportedHomology G (verticalHomologyTransportIso G e q) i).hom ≫
      G.map (eqToHom (congrArg (fun t ↦ (verticalHomology L q).homology t) hij)) =
    eqToHom (congrArg (fun t ↦ (verticalHomology K q).homology t) hij) ≫
      (transportedHomology G (verticalHomologyTransportIso G e q) j).hom := by
  subst j
  simp

open private secondIsoOfShortIso from MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.DoubleComplexFirstPages

include ht in
/-- The scalar change on the actual second page is the prescribed change
on the horizontal cohomology of the unsigned vertical cohomology complex. -/
lemma columnSecondIso_transport (p q : ℤ) :
    (pageTransportIso G DK.filtration DL.filtration t h DK.pages DL.pages 2 (by omega) p (p+q)).hom ≫
      G.map (columnSecondPageIso DL p q).hom =
    (columnSecondPageIso DK p q).hom ≫
      (transportedHomology G (verticalHomologyTransportIso G e q) p).hom := by
  dsimp only [columnSecondPageIso, columnSecondIso, secondIsoOfShortIso, Iso.trans_hom, eqToIso.hom]
  rw [Functor.map_comp, ← Category.assoc,
    pageTransportIso_reindex G DK DL t h 2 (by omega) p (p-1+1) (p+q) (p-1+q+1)
      (by omega) (by omega)]
  have hc := columnSecondCoreIso_transport G DK DL e t h ht (p-1) q
  simp only [Functor.map_comp, Category.assoc] at hc ⊢
  rw [(reassoc_of% hc), transportedVerticalHomology_reindex G e q (p-1+1) p (by omega)]


/-- The cycle normalization in HA-B03 characterizes the first-page coordinates. -/
lemma specifiedColumnFirstIso_eq (D₀ : ColumnSpectralData K) (p q : ℤ) :
    D₀.firstPages.firstIso p q = columnFirstIso K D₀.filtration D₀.formula D₀.pages p q := by
  let x := (K.X p).iCycles q
  have hx : x ≫ (K.X p).d q (q+1) = 0 := (K.X p).iCycles_d q (q+1)
  let a := columnAlmostCycle K D₀.filtration D₀.formula p q x hx
  have ha := D₀.firstPages.first_formula p q x hx a
    (columnAlmostCycle_arrow K D₀.filtration D₀.formula p q x hx)
  have hlift : (K.X p).liftCycles x (q+1) (by simp) hx = 𝟙 _ := by
    apply (cancel_mono x).1
    simp [x]
  apply Iso.ext
  apply (cancel_epi (columnCyclesToPage K D₀.filtration D₀.formula D₀.pages p q)).1
  rw [columnCyclesToPage_firstIso]
  rw [hlift, Category.id_comp] at ha
  change (a ≫ toPage D₀.filtration 1 p (p+q) (D₀.pages.containment 1 p (p+q))) ≫ _ = _
  rw [Category.assoc, ha]

/-- Every representative-normalized next-page model supplies the canonical map. -/
lemma specifiedNextIso_eq (D₀ : ColumnSpectralData K) (C₀ : PageCohomology.Data D₀.filtration D₀.pages)
    (r : ℤ) (hr : 0 ≤ r) (p n : ℤ) :
    C₀.nextIso r hr p n = PageCohomology.nextIso D₀.filtration D₀.pages r hr p n := by
  apply Iso.ext
  apply (cancel_epi (toPage D₀.filtration (r+1) (p+r) (n+1)
    (D₀.pages.containment (r+1) (p+r) (n+1)))).1
  exact (C₀.nextIso_formula r hr p n).trans
    ((PageCohomology.data D₀.filtration D₀.pages).nextIso_formula r hr p n).symm

private lemma specifiedColumnFirstShortIso_eq (D₀ : ColumnSpectralData K) (p q : ℤ) :
    firstPageShortIso D₀.filtration D₀.pages (verticalHomology K q) q
      (fun s => D₀.firstPages.firstIso s q) (fun s => D₀.firstPages.first_d s q) p =
    firstPageShortIso D₀.filtration D₀.pages (verticalHomology K q) q
      (fun s => (columnData K D₀.filtration D₀.formula D₀.pages).firstIso s q)
      (fun s => (columnData K D₀.filtration D₀.formula D₀.pages).first_d s q) p := by
  have h (s : ℤ) :
      D₀.firstPages.firstIso s q = (columnData K D₀.filtration D₀.formula D₀.pages).firstIso s q :=
    specifiedColumnFirstIso_eq _ s q
  apply Iso.ext
  ext
  · exact congrArg (fun i => i.hom) (h p)
  · dsimp only [firstPageShortIso, ShortComplex.isoMk_hom_τ₂, Iso.trans_hom]
    rw [h (p+1)]
  · dsimp only [firstPageShortIso, ShortComplex.isoMk_hom_τ₃, Iso.trans_hom]
    rw [h (p+1+1)]

/-- The representative-normalized B03 records use the canonical second-page isomorphism. -/
lemma specifiedColumnSecondIso_eq (D₀ : ColumnSpectralData K) (p q : ℤ) :
    D₀.firstPages.secondIso p q = columnSecondPageIso D₀ p q := by
  suffices H : ∀ i : ℤ, D₀.firstPages.secondIso (i+1) q = columnSecondPageIso D₀ (i+1) q by
    exact Eq.mp (congrArg (fun i => D₀.firstPages.secondIso i q = columnSecondPageIso D₀ i q)
      (show p - 1 + 1 = p by omega)) (H (p-1))
  intro i
  obtain ⟨A₀, ha⟩ := D₀.firstPages.second_formula q
  obtain ⟨B₀, hb⟩ := (columnData K D₀.filtration D₀.formula D₀.pages).second_formula q
  dsimp only at ha hb
  rw [← ha i]
  change _ = (columnData K D₀.filtration D₀.formula D₀.pages).secondIso (i+1) q
  rw [← hb i, specifiedColumnFirstShortIso_eq,
    specifiedNextIso_eq D₀ A₀, specifiedNextIso_eq D₀ B₀]


open Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients (comparesColumnSecond)

include h ht in
/-- The B03 formula is carried by any page map with the prescribed
representative coordinates for this scalar and filtered total comparison. -/
theorem column_second_transport : comparesColumnSecond G DK DL e t := by
  refine ⟨verticalHomologyTransportIso G e, fun _ _ ↦ rfl, ?_⟩
  intro p q z c hz hc
  have hz' : z = (almostCycleTransportIso G DK.filtration DL.filtration t h 2 p (p+q)).hom := by
    apply (cancel_mono (G.map (almost DL.filtration 2 p (p+q)).arrow)).1
    exact hz.trans (almostCycleTransportIso_arrow G DK.filtration DL.filtration t h 2 p (p+q)).symm
  have hc' : c = (pageTransportIso G DK.filtration DL.filtration t h DK.pages DL.pages
      2 (by omega) p (p+q)).hom := by
    apply (cancel_epi (toPage DK.filtration 2 p (p+q) (DK.pages.containment 2 p (p+q)))).1
    rw [hz'] at hc
    exact hc.trans (pageTransportIso_representative G DK.filtration DL.filtration t h
      DK.pages DL.pages 2 (by omega) p (p+q)).symm
  rw [hc', specifiedColumnSecondIso_eq DK, specifiedColumnSecondIso_eq DL]
  exact columnSecondIso_transport G DK DL e t h ht p q

end ColumnTransport

end LimitTransport

section SignedTotal

open FiniteDiagonalFiltrations
open CechToCohomology (natToIntDoubleComplex mapExtendIso mapExtendXIso mapExtendIso_hom_f)

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (F : C ⥤ D) [F.Additive]

private lemma mapExtend_natural {A B : Type*} [Category* A] [Category* B]
    [Preadditive A] [Preadditive B] [HasZeroObject A] [HasZeroObject B]
    (G : A ⥤ B) [G.Additive] {K L : CochainComplex A ℕ} (f : K ⟶ L)
    (ee : (ComplexShape.up ℕ).Embedding (.up ℤ)) :
    (G.mapHomologicalComplex (.up ℤ)).map (HomologicalComplex.extendMap f ee) ≫
        (mapExtendIso G L ee).hom =
      (mapExtendIso G K ee).hom ≫
        HomologicalComplex.extendMap ((G.mapHomologicalComplex (.up ℕ)).map f) ee := by
  ext i
  change G.map (HomologicalComplex.extend.mapX f (ee.r i)) ≫
      (mapExtendXIso G L (ee.r i)).hom =
    (mapExtendXIso G K (ee.r i)).hom ≫
      HomologicalComplex.extend.mapX ((G.mapHomologicalComplex (.up ℕ)).map f) (ee.r i)
  cases ee.r i <;> simp [mapExtendXIso, HomologicalComplex.extend.mapX]

/-- Zero extension in both directions commutes with the coefficient functor. -/
def mapIntDoubleIso (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) :
    (mapIntDouble F).obj (natToIntDoubleComplex K) ≅
      natToIntDoubleComplex ((mapDouble F).obj K) := by
  let ee := ComplexShape.embeddingUpIntGE 0
  let H := F.mapHomologicalComplex (.up ℤ)
  let L := ((ee.extendFunctor C).mapHomologicalComplex (.up ℕ)).obj K
  refine mapExtendIso H L ee ≪≫ (ee.extendFunctor _).mapIso ?_
  refine HomologicalComplex.Hom.isoOfComponents (fun i ↦ mapExtendIso F (K.X i) ee) ?_
  intro p q _
  exact (mapExtend_natural F (K.d p q) ee).symm

private abbrev extendedColumnIso {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) (p : ℕ) :
    (natToIntDoubleComplex K).X (p : ℤ) ≅ (K.X p).extend embedding :=
  (((embedding.extendFunctor B).mapHomologicalComplex (.up ℕ)).obj K).extendXIso embedding
    (by simp [embedding])

private lemma extendedColumnIso_naturality {B : Type*} [Category* B] [Abelian B]
    {K L : HomologicalComplex₂ B (.up ℕ) (.up ℕ)} (f : K ⟶ L) (p : ℕ) :
    (CechToCohomology.natToIntDoubleComplexMap f).f (p : ℤ) ≫ (extendedColumnIso L p).hom =
      (extendedColumnIso K p).hom ≫ HomologicalComplex.extendMap (f.f p) embedding := by
  dsimp only [CechToCohomology.natToIntDoubleComplexMap]
  rw [HomologicalComplex.extendMap_f _ _ (by simp [embedding] : embedding.f p = (p : ℤ))]
  simp [extendedColumnIso, Category.assoc]

private lemma mapIntDoubleIso_column (K : HomologicalComplex₂ C (.up ℕ) (.up ℕ)) (p : ℕ) :
    (mapIntDoubleIso F K).hom.f (p : ℤ) ≫ (extendedColumnIso ((mapDouble F).obj K) p).hom =
      (F.mapHomologicalComplex (.up ℤ)).map (extendedColumnIso K p).hom ≫
        (mapExtendIso F (K.X p) embedding).hom := by
  let H := F.mapHomologicalComplex (.up ℤ)
  let L := ((embedding.extendFunctor C).mapHomologicalComplex (.up ℕ)).obj K
  let E : (H.mapHomologicalComplex (.up ℕ)).obj L ≅
      ((embedding.extendFunctor D).mapHomologicalComplex (.up ℕ)).obj ((mapDouble F).obj K) :=
    HomologicalComplex.Hom.isoOfComponents (fun p ↦ mapExtendIso F (K.X p) embedding)
      (fun p q _ ↦ (mapExtend_natural F (K.d p q) embedding).symm)
  change ((mapExtendIso H L embedding).hom.f (p : ℤ) ≫
      (HomologicalComplex.extendMap E.hom embedding).f (p : ℤ)) ≫
        (extendedColumnIso ((mapDouble F).obj K) p).hom = _
  rw [HomologicalComplex.extendMap_f _ _ (by simp [embedding] : embedding.f p = (p : ℤ))]
  simp only [Category.assoc, extendedColumnIso, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, mapExtendIso_hom_f]
  rfl

private abbrev extendedZeroColumnIso {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) :=
  extendedColumnIso K 0

/-- Comparing the two zero columns commutes with extension of a map into them. -/
private lemma intZeroColumnTransport {K : HomologicalComplex₂ D (.up ℕ) (.up ℕ)}
    {L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)}
    {P : CochainComplex D ℕ} {Q : CochainComplex C ℕ}
    (e : K ≅ (mapDouble F).obj L)
    (s : P ≅ (F.mapHomologicalComplex (.up ℕ)).obj Q)
    (α : P ⟶ K.X 0) (β : Q ⟶ L.X 0)
    (h : α ≫ e.hom.f 0 = s.hom ≫ (F.mapHomologicalComplex (.up ℕ)).map β) :
    let e' := (embedding.extendFunctor _).mapIso
      (((embedding.extendFunctor _).mapHomologicalComplex (.up ℕ)).mapIso e) ≪≫
      (mapIntDoubleIso F L).symm
    let s' := (embedding.extendFunctor _).mapIso s ≪≫ (mapExtendIso F Q embedding).symm
    (HomologicalComplex.extendMap α embedding ≫ (extendedZeroColumnIso K).inv) ≫ e'.hom.f 0 =
      s'.hom ≫ (F.mapHomologicalComplex (.up ℤ)).map
        (HomologicalComplex.extendMap β embedding ≫ (extendedZeroColumnIso L).inv) := by
  let H := F.mapHomologicalComplex (.up ℤ)
  let w := mapIntDoubleIso F L
  let π := (extendedZeroColumnIso ((mapDouble F).obj L)).hom
  have hw : w.inv.f 0 ≫ (w.hom.f 0 ≫ π) = π := by
    rw [← Category.assoc]
    have hi := HomologicalComplex.congr_hom w.inv_hom_id (0 : ℤ)
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hi
    rw [hi, Category.id_comp]
  have hright :
      H.map (HomologicalComplex.extendMap β embedding ≫ (extendedZeroColumnIso L).inv) ≫
        (w.hom.f 0 ≫ π) =
      (mapExtendIso F Q embedding).hom ≫
        HomologicalComplex.extendMap ((F.mapHomologicalComplex (.up ℕ)).map β) embedding := by
    change _ ≫ ((mapIntDoubleIso F L).hom.f 0 ≫
      (extendedZeroColumnIso ((mapDouble F).obj L)).hom) = _
    rw [show (mapIntDoubleIso F L).hom.f (0 : ℤ) ≫ (extendedZeroColumnIso ((mapDouble F).obj L)).hom = _
          from mapIntDoubleIso_column F L 0, ← Category.assoc, ← Functor.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact mapExtend_natural F β embedding
  dsimp only
  apply (cancel_mono (w.hom.f 0 ≫ π)).1
  simp only [Iso.trans_hom, Iso.symm_hom, HomologicalComplex.comp_f]
  have he : ((embedding.extendFunctor _).mapIso
      (((embedding.extendFunctor _).mapHomologicalComplex (.up ℕ)).mapIso e)).hom =
      CechToCohomology.natToIntDoubleComplexMap e.hom := rfl
  have hs : ((embedding.extendFunctor _).mapIso s).hom =
      HomologicalComplex.extendMap s.hom embedding := rfl
  rw [he, hs]
  simp only [Category.assoc]
  change HomologicalComplex.extendMap α embedding ≫ (extendedZeroColumnIso K).inv ≫
      (CechToCohomology.natToIntDoubleComplexMap e.hom).f 0 ≫ w.inv.f 0 ≫ w.hom.f 0 ≫ π =
    HomologicalComplex.extendMap s.hom embedding ≫ (mapExtendIso F Q embedding).inv ≫
      H.map (HomologicalComplex.extendMap β embedding ≫ (extendedZeroColumnIso L).inv) ≫ w.hom.f 0 ≫ π
  rw [hw, hright, Iso.inv_hom_id_assoc]
  change _ ≫ _ ≫ ((CechToCohomology.natToIntDoubleComplexMap e.hom).f 0 ≫
    (extendedZeroColumnIso ((mapDouble F).obj L)).hom) = _
  rw [show (CechToCohomology.natToIntDoubleComplexMap e.hom).f (0 : ℤ) ≫
          (extendedZeroColumnIso ((mapDouble F).obj L)).hom = _
        from extendedColumnIso_naturality e.hom 0, Iso.inv_hom_id_assoc]
  rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp, h]

/-- The comparison on integer entries restricts to the given map on every
nonnegative bidegree. -/
private lemma comparedBicomplexColumn {K : HomologicalComplex₂ D (.up ℕ) (.up ℕ)}
    {L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)}
    (e : K ≅ (mapDouble F).obj L) (p : ℕ) :
    let e' := (embedding.extendFunctor _).mapIso
      (((embedding.extendFunctor _).mapHomologicalComplex (.up ℕ)).mapIso e) ≪≫
      (mapIntDoubleIso F L).symm
    e'.hom.f (p : ℤ) ≫ (F.mapHomologicalComplex (.up ℤ)).map (extendedColumnIso L p).hom ≫
      (mapExtendIso F (L.X p) embedding).hom =
        (extendedColumnIso K p).hom ≫ HomologicalComplex.extendMap (e.hom.f p) embedding := by
  let H := F.mapHomologicalComplex (.up ℤ)
  let w := mapIntDoubleIso F L
  let e' := (embedding.extendFunctor _).mapIso
      (((embedding.extendFunctor _).mapHomologicalComplex (.up ℕ)).mapIso e) ≪≫ w.symm
  let π := (extendedColumnIso ((mapDouble F).obj L) p).hom
  have hw : w.inv.f (p : ℤ) ≫ (w.hom.f (p : ℤ) ≫ π) = π := by
    rw [← Category.assoc]
    have hi := HomologicalComplex.congr_hom w.inv_hom_id (p : ℤ)
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hi
    rw [hi, Category.id_comp]
  change e'.hom.f (p : ℤ) ≫ H.map (extendedColumnIso L p).hom ≫ (mapExtendIso F (L.X p) embedding).hom = _
  dsimp only [e', Iso.trans_hom, Iso.symm_hom, HomologicalComplex.comp_f]
  change ((CechToCohomology.natToIntDoubleComplexMap e.hom).f (p : ℤ) ≫ w.inv.f (p : ℤ)) ≫
    H.map (extendedColumnIso L p).hom ≫ (mapExtendIso F (L.X p) embedding).hom = _
  rw [← mapIntDoubleIso_column F L p, Category.assoc, hw]
  exact extendedColumnIso_naturality e.hom p

/-- The comparison on integer entries restricts to the given map on every
nonnegative bidegree. -/
private lemma comparedBicomplexTerm {K : HomologicalComplex₂ D (.up ℕ) (.up ℕ)}
    {L : HomologicalComplex₂ C (.up ℕ) (.up ℕ)}
    (e : K ≅ (mapDouble F).obj L) (p q : ℕ) :
    let e' := (embedding.extendFunctor _).mapIso
      (((embedding.extendFunctor _).mapHomologicalComplex (.up ℕ)).mapIso e) ≪≫
      (mapIntDoubleIso F L).symm
    (e'.hom.f (p : ℤ)).f (q : ℤ) ≫ F.map (intBicomplexTermIso L p q).hom =
      (intBicomplexTermIso K p q).hom ≫ (e.hom.f p).f q := by
  let e' := (embedding.extendFunctor _).mapIso
      (((embedding.extendFunctor _).mapHomologicalComplex (.up ℕ)).mapIso e) ≪≫
        (mapIntDoubleIso F L).symm
  have hColumn := comparedBicomplexColumn F e p
  have hq : embedding.f q = (q : ℤ) := by simp [embedding]
  let B := (mapExtendIso F (L.X p) embedding).hom.f (q : ℤ)
  have h := HomologicalComplex.congr_hom hColumn (q : ℤ)
  simp only [HomologicalComplex.comp_f] at h
  change (e'.hom.f (p : ℤ)).f (q : ℤ) ≫ F.map ((extendedColumnIso L p).hom.f (q : ℤ)) ≫
      B = (extendedColumnIso K p).hom.f (q : ℤ) ≫
        (HomologicalComplex.extendMap (e.hom.f p) embedding).f (q : ℤ) at h
  change (e'.hom.f (p : ℤ)).f (q : ℤ) ≫ F.map
      ((extendedColumnIso L p).hom.f (q : ℤ) ≫ ((L.X p).extendXIso embedding hq).hom) =
    ((extendedColumnIso K p).hom.f (q : ℤ) ≫ ((K.X p).extendXIso embedding hq).hom) ≫
      (e.hom.f p).f q
  rw [Functor.map_comp, ← CechToCohomology.mapExtendIso_hom_f F (L.X p) embedding hq]
  change _ ≫ _ ≫ B ≫ _ = _
  rw [← Category.assoc _ B, ← Category.assoc, h]
  rw [Category.assoc, HomologicalComplex.extendMap_f _ _ hq]
  simp only [Category.assoc]
  have hc : ((((mapDouble F).obj L).X p).extendXIso embedding hq).inv ≫
      (((F.mapHomologicalComplex (.up ℕ)).obj (L.X p)).extendXIso embedding hq).hom =
        𝟙 _ := ((((mapDouble F).obj L).X p).extendXIso embedding hq).inv_hom_id
  rw [hc, Category.comp_id]


variable (K : Bicomplex C) [hK : K.HasTotal (.up ℤ)]
  [hM : HomologicalComplex₂.HasTotal ((mapIntDouble F).obj K) (.up ℤ)]
  [PreservesColimitsOfSize.{0,0} F]

private def totalDegreeIso (n : ℤ) :
    (sumTotal ((mapIntDouble F).obj K)).X n ≅ F.obj ((sumTotal K).X n) := by
  letI : HasCoproduct (diagonalFamily K n) :=
    hK n
  letI : HasCoproduct (fun i ↦ F.obj (diagonalFamily K n i)) :=
    hM n
  exact (PreservesCoproduct.iso F (diagonalFamily K n)).symm

private lemma totalDegreeIso_injection (p q n : ℤ) (h : p + q = n) :
    sumInjection ((mapIntDouble F).obj K) p q n h ≫ (totalDegreeIso F K n).hom =
      F.map (sumInjection K p q n h) := by
  letI : HasCoproduct (diagonalFamily K n) :=
    hK n
  letI : HasCoproduct (fun i ↦ F.obj (diagonalFamily K n i)) :=
    hM n
  exact ι_comp_sigmaComparison F (diagonalFamily K n) ⟨(p, q), h⟩

/-- Scalar restriction preserves the signed total and its diagonal inclusions. -/
def totalScalarIso :
    sumTotal ((mapIntDouble F).obj K) ≅ (F.mapHomologicalComplex (.up ℤ)).obj (sumTotal K) :=
  HomologicalComplex.Hom.isoOfComponents (totalDegreeIso F K) (by
    intro n m hnm
    have h : n + 1 = m := hnm
    subst m
    apply HomologicalComplex₂.total.hom_ext (.up ℤ)
    intro p q hpq
    have hp : p + 1 + q = n + 1 := by change p + q = n at hpq; omega
    have hq : p + (q + 1) = n + 1 := by change p + q = n at hpq; omega
    rw [← Category.assoc, totalDegreeIso_injection F K p q n hpq]
    change F.map (sumInjection K p q n hpq) ≫ F.map ((sumTotal K).d n (n + 1)) =
      sumInjection ((mapIntDouble F).obj K) p q n hpq ≫
        (sumTotal ((mapIntDouble F).obj K)).d n (n + 1) ≫ _
    rw [← Functor.map_comp, ← Category.assoc (sumInjection ((mapIntDouble F).obj K) p q n hpq),
      DoubleTotalization.sumDifferential K p (p + 1) q (q + 1) n (n + 1) rfl rfl hpq hp hq,
      DoubleTotalization.sumDifferential ((mapIntDouble F).obj K) p (p + 1) q (q + 1)
        n (n + 1) rfl rfl hpq hp hq]
    simp only [Functor.map_add, Units.smul_def, Functor.map_zsmul, Functor.map_comp,
      Preadditive.add_comp, Preadditive.zsmul_comp, Category.assoc,
      totalDegreeIso_injection F K p (q + 1) (n + 1) hq,
      totalDegreeIso_injection F K (p + 1) q (n + 1) hp]
    rfl)

lemma totalScalarIso_injection (p q n : ℤ) (h : p + q = n) :
    sumInjection ((mapIntDouble F).obj K) p q n h ≫ (totalScalarIso F K).hom.f n =
      F.map (sumInjection K p q n h) :=
  totalDegreeIso_injection F K p q n h

open CechToCohomology (resolutionDoubleComplexInt)

def doubleIntIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    doubleComplexInt.{u,r,a,v} R c K ≅
      (mapIntDouble (originalScalars.{u,r,a,v} R c)).obj
        (natToIntDoubleComplex (raisedDouble.{u,r,a,v} R c K)) :=
  let ee := ComplexShape.embeddingUpIntGE 0
  (ee.extendFunctor _).mapIso (((ee.extendFunctor _).mapHomologicalComplex (.up ℕ)).mapIso
    (doubleIso.{u,r,a,v} R c K)) ≪≫
    (mapIntDoubleIso (originalScalars.{u,r,a,v} R c) (raisedDouble.{u,r,a,v} R c K)).symm

/-- The promoted comparison has the same coordinate map on every total summand. -/
def signedTotalIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    sumTotal (doubleComplexInt.{u,r,a,v} R c K) ≅
      ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℤ)).obj
        (sumTotal (natToIntDoubleComplex (raisedDouble.{u,r,a,v} R c K))) :=
  HomologicalComplex₂.total.mapIso (doubleIntIso.{u,r,a,v} R c K) (.up ℤ) ≪≫
    totalScalarIso (originalScalars.{u,r,a,v} R c) (natToIntDoubleComplex (raisedDouble.{u,r,a,v} R c K))

lemma signedTotalIso_injection (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (p q n : ℤ) (h : p + q = n) :
    sumInjection (doubleComplexInt.{u,r,a,v} R c K) p q n h ≫
        (signedTotalIso.{u,r,a,v} R c K).hom.f n =
      ((doubleIntIso.{u,r,a,v} R c K).hom.f p).f q ≫
        (originalScalars.{u,r,a,v} R c).map
          (sumInjection (natToIntDoubleComplex (raisedDouble.{u,r,a,v} R c K)) p q n h) := by
  dsimp only [signedTotalIso, Iso.trans_hom, HomologicalComplex.comp_f, HomologicalComplex₂.total.mapIso]
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc, totalScalarIso_injection]

/-- The signed comparison carries the original column filtration to the
raised column filtration, viewed over the original section ring. -/
lemma signedTotalIso_filtration (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (D : ColumnSpectralData (doubleComplexInt.{u,r,a,v} R c K))
    (E : ColumnSpectralData (natToIntDoubleComplex (raisedDouble.{u,r,a,v} R c K)))
    (p n : ℤ) :
    Subobject.mk ((D.filtration.piece p n).arrow ≫ (signedTotalIso.{u,r,a,v} R c K).hom.f n) =
      Subobject.mk ((originalScalars.{u,r,a,v} R c).map ((E.filtration.piece p n).arrow)) := by
  let e := doubleIntIso.{u,r,a,v} R c K
  let f (p q : ℤ) := (HomologicalComplex.eval _ (.up ℤ) q).mapIso
    ((HomologicalComplex.eval _ (.up ℤ) p).mapIso e)
  exact filtration_piece_transport (originalScalars.{u,r,a,v} R c)
    D.filtration E.filtration D.formula E.formula (signedTotalIso.{u,r,a,v} R c K)
    f (signedTotalIso_injection.{u,r,a,v} R c K) p n

/-- The integer bicomplex comparison agrees on every actual tuple section
with the original cover and coefficient comparison. -/
lemma doubleIntIso_apply (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (p q : ℕ) (x : Cochains R (K.X q).val c p) :
    (((intBicomplexTermIso (doubleComplex.{u,r,a,v} R c K) p q).inv) ≫
      ((doubleIntIso.{u,r,a,v} R c K).hom.f (p : ℤ)).f (q : ℤ) ≫
        (originalScalars.{u,r,a,v} R c).map
          (intBicomplexTermIso (raisedDouble.{u,r,a,v} R c K) p q).hom) x =
      cochainComparison.{u,r,a,v} R (K.X q) c p x := by
  have h : ((doubleIntIso.{u,r,a,v} R c K).hom.f (p : ℤ)).f (q : ℤ) ≫
      (originalScalars.{u,r,a,v} R c).map (intBicomplexTermIso (raisedDouble.{u,r,a,v} R c K) p q).hom =
      (intBicomplexTermIso (doubleComplex.{u,r,a,v} R c K) p q).hom ≫
        ((doubleIso.{u,r,a,v} R c K).hom.f p).f q :=
    comparedBicomplexTerm (originalScalars.{u,r,a,v} R c) (doubleIso.{u,r,a,v} R c K) p q
  rw [h, Iso.inv_hom_id_assoc]
  rfl

/-- Lift the prescribed section comparison to the integer resolution complexes. -/
def intLiftedSectionsIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    intSections.{u,r,a,v} R c K ≅
      ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℤ)).obj
        ((raisedLiftedSections.{u,r,a,v} R c K).extend embedding) :=
  (embedding.extendFunctor _).mapIso (liftedSectionsIso.{u,r,a,v} R c K) ≪≫
    (mapExtendIso (originalScalars.{u,r,a,v} R c) (raisedLiftedSections.{u,r,a,v} R c K) embedding).symm

private lemma intLiftedSectionsIso_coordinate (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (q : ℕ) :
    let hq : embedding.f q = (q : ℤ) := by simp [embedding]
    (intLiftedSectionsIso.{u,r,a,v} R c K).hom.f (q : ℤ) ≫
        (originalScalars.{u,r,a,v} R c).map
          ((raisedLiftedSections.{u,r,a,v} R c K).extendXIso embedding hq).hom =
      ((liftedSections.{u,r,a,v} R c K).extendXIso embedding hq).hom ≫
        (liftedSectionsIso.{u,r,a,v} R c K).hom.f q := by
  let hq : embedding.f q = (q : ℤ) := by simp [embedding]
  let S := originalScalars.{u,r,a,v} R c
  let Q := raisedLiftedSections.{u,r,a,v} R c K
  let e := mapExtendIso S Q embedding
  have he : e.inv.f (q : ℤ) ≫ S.map (Q.extendXIso embedding hq).hom =
      (((S.mapHomologicalComplex (.up ℕ)).obj Q).extendXIso embedding hq).hom := by
    rw [← CechToCohomology.mapExtendIso_hom_f S Q embedding hq]
    have hi := HomologicalComplex.congr_hom e.inv_hom_id (q : ℤ)
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hi
    rw [← Category.assoc]
    exact congrArg (fun f => f ≫ (((S.mapHomologicalComplex (.up ℕ)).obj Q).extendXIso embedding hq).hom) hi
      |>.trans (Category.id_comp _)
  dsimp only [intLiftedSectionsIso, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.comp_f, Category.assoc]
  change (HomologicalComplex.extendMap (liftedSectionsIso.{u,r,a,v} R c K).hom embedding).f (q : ℤ) ≫
      e.inv.f (q : ℤ) ≫ S.map (Q.extendXIso embedding hq).hom = _
  rw [he, HomologicalComplex.extendMap_f _ _ hq]
  simp only [Category.assoc]
  have hx := ((((S.mapHomologicalComplex (.up ℕ)).obj Q).extendXIso embedding hq)).inv_hom_id
  change _ ≫ _ ≫ ((((S.mapHomologicalComplex (.up ℕ)).obj Q).extendXIso embedding hq)).inv ≫
    (((S.mapHomologicalComplex (.up ℕ)).obj Q).extendXIso embedding hq).hom = _
  rw [hx, Category.comp_id]

lemma intLiftedSectionsIso_apply (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (q : ℕ) (x : (K.X q).val.obj (op U)) :
    let hq : embedding.f q = (q : ℤ) := by simp [embedding]
    (((liftedSections.{u,r,a,v} R c K).extendXIso embedding hq).inv ≫
      (intLiftedSectionsIso.{u,r,a,v} R c K).hom.f (q : ℤ) ≫
      (originalScalars.{u,r,a,v} R c).map
          ((raisedLiftedSections.{u,r,a,v} R c K).extendXIso embedding hq).hom) (ULift.up x) =
      ULift.up (sectionAtCover.{u,r,a} R (U := U) (K.X q) x) := by
  dsimp only
  rw [intLiftedSectionsIso_coordinate, Iso.inv_hom_id_assoc]
  rfl

/-- The horizontal augmentation on the integer bicomplex is transported
by the same normalized section and tuple comparisons. -/
lemma intHorizontalAugmentation_transport {M : AmbientSheaves.{a} R}
    (J : InjectiveResolution M) :
    let S := originalScalars.{u,r,a,v} R c
    let J' := raisedResolution.{u,r,a} R J
    intHorizontalAugmentation.{u,r,a,v} R c J.cocomplex ≫ (doubleIntIso.{u,r,a,v} R c J.cocomplex).hom.f 0 =
      (intLiftedSectionsIso.{u,r,a,v} R c J.cocomplex).hom ≫
        (S.mapHomologicalComplex (.up ℤ)).map
          (CechToCohomology.resolutionAugmentation (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
            ((transport.{a} R).obj M) J') := by
  let K := J.cocomplex
  let S := originalScalars.{u,r,a,v} R c
  have h : horizontalAugmentation.{u,r,a,v} R c K ≫ (doubleIso.{u,r,a,v} R c K).hom.f 0 =
      (liftedSectionsIso.{u,r,a,v} R c K).hom ≫ (S.mapHomologicalComplex (.up ℕ)).map
        (raisedHorizontalAugmentation.{u,r,a,v} R c K) := by
    apply HomologicalComplex.hom_ext
    intro q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    rintro ⟨x⟩
    exact (InjectiveCechOriginalCoefficients.cochain_comparison.{u,r,a,v} R (K.X q) c).1 x
  exact intZeroColumnTransport S (doubleIso.{u,r,a,v} R c K) (liftedSectionsIso.{u,r,a,v} R c K)
    (horizontalAugmentation.{u,r,a,v} R c K) (raisedHorizontalAugmentation.{u,r,a,v} R c K) h

/-- The row augmentation to the signed total agrees with the actual raised row augmentation. -/
lemma totalAugmentationMap_transport {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    let S := originalScalars.{u,r,a,v} R c
    let J' := raisedResolution.{u,r,a} R J
    totalAugmentationMap.{u,r,a,v} R c J ≫ (signedTotalIso.{u,r,a,v} R c J.cocomplex).hom =
      (intLiftedSectionsIso.{u,r,a,v} R c J.cocomplex).hom ≫
        (S.mapHomologicalComplex (.up ℤ)).map
          (CechToCohomology.resolutionTotalAugmentation (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
            ((transport.{a} R).obj M) J') := by
  let S := originalScalars.{u,r,a,v} R c
  let J' := raisedResolution.{u,r,a} R J
  dsimp only
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    totalAugmentationMap_f, CechToCohomology.resolutionTotalAugmentation_f, Category.assoc,
    signedTotalIso_injection, Functor.map_comp]
  have h := HomologicalComplex.congr_hom (intHorizontalAugmentation_transport.{u,r,a,v} R c J) n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f] at h
  have h' := congrArg (fun f => f ≫ S.map
    (sumInjection (natToIntDoubleComplex (raisedDouble.{u,r,a,v} R c J.cocomplex)) 0 n n (zero_add n))) h
  simp only [Category.assoc] at h'
  exact h'

/-- The homology comparison for an exact scalar functor respects extension by zero. -/
private lemma extendHomologyIso_mapHomologyIso
    {B D : Type*} [Category* B] [Category* D] [Abelian B] [Abelian D]
    (F : B ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex B ℕ) (q : ℕ) :
    let hq : embedding.f q = (q : ℤ) := by simp [embedding]
    let K' := (F.mapHomologicalComplex (.up ℕ)).obj K
    HomologicalComplex.homologyMap (mapExtendIso F K embedding).hom (q : ℤ) ≫
        (K'.extendHomologyIso embedding hq).hom ≫ ((K.sc q).mapHomologyIso F).hom =
      (((K.extend embedding).sc (q : ℤ)).mapHomologyIso F).hom ≫
        F.map (K.extendHomologyIso embedding hq).hom := by
  let hq : embedding.f q = (q : ℤ) := by simp [embedding]
  let K' := (F.mapHomologicalComplex (.up ℕ)).obj K
  let L := (F.mapHomologicalComplex (.up ℤ)).obj (K.extend embedding)
  let e := mapExtendIso F K embedding
  let S := K.sc q
  let T := (K.extend embedding).sc (q : ℤ)
  have hcycles :
      HomologicalComplex.cyclesMap e.hom (q : ℤ) ≫
          (K'.extendCyclesIso embedding hq).hom ≫ (S.mapCyclesIso F).hom =
        (T.mapCyclesIso F).hom ≫ F.map (K.extendCyclesIso embedding hq).hom := by
    apply (cancel_mono (F.map (K.iCycles q))).1
    simp only [Category.assoc]
    change _ ≫ _ ≫ (S.mapCyclesIso F).hom ≫ F.map S.iCycles =
      (T.mapCyclesIso F).hom ≫ F.map (K.extendCyclesIso embedding hq).hom ≫ F.map (K.iCycles q)
    rw [ShortComplex.mapCyclesIso_hom_iCycles, ← Functor.map_comp]
    change _ ≫ _ ≫ K'.iCycles q = _ ≫ F.map (_ ≫ K.iCycles q)
    rw [HomologicalComplex.extendCyclesIso_hom_iCycles,
      HomologicalComplex.extendCyclesIso_hom_iCycles, ← Category.assoc,
      HomologicalComplex.cyclesMap_i, Category.assoc, Functor.map_comp]
    change L.iCycles (q : ℤ) ≫ e.hom.f (q : ℤ) ≫
        (K'.extendXIso embedding hq).hom =
      (T.mapCyclesIso F).hom ≫ F.map T.iCycles ≫ F.map (K.extendXIso embedding hq).hom
    rw [ShortComplex.mapCyclesIso_hom_iCycles_assoc]
    change _ ≫ (mapExtendIso F K embedding).hom.f (q : ℤ) ≫ _ = _
    rw [mapExtendIso_hom_f F K embedding hq]
    rfl
  dsimp only
  apply (cancel_epi (L.homologyπ (q : ℤ))).1
  simp only [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom_assoc]
  change _ ≫ _ ≫ (S.map F).homologyπ ≫ _ =
    (T.map F).homologyπ ≫ (T.mapHomologyIso F).hom ≫ F.map (K.extendHomologyIso embedding hq).hom
  rw [CechToCohomology.homologyπ_mapHomologyIso,
    CechToCohomology.homologyπ_mapHomologyIso_assoc, ← Functor.map_comp]
  change _ = (T.mapCyclesIso F).hom ≫
    F.map ((K.extend embedding).homologyπ (q : ℤ) ≫ (K.extendHomologyIso embedding hq).hom)
  rw [HomologicalComplex.homologyπ_extendHomologyIso_hom, Functor.map_comp]
  have hc := congrArg (fun g => g ≫ F.map (K.homologyπ q)) hcycles
  simp only [Category.assoc] at hc
  exact hc


open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (sectionsValue cohomologyValue)

abbrev sectionScalars :=
  ModuleCat.restrictScalars.{max a u r} (ringAt.{u,r,a} R ((opensEquiv.{max a u r} X).symm U) U
    ((opensEquiv.{max a u r} X).apply_symm_apply U)).toRingHom

private instance sectionScalars_equivalence :
    (sectionScalars.{u,r,a} R (U := U)).IsEquivalence :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{r,max a u r,max a u r}
    (ringAt.{u,r,a} R ((opensEquiv.{max a u r} X).symm U) U
      ((opensEquiv.{max a u r} X).apply_symm_apply U))).isEquivalence_functor

abbrev raisedSections (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :=
  (((transport.{a} R) ⋙ SheafOfModules.evaluation (liftedRing.{a} R)
      (op ((opensEquiv.{max a u r} X).symm U))).mapHomologicalComplex (.up ℕ)).obj K

/-- The ordinary section comparison in each degree before applying the carrier lift. -/
def sectionScalarIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    sectionComplex.{u,r,a} R U K ≅
      ((sectionScalars.{u,r,a} R (U := U)).mapHomologicalComplex (.up ℕ)).obj
        (raisedSections.{u,r,a} R (U := U) K) :=
  HomologicalComplex.Hom.isoOfComponents (fun q ↦
    (show ((sectionComplex.{u,r,a} R U K).X q) ≃ₗ[sectionRing R U]
        (((sectionScalars.{u,r,a} R (U := U)).mapHomologicalComplex (.up ℕ)).obj
          (raisedSections.{u,r,a} R (U := U) K)).X q from
      { toAddEquiv := sectionAtCover.{u,r,a} R (U := U) (K.X q)
        map_smul' := sectionAt_smul.{u,r,a} R (K.X q) ((opensEquiv.{max a u r} X).apply_symm_apply U) }
    ).toModuleIso) (by
      intro q q' _
      apply ModuleCat.hom_ext
      ext x : 1
      exact (sectionAt_map.{u,r,a} R (K.d q q') _ _
        ((opensEquiv.{max a u r} X).apply_symm_apply U) x).symm)

private lemma liftedSectionsIso_eq_map_sectionScalarIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    liftedSectionsIso.{u,r,a,v} R c K =
      ((sectionLift.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).mapIso
        (sectionScalarIso.{u,r,a} R (U := U) K) := by
  apply Iso.ext
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  ext x : 1
  rfl


/-- Homology of the integer section comparison is the carrier lift of the
comparison induced by the original degreewise section maps. -/
lemma intLiftedSectionsIso_homology (K : CochainComplex (AmbientSheaves.{a} R) ℕ) (n : ℕ) :
    let S := originalScalars.{u,r,a,v} R c
    let S₀ := sectionScalars.{u,r,a} R (U := U)
    let H := CechToCohomology.sectionLift (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
    let F := sectionLift.{u,r,a,v} R c
    let P := sectionComplex.{u,r,a} R U K
    let Q := raisedSections.{u,r,a} R (U := U) K
    let P' := liftedSections.{u,r,a,v} R c K
    let Q' := raisedLiftedSections.{u,r,a,v} R c K
    let h : embedding.f n = (n : ℤ) := by simp [embedding]
    HomologicalComplex.homologyMap (intLiftedSectionsIso.{u,r,a,v} R c K).hom (n : ℤ) ≫
        (((Q'.extend embedding).sc (n : ℤ)).mapHomologyIso S).hom ≫
        S.map ((Q'.extendHomologyIso embedding h).hom ≫ ((Q.sc n).mapHomologyIso H).hom) =
      (P'.extendHomologyIso embedding h).hom ≫ ((P.sc n).mapHomologyIso F).hom ≫
        F.map (HomologicalComplex.homologyMap (sectionScalarIso.{u,r,a} R (U := U) K).hom n ≫
          ((Q.sc n).mapHomologyIso S₀).hom) := by
  let S := originalScalars.{u,r,a,v} R c
  let S₀ := sectionScalars.{u,r,a} R (U := U)
  let H := CechToCohomology.sectionLift (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
  let F := sectionLift.{u,r,a,v} R c
  let P := sectionComplex.{u,r,a} R U K
  let Q := raisedSections.{u,r,a} R (U := U) K
  let P' := liftedSections.{u,r,a,v} R c K
  let Q' := raisedLiftedSections.{u,r,a,v} R c K
  let z := mapExtendIso S Q' embedding
  let e := liftedSectionsIso.{u,r,a,v} R c K
  let g := sectionScalarIso.{u,r,a} R (U := U) K
  let h : embedding.f n = (n : ℤ) := by simp [embedding]
  have hExt :
      HomologicalComplex.homologyMap z.inv (n : ℤ) ≫
          (((Q'.extend embedding).sc (n : ℤ)).mapHomologyIso S).hom ≫
          S.map (Q'.extendHomologyIso embedding h).hom =
        (((S.mapHomologicalComplex (.up ℕ)).obj Q').extendHomologyIso embedding h).hom ≫
          ((Q'.sc n).mapHomologyIso S).hom := by
    rw [← extendHomologyIso_mapHomologyIso S Q' n]
    change HomologicalComplex.homologyMap z.inv (n : ℤ) ≫
      HomologicalComplex.homologyMap z.hom (n : ℤ) ≫ _ = _
    rw [← Category.assoc, ← HomologicalComplex.homologyMap_comp, z.inv_hom_id,
      HomologicalComplex.homologyMap_id, Category.id_comp]
  have hComp :
      ((Q'.sc n).mapHomologyIso S).hom ≫ S.map ((Q.sc n).mapHomologyIso H).hom =
        ((((S₀.mapHomologicalComplex (.up ℕ)).obj Q).sc n).mapHomologyIso F).hom ≫
          F.map ((Q.sc n).mapHomologyIso S₀).hom := by
    change (((Q.sc n).map H).mapHomologyIso S).hom ≫ S.map ((Q.sc n).mapHomologyIso H).hom =
      (((Q.sc n).map S₀).mapHomologyIso F).hom ≫ F.map ((Q.sc n).mapHomologyIso S₀).hom
    rw [← CechToCohomology.mapHomologyIso_comp_hom, ← CechToCohomology.mapHomologyIso_comp_hom]
    rfl
  have hLift := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) n).map g.hom) F
  change HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map g.hom) n ≫
      ((((S₀.mapHomologicalComplex (.up ℕ)).obj Q).sc n).mapHomologyIso F).hom =
    ((P.sc n).mapHomologyIso F).hom ≫ F.map (HomologicalComplex.homologyMap g.hom n) at hLift
  change HomologicalComplex.homologyMap (HomologicalComplex.extendMap e.hom embedding ≫ z.inv)
      (n : ℤ) ≫ (((Q'.extend embedding).sc (n : ℤ)).mapHomologyIso S).hom ≫
        S.map ((Q'.extendHomologyIso embedding h).hom ≫ ((Q.sc n).mapHomologyIso H).hom) =
    (P'.extendHomologyIso embedding h).hom ≫ ((P.sc n).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap g.hom n ≫ ((Q.sc n).mapHomologyIso S₀).hom)
  simp only [HomologicalComplex.homologyMap_comp, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hExt, HomologicalComplex.extendHomologyIso_hom_naturality_assoc, hComp]
  change _ ≫ HomologicalComplex.homologyMap (liftedSectionsIso.{u,r,a,v} R c K).hom n ≫ _ = _
  rw [liftedSectionsIso_eq_map_sectionScalarIso]
  change _ ≫ HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map g.hom) n ≫ _ = _
  rw [reassoc_of% hLift]


open CechToCohomology (sectionCohomologyResolutionIso liftedSectionHomologyIso
  resolutionAbutmentIso resolutionAbutmentIso_agrees resolutionTotalAugmentation)

lemma liftedSectionModelMap_transport {M : AmbientSheaves.{a} R}
    (J : InjectiveResolution M) (n : ℕ)
    (τ : (cohomologyValue.{a,u,r} R U n).obj M ≅
      (sectionScalars.{u,r,a} R (U := U)).obj
        ((sectionCohomology (liftedRing.{a} R) ((opensEquiv.{max a u r} X).symm U) n).obj
          ((transport.{a} R).obj M)))
    (hτ :
      let W := (opensEquiv.{max a u r} X).symm U
      let S₀ := sectionScalars.{u,r,a} R (U := U)
      let Q := raisedSections.{u,r,a} R (U := U) J.cocomplex
      HomologicalComplex.homologyMap (sectionScalarIso.{u,r,a} R (U := U) J.cocomplex).hom n ≫
        ((Q.sc n).mapHomologyIso S₀).hom ≫
        S₀.map (sectionCohomologyResolutionIso (liftedRing.{a} R) W
          ((transport.{a} R).obj M) (raisedResolution.{u,r,a} R J) n).inv =
        sectionModelMap.{u,r,a} R U J n ≫ τ.hom) :
    let W := (opensEquiv.{max a u r} X).symm U
    let S := originalScalars.{u,r,a,v} R c
    let R' := liftedRing.{a} R
    let c' := liftCover.{u,a,r,v} c
    let M' := (transport.{a} R).obj M
    let J' := raisedResolution.{u,r,a} R J
    let V := CechToCohomology.sectionComplexInt R' c' M' J'
    HomologicalComplex.homologyMap (intLiftedSectionsIso.{u,r,a,v} R c J.cocomplex).hom (n : ℤ) ≫
      ((V.sc (n : ℤ)).mapHomologyIso S).hom ≫
        S.map ((liftedSectionHomologyIso R' c' M' J' n).hom ≫
          (CechToCohomology.sectionLift R' c').map
            (sectionCohomologyResolutionIso R' W M' J' n).inv) =
      liftedSectionModelMap.{u,r,a,v} R c J n ≫ (sectionLift.{u,r,a,v} R c).map τ.hom := by
  let S := originalScalars.{u,r,a,v} R c
  let S₀ := sectionScalars.{u,r,a} R (U := U)
  let F := sectionLift.{u,r,a,v} R c
  let H := CechToCohomology.sectionLift (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
  let P := sectionComplex.{u,r,a} R U J.cocomplex
  let Q := raisedSections.{u,r,a} R (U := U) J.cocomplex
  let P' := liftedSections.{u,r,a,v} R c J.cocomplex
  let Q' := raisedLiftedSections.{u,r,a,v} R c J.cocomplex
  let g := sectionScalarIso.{u,r,a} R (U := U) J.cocomplex
  let b := (sectionCohomologyResolutionIso (liftedRing.{a} R) ((opensEquiv.{max a u r} X).symm U)
    ((transport.{a} R).obj M) (raisedResolution.{u,r,a} R J) n).inv
  let h : embedding.f n = (n : ℤ) := by simp [embedding]
  have hlift := intLiftedSectionsIso_homology.{u,r,a,v} R c J.cocomplex n
  change HomologicalComplex.homologyMap (intLiftedSectionsIso.{u,r,a,v} R c J.cocomplex).hom (n : ℤ) ≫
      (((Q'.extend embedding).sc (n : ℤ)).mapHomologyIso S).hom ≫
      S.map (((Q'.extendHomologyIso embedding h).hom ≫ ((Q.sc n).mapHomologyIso H).hom) ≫ H.map b) =
    (P'.extendHomologyIso embedding h).hom ≫ ((P.sc n).mapHomologyIso F).hom ≫
      F.map (sectionModelMap.{u,r,a} R U J n) ≫ F.map τ.hom
  rw [Functor.map_comp, reassoc_of% hlift]
  change _ ≫ _ ≫ F.map (HomologicalComplex.homologyMap g.hom n ≫ ((Q.sc n).mapHomologyIso S₀).hom) ≫
      F.map (S₀.map b) = _
  rw [← Functor.map_comp, Category.assoc]
  change HomologicalComplex.homologyMap g.hom n ≫ ((Q.sc n).mapHomologyIso S₀).hom ≫ S₀.map b =
      sectionModelMap.{u,r,a} R U J n ≫ τ.hom at hτ
  rw [hτ, Functor.map_comp]

/-- Compatibility of the total abutment with the normalized section comparison. -/
lemma abutmentIso_transport {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℕ)
    (τ : (cohomologyValue.{a,u,r} R U n).obj M ≅
      (sectionScalars.{u,r,a} R (U := U)).obj
        ((sectionCohomology (liftedRing.{a} R) ((opensEquiv.{max a u r} X).symm U) n).obj
          ((transport.{a} R).obj M)))
    (hτ :
      let W := (opensEquiv.{max a u r} X).symm U
      let S₀ := sectionScalars.{u,r,a} R (U := U)
      let Q := raisedSections.{u,r,a} R (U := U) J.cocomplex
      HomologicalComplex.homologyMap (sectionScalarIso.{u,r,a} R (U := U) J.cocomplex).hom n ≫
        ((Q.sc n).mapHomologyIso S₀).hom ≫
        S₀.map (sectionCohomologyResolutionIso (liftedRing.{a} R) W
          ((transport.{a} R).obj M) (raisedResolution.{u,r,a} R J) n).inv =
        sectionModelMap.{u,r,a} R U J n ≫ τ.hom) :
    let R' := liftedRing.{a} R
    let c' := liftCover.{u,a,r,v} c
    let M' := (transport.{a} R).obj M
    let J' := raisedResolution.{u,r,a} R J
    let S := originalScalars.{u,r,a,v} R c
    let T := sumTotal (CechToCohomology.resolutionDoubleComplexInt R' c' M' J')
    HomologicalComplex.homologyMap (signedTotalIso.{u,r,a,v} R c J.cocomplex).hom (n : ℤ) ≫
        ((T.sc (n : ℤ)).mapHomologyIso S).hom ≫ S.map (resolutionAbutmentIso R' c' M' J' n).hom =
      (abutmentIso.{u,r,a,v} R c J n).hom ≫ (sectionLift.{u,r,a,v} R c).map τ.hom := by
  let R' := liftedRing.{a} R
  let c' := liftCover.{u,a,r,v} c
  let M' := (transport.{a} R).obj M
  let J' := raisedResolution.{u,r,a} R J
  let S := originalScalars.{u,r,a,v} R c
  let V := CechToCohomology.sectionComplexInt R' c' M' J'
  let T := sumTotal (CechToCohomology.resolutionDoubleComplexInt R' c' M' J')
  let β := resolutionTotalAugmentation R' c' M' J'
  let α := totalAugmentationMap.{u,r,a,v} R c J
  let t := signedTotalIso.{u,r,a,v} R c J.cocomplex
  let e := intLiftedSectionsIso.{u,r,a,v} R c J.cocomplex
  have h := congrArg (fun f => HomologicalComplex.homologyMap f (n : ℤ))
    (totalAugmentationMap_transport.{u,r,a,v} R c J)
  simp only [HomologicalComplex.homologyMap_comp] at h
  have hn := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) (n : ℤ)).map β) S
  change HomologicalComplex.homologyMap ((S.mapHomologicalComplex (.up ℤ)).map β) (n : ℤ) ≫
      ((T.sc (n : ℤ)).mapHomologyIso S).hom =
    ((V.sc (n : ℤ)).mapHomologyIso S).hom ≫ S.map (HomologicalComplex.homologyMap β (n : ℤ)) at hn
  have ha : HomologicalComplex.homologyMap α (n : ℤ) ≫ (abutmentIso.{u,r,a,v} R c J n).hom =
      liftedSectionModelMap.{u,r,a,v} R c J n := by
    simp [α, abutmentIso]
  dsimp only
  apply (cancel_epi (HomologicalComplex.homologyMap α (n : ℤ))).1
  change HomologicalComplex.homologyMap α (n : ℤ) ≫ HomologicalComplex.homologyMap t.hom (n : ℤ) ≫
      ((T.sc (n : ℤ)).mapHomologyIso S).hom ≫ S.map (resolutionAbutmentIso R' c' M' J' n).hom =
    HomologicalComplex.homologyMap α (n : ℤ) ≫ (abutmentIso.{u,r,a,v} R c J n).hom ≫
      (sectionLift.{u,r,a,v} R c).map τ.hom
  rw [reassoc_of% h, reassoc_of% hn, reassoc_of% ha, ← Functor.map_comp]
  change HomologicalComplex.homologyMap e.hom (n : ℤ) ≫ ((V.sc (n : ℤ)).mapHomologyIso S).hom ≫
    S.map (HomologicalComplex.homologyMap β (n : ℤ) ≫ (resolutionAbutmentIso R' c' M' J' n).hom) = _
  rw [resolutionAbutmentIso_agrees R' c' M' J' n]
  exact liftedSectionModelMap_transport.{u,r,a,v} R c J n τ hτ

theorem signed_total_transport :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.signedTotalTransport.{u,r,a,v} := by
  intro X R U A c M J
  letI := ambient_enough_injectives.{a,u,r} X R
  refine ⟨raisedResolution.{u,r,a} R J, rfl, heq_of_eq (raisedResolution_ι_zero.{u,r,a} R J),
    doubleIntIso.{u,r,a,v} R c J.cocomplex, signedTotalIso.{u,r,a,v} R c J.cocomplex,
    ?_, signedTotalIso_injection.{u,r,a,v} R c J.cocomplex,
    ?_, ?_⟩
  · intro p q x
    exact heq_of_eq (doubleIntIso_apply.{u,r,a,v} R c J.cocomplex p q x)
  · intro D E
    let h := signedTotalIso_filtration.{u,r,a,v} R c J.cocomplex D E
    let S := originalScalars.{u,r,a,v} R c
    let e := doubleIntIso.{u,r,a,v} R c J.cocomplex
    let t := signedTotalIso.{u,r,a,v} R c J.cocomplex
    exact ⟨h, limiting_transport S D.filtration E.filtration t h D.pages E.pages,
      pages_transport S D.filtration E.filtration t h D.pages E.pages,
      column_second_transport S D E e t h (signedTotalIso_injection.{u,r,a,v} R c J.cocomplex)⟩
  · let α := totalAugmentationMap.{u,r,a,v} R c J
    let β := CechToCohomology.resolutionTotalAugmentation (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
      ((transport.{a} R).obj M) (raisedResolution.{u,r,a} R J)
    refine ⟨intLiftedSectionsIso.{u,r,a,v} R c J.cocomplex, α, β, inferInstance, inferInstance,
      ?_, totalAugmentationMap_f.{u,r,a,v} R c J,
      CechToCohomology.resolutionTotalAugmentation_f (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
        ((transport.{a} R).obj M) (raisedResolution.{u,r,a} R J),
      totalAugmentationMap_transport.{u,r,a,v} R c J⟩
    intro q x
    exact heq_of_eq (intLiftedSectionsIso_apply.{u,r,a,v} R c J.cocomplex q x)

end SignedTotal

section HomologyTransport

open CechToCohomology (mapHomologyIso_comp_hom)

variable {P Q A B : Type*} [Category* P] [Category* Q] [Category* A] [Category* B]
  [Abelian P] [Abelian Q] [Abelian A] [Abelian B]
  (E : P ⥤ Q) (F : P ⥤ A) (G : Q ⥤ B) (T : B ⥤ A)
  [E.Additive] [F.Additive] [G.Additive] [T.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
  [PreservesFiniteColimits E] [PreservesFiniteColimits F] [PreservesFiniteColimits G]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]

private lemma compareExactModel (C : ShortComplex P) (η : F ≅ E ⋙ G ⋙ T)
    {M : P} {N : Q} (i : M ≅ C.homology) (j : N ≅ (C.map E).homology) :
    ((C.mapHomologyIso F).hom ≫ F.map i.inv) ≫
      (η.hom.app M ≫ (G ⋙ T).map (E.map i.hom ≫ (C.mapHomologyIso E).inv ≫ j.inv)) =
    ShortComplex.homologyMap (C.mapNatTrans η.hom) ≫
      (((C.map E).map G).mapHomologyIso T).hom ≫
        T.map (((C.map E).mapHomologyIso G).hom ≫ G.map j.inv) := by
  let L := G ⋙ T
  have hn : F.map i.inv ≫ η.hom.app M = η.hom.app C.homology ≫ L.map (E.map i.inv) :=
    η.hom.naturality i.inv
  have hh : (C.mapHomologyIso F).hom ≫ η.hom.app C.homology =
      ShortComplex.homologyMap (C.mapNatTrans η.hom) ≫ (C.mapHomologyIso (E ⋙ L)).hom := by
    rw [η.hom.app_homology C, Iso.hom_inv_id_assoc]
  have hcomp : (C.mapHomologyIso (E ⋙ L)).hom =
      (((C.map E).map G).mapHomologyIso T).hom ≫
        T.map ((C.map E).mapHomologyIso G).hom ≫ L.map (C.mapHomologyIso E).hom := by
    rw [mapHomologyIso_comp_hom C E L, mapHomologyIso_comp_hom (C.map E) G T, Category.assoc]
  have hc : L.map (E.map i.inv) ≫ L.map
      (E.map i.hom ≫ (C.mapHomologyIso E).inv ≫ j.inv) =
      L.map ((C.mapHomologyIso E).inv ≫ j.inv) := by
    rw [← L.map_comp, ← Category.assoc, ← E.map_comp, Iso.inv_hom_id, E.map_id, Category.id_comp]
  have hd : L.map (C.mapHomologyIso E).hom ≫ L.map ((C.mapHomologyIso E).inv ≫ j.inv) =
      L.map j.inv := by rw [← L.map_comp, Iso.hom_inv_id_assoc]
  calc
    _ = (C.mapHomologyIso F).hom ≫ η.hom.app C.homology ≫
        L.map ((C.mapHomologyIso E).inv ≫ j.inv) := by
      rw [Category.assoc, ← Category.assoc (F.map i.inv), hn, Category.assoc, hc]
    _ = _ := by
      rw [← Category.assoc, hh, hcomp]
      simp only [Category.assoc, hd, T.map_comp]
      rfl

end HomologyTransport

section LocalCarrier

open CechToCohomology (mapHomologyIso_comp_hom homologyπ_mapHomologyIso)

private lemma presheafSectionAt_restrict (F : AmbientPresheaves.{a} R)
    {V W : Opens X} {V' W' : Opens (liftedSpace.{max a u r} X)}
    (hV : opensEquiv.{max a u r} X V' = V) (hW : opensEquiv.{max a u r} X W' = W)
    (i : V ⟶ W) (i' : V' ⟶ W') (s : F.obj (op W)) :
    presheafSectionAt.{u,r,a} R F V' V hV (F.map i.op s) =
      ((transportPresheaf.{a} R).obj F).map i'.op (presheafSectionAt.{u,r,a} R F W' W hW s) := by
  subst V W
  rfl

private lemma presheafSectionAt_scalar (F : AmbientPresheaves.{a} R)
    {V W : Opens X} {V' W' : Opens (liftedSpace.{max a u r} X)}
    (hV : opensEquiv.{max a u r} X V' = V) (hW : opensEquiv.{max a u r} X W' = W)
    (i : V ⟶ W) (i' : V' ⟶ W') (b : sectionRing R W) (s : F.obj (op V)) :
    presheafSectionAt.{u,r,a} R F V' V hV (R.obj.map i.op b • s) =
      (liftedRing.{a} R).obj.map i'.op (ringAt.{u,r,a} R W' W hW b) •
        presheafSectionAt.{u,r,a} R F V' V hV s := by
  subst V W
  rfl

private lemma presheafSectionAt_map {F G : AmbientPresheaves.{a} R} (f : F ⟶ G)
    {W : Opens (liftedSpace.{max a u r} X)} {V : Opens X}
    (h : opensEquiv.{max a u r} X W = V) (s : F.obj (op V)) :
    presheafSectionAt.{u,r,a} R G W V h (f.app (op V) s) =
      ((transportPresheaf.{a} R).map f).app (op W) (presheafSectionAt.{u,r,a} R F W V h s) := by
  subst V
  rfl

private def presheafCochainLinearEquiv (F : AmbientPresheaves.{a} R) (p : ℕ) :
    (cochainComplex.{u,r,a,v} R c F).X p ≃ₗ[sectionRing R U]
      (((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj
        (CechToCohomology.cechComplex (liftedRing.{a} R)
          (liftCover.{u,a,r,v} c) ((transportPresheaf.{a} R).obj F))).X p where
  toAddEquiv := AddEquiv.piCongrRight (fun t ↦
    presheafSectionAt.{u,r,a} R F _ _ (liftCover_tuple.{u,r,a,v} c t))
  map_smul' b s := by
    funext t
    exact presheafSectionAt_scalar.{u,r,a} R F (liftCover_tuple.{u,r,a,v} c t)
      ((opensEquiv.{max a u r} X).apply_symm_apply U)
      (homOfLE (tupleOpen_le c t)) (homOfLE (tupleOpen_le _ t)) b (s t)

/-- The full tuple comparison, also for presheaves of local cohomology. -/
def presheafCochainIso :
    cochainFunctor.{u,r,a,v} R c ≅
      transportPresheaf.{a} R ⋙
        CechToCohomology.cochainFunctor (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ⋙
          (originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ) :=
  NatIso.ofComponents
    (fun F ↦ HomologicalComplex.Hom.isoOfComponents
      (fun p ↦ (presheafCochainLinearEquiv.{u,r,a,v} R c F p).toModuleIso) (by
      intro p q hpq
      have h : p + 1 = q := hpq
      subst q
      change _ ≫ (originalScalars.{u,r,a,v} R c).map
        ((CechToCohomology.cechComplex (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
          ((transportPresheaf.{a} R).obj F)).d p (p + 1)) =
          (cochainComplex.{u,r,a,v} R c F).d p (p + 1) ≫ _
      rw [cochainComplex_d, CechToCohomology.cechComplex_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      symm
      let e := (presheafCochainLinearEquiv.{u,r,a,v} R c F (p + 1)).toAddEquiv
      change e (Cech.differential R F c p s) =
        Cech.differential (liftedRing.{a} R) ((transportPresheaf.{a} R).obj F)
          (liftCover.{u,a,r,v} c) p (presheafCochainLinearEquiv.{u,r,a,v} R c F p s)
      simp only [Cech.differential, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      funext t
      exact presheafSectionAt_restrict.{u,r,a} R F (liftCover_tuple.{u,r,a,v} c t)
        (liftCover_tuple.{u,r,a,v} c (t ∘ i.succAbove))
        (homOfLE (tupleOpen_reindex_le c _ t)) (homOfLE (tupleOpen_reindex_le _ _ t))
        (s (t ∘ i.succAbove))))
    (by
      intro F G f
      apply HomologicalComplex.hom_ext
      intro p
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      funext t
      exact presheafSectionAt_map.{u,r,a} R f (liftCover_tuple.{u,r,a,v} c t) (s t))

/-- The same tuple and same local section comparison in the whole alternating complex. -/
def localCochainIso {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (q : ℕ) :
    cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M) ≅
      ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).obj
        (CechToCohomology.cechComplex (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
          ((CechToCohomology.localCohomology (liftedRing.{a} R) q).obj ((transport.{a} R).obj M))) :=
  localModelCochainIso.{u,r,a,v} R c J q (presheafCochainIso.{u,r,a,v} R c)

lemma localPresheafIso_naturality {M N : AmbientSheaves.{a} R} (f : M ⟶ N)
    (I : InjectiveResolution M) (J : InjectiveResolution N) (φ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    (transportPresheaf.{a} R).map ((localCohomology.{u,r,a} R q).map f) ≫
      (localPresheafIso.{u,r,a} R J q).hom =
    (localPresheafIso.{u,r,a} R I q).hom ≫
      (CechToCohomology.localCohomology (liftedRing.{a} R) q).map ((transport.{a} R).map f) := by
  let P := transportPresheaf.{a} R
  let T := transport.{a} R
  let F := SheafOfModules.forget R
  let G := SheafOfModules.forget (liftedRing.{a} R)
  let e := (T.mapHomologicalComplex (.up ℕ)).map φ
  have he : (raisedResolution.{u,r,a} R I).ι.f 0 ≫ e.f 0 =
      T.map f ≫ (raisedResolution.{u,r,a} R J).ι.f 0 := by
    rw [raisedResolution_ι_zero, raisedResolution_ι_zero]
    change T.map (I.ι.f 0) ≫ T.map (φ.f 0) = T.map f ≫ T.map (J.ι.f 0)
    exact (T.map_comp ..).symm.trans ((T.congr_map hφ).trans (T.map_comp ..))
  have h₁ := I.isoRightDerivedObj_hom_naturality f J φ hφ F q
  have h₂ := (raisedResolution.{u,r,a} R I).isoRightDerivedObj_inv_naturality
    (T.map f) (raisedResolution.{u,r,a} R J) e he G q
  have h₃ := ShortComplex.mapHomologyIso_inv_naturality
    (((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map
      ((F.mapHomologicalComplex (.up ℕ)).map φ))) P
  change P.map ((F.rightDerived q).map f) ≫ (localPresheafIso R J q).hom =
    (localPresheafIso R I q).hom ≫ (G.rightDerived q).map (T.map f)
  simp only [localPresheafIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
  change P.map ((F.rightDerived q).map f) ≫ P.map (J.isoRightDerivedObj F q).hom ≫ _ =
    P.map (I.isoRightDerivedObj F q).hom ≫ _ ≫
      ((raisedResolution.{u,r,a} R I).isoRightDerivedObj G q).inv ≫ _
  rw [← Functor.map_comp_assoc, h₁, Functor.map_comp, Category.assoc, h₂]
  congr 1
  rw [← Category.assoc,
    ← Category.assoc ((((underlyingComplex.{u,r,a} R I.cocomplex).sc q).mapHomologyIso P).inv)]
  exact congrArg (fun g ↦ g ≫ ((raisedResolution.{u,r,a} R J).isoRightDerivedObj G q).inv) h₃

/-- Comparing the local coefficient presheaves is natural in the original sheaf. -/
def localPresheafComparison (q : ℕ) : raisedLocalComparisonType.{u,r,a} R q :=
  NatIso.ofComponents (fun M ↦ localPresheafIso.{u,r,a} R (InjectiveResolution.of M) q) (by
    intro M N f
    exact localPresheafIso_naturality.{u,r,a} R f _ _
      (InjectiveResolution.desc f _ _) (InjectiveResolution.desc_commutes_zero f _ _) q)

lemma localPresheafComparison_model {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (q : ℕ) :
    (localPresheafComparison.{u,r,a} R q).app M = localPresheafIso.{u,r,a} R J q := by
  let I := InjectiveResolution.of M
  have h := localPresheafIso_naturality.{u,r,a} R (𝟙 M) I J
    (InjectiveResolution.desc (𝟙 M) J I) (InjectiveResolution.desc_commutes_zero (𝟙 M) J I) q
  apply Iso.ext
  change (localPresheafIso.{u,r,a} R I q).hom = _
  have ho := (localCohomology.{u,r,a} R q).map_id M
  have hr := (CechToCohomology.localCohomology (liftedRing.{a} R) q).map_id
    ((transport.{a} R).obj M)
  have ht := (transport.{a} R).map_id M
  have hp := (transportPresheaf.{a} R).map_id ((localCohomology.{u,r,a} R q).obj M)
  rw [ho, ht, hr, hp, Category.id_comp, Category.comp_id] at h
  exact h.symm

end LocalCarrier

set_option maxHeartbeats 2200000 in
/-- The exact-product comparison commutes with transport on the entire
horizontal complex, before taking its cohomology in the Čech degree. -/
lemma localCochainIso_verticalComparison {M : AmbientSheaves.{a} R}
    (J : InjectiveResolution M) (q : ℕ) :
    let T := originalScalars.{u,r,a,v} R c
    let B := T.mapHomologicalComplex (.up ℕ)
    let R' := liftedRing.{a} R
    let c' := liftCover.{u,a,r,v} c
    let M' := (transport.{a} R).obj M
    let J' := raisedResolution.{u,r,a} R J
    let G := CechToCohomology.cochainFunctor R' c'
    let L := (G.mapHomologicalComplex (.up ℕ)).obj (CechToCohomology.underlyingComplex R' J'.cocomplex)
    let K := underlyingComplex.{u,r,a} R J.cocomplex
    let h := (NatIso.mapHomologicalComplex (presheafCochainIso.{u,r,a,v} R c) (.up ℕ)).app K
    HomologicalComplex.homologyMap h.hom q ≫ ((L.sc q).mapHomologyIso B).hom ≫
      B.map (CechToCohomology.resolutionVerticalIso R' c' M' J' q).hom =
      (verticalComparison.{u,r,a,v} R c J q).hom ≫ (localCochainIso.{u,r,a,v} R c J q).hom := by
  let R' := liftedRing.{a} R
  let c' := liftCover.{u,a,r,v} c
  let J' := raisedResolution.{u,r,a} R J
  let P := transportPresheaf.{a} R
  let F := cochainFunctor.{u,r,a,v} R c
  let G := CechToCohomology.cochainFunctor R' c'
  let B := (originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)
  let C := (underlyingComplex.{u,r,a} R J.cocomplex).sc q
  let i := J.isoRightDerivedObj (SheafOfModules.forget R) q
  let j := J'.isoRightDerivedObj (SheafOfModules.forget R') q
  exact (compareExactModel P F G B C (presheafCochainIso.{u,r,a,v} R c) i j).symm

set_option maxHeartbeats 2200000 in
theorem local_carrier_transport :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.localCarrierTransport.{u,r,a,v} := by
  intro X R U A c _
  refine ⟨localPresheafComparison.{u,r,a} R, presheafCochainIso.{u,r,a,v} R c,
    fun _ _ _ _ ↦ rfl, inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  intro M J q
  have h := localPresheafComparison_model.{u,r,a} R J q
  refine ⟨congrArg Iso.hom h, ?_⟩
  dsimp only
  have h' := congrArg Iso.hom h
  let G := CechToCohomology.cochainFunctor (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
  let B := (originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)
  change _ = _ ≫ _ ≫ (G ⋙ B).map ((localPresheafComparison.{u,r,a} R q).app M).hom
  rw [h']
  exact localCochainIso_verticalComparison.{u,r,a,v} R c J q


section CoefficientNaturality

open CechToCohomology (abutmentPiece abutmentPieceMap abutmentPieceMap_arrow
  abutmentGradedMap columnSecondPageIso columnSecondPageIso_naturality_assoc
  columnFilteredMap_hom natToIntDoubleComplexVerticalHomologyIso_naturality
  verticalHomologyNatIso_naturality rowTotalAugmentation_naturality
  total_homologyMap_eq_of_augmentation extendMap_homology_eq
  columnAbutmentLimitIso_naturality)
open DoubleComplexFirstPages (verticalHomologyMap)
open FiniteFiltrationConvergence (Stabilized)

variable {M N : AmbientSheaves.{a} R}
variable (I : InjectiveResolution M) (J : InjectiveResolution N)
variable (φ : I.cocomplex ⟶ J.cocomplex)

section
omit [EnoughInjectives (AmbientSheaves.{a} R)]

lemma horizontalAugmentation_naturality :
    (liftedSectionsMap.{u,r,a,v} R c φ) ≫ horizontalAugmentation.{u,r,a,v} R c J.cocomplex =
      horizontalAugmentation.{u,r,a,v} R c I.cocomplex ≫
        (doubleComplexMap.{u,r,a,v} R c φ).f 0 := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  funext t
  let j := (homOfLE (tupleOpen_le c t)).op
  change (J.cocomplex.X q).val.map j ((φ.f q).val.app (op U) s.down) =
    (φ.f q).val.app (op (tupleOpen c t)) ((I.cocomplex.X q).val.map j s.down)
  exact (PresheafOfModules.naturality_apply (φ.f q).val j s.down).symm

lemma verticalAugmentation_naturality (f : M ⟶ N)
    (h : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) :
    cochainMap.{u,r,a,v} R c f.val ≫ verticalAugmentation.{u,r,a,v} R c J =
      verticalAugmentation.{u,r,a,v} R c I ≫
        ((HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)).map
          (doubleComplexMap.{u,r,a,v} R c φ)).f 0 := by
  change (cochainFunctor.{u,r,a,v} R c).map ((SheafOfModules.forget R).map f) ≫
      (cochainFunctor.{u,r,a,v} R c).map ((SheafOfModules.forget R).map (J.ι.f 0)) =
    (cochainFunctor.{u,r,a,v} R c).map ((SheafOfModules.forget R).map (I.ι.f 0)) ≫
      (cochainFunctor.{u,r,a,v} R c).map ((SheafOfModules.forget R).map (φ.f 0))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, h]

private lemma zeroColumnIso_naturality :
    (doubleComplexIntMap.{u,r,a,v} R c φ).f 0 ≫ (zeroColumnIso.{u,r,a,v} R c J.cocomplex).hom =
      (zeroColumnIso.{u,r,a,v} R c I.cocomplex).hom ≫
        HomologicalComplex.extendMap ((doubleComplexMap.{u,r,a,v} R c φ).f 0)
          (ComplexShape.embeddingUpIntGE 0) := by
  change (HomologicalComplex.extendMap _ _).f 0 ≫ _ = _
  rw [HomologicalComplex.extendMap_f _ _ (by simp :
    (ComplexShape.embeddingUpIntGE 0).f (0 : ℕ) = (0 : ℤ))]
  simp only [Category.assoc, zeroColumnIso, Iso.inv_hom_id, Category.comp_id]
  rfl

lemma intHorizontalAugmentation_naturality :
    intSectionsMap.{u,r,a,v} R c φ ≫ intHorizontalAugmentation.{u,r,a,v} R c J.cocomplex =
      intHorizontalAugmentation.{u,r,a,v} R c I.cocomplex ≫ (doubleComplexIntMap.{u,r,a,v} R c φ).f 0 := by
  dsimp only [intSectionsMap, intHorizontalAugmentation]
  rw [← Category.assoc, ← HomologicalComplex.extendMap_comp,
    horizontalAugmentation_naturality.{u,r,a,v} R c I J φ, HomologicalComplex.extendMap_comp]
  simp only [Category.assoc]
  congr 1
  apply (cancel_epi (zeroColumnIso.{u,r,a,v} R c I.cocomplex).hom).1
  apply (cancel_mono (zeroColumnIso.{u,r,a,v} R c J.cocomplex).hom).1
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id] using
    (zeroColumnIso_naturality.{u,r,a,v} R c I J φ).symm

lemma totalAugmentationMap_naturality :
    intSectionsMap.{u,r,a,v} R c φ ≫ totalAugmentationMap.{u,r,a,v} R c J =
      totalAugmentationMap.{u,r,a,v} R c I ≫ HomologicalComplex₂.total.map
        (doubleComplexIntMap.{u,r,a,v} R c φ) (.up ℤ) :=
  rowTotalAugmentation_naturality (intHorizontalAugmentation.{u,r,a,v} R c I.cocomplex)
    (intHorizontalAugmentation.{u,r,a,v} R c J.cocomplex)
    (totalAugmentationMap.{u,r,a,v} R c I) (totalAugmentationMap.{u,r,a,v} R c J)
    (totalAugmentationMap_f.{u,r,a,v} R c I) (totalAugmentationMap_f.{u,r,a,v} R c J)
    (intSectionsMap.{u,r,a,v} R c φ) (doubleComplexIntMap.{u,r,a,v} R c φ)
    (intHorizontalAugmentation_naturality.{u,r,a,v} R c I J φ)

lemma totalHomologyMap_lift_independent (f : M ⟶ N)
    (ψ : I.cocomplex ⟶ J.cocomplex)
    (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (hψ : I.ι.f 0 ≫ ψ.f 0 = f ≫ J.ι.f 0) (n : ℤ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (doubleComplexIntMap.{u,r,a,v} R c φ) (.up ℤ)) n =
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (doubleComplexIntMap.{u,r,a,v} R c ψ) (.up ℤ)) n := by
  apply total_homologyMap_eq_of_augmentation (totalAugmentationMap.{u,r,a,v} R c I)
    (totalAugmentationMap.{u,r,a,v} R c J) (intSectionsMap.{u,r,a,v} R c φ)
    (intSectionsMap.{u,r,a,v} R c ψ) (doubleComplexIntMap.{u,r,a,v} R c φ)
    (doubleComplexIntMap.{u,r,a,v} R c ψ)
    (totalAugmentationMap_naturality.{u,r,a,v} R c I J φ)
    (totalAugmentationMap_naturality.{u,r,a,v} R c I J ψ) n
  apply extendMap_homology_eq
  intro q
  have h : Homotopy φ ψ := by
    apply InjectiveResolution.descHomotopy f
    · apply HomologicalComplex.from_single_hom_ext
      simpa using hφ
    · apply HomologicalComplex.from_single_hom_ext
      simpa using hψ
  let F := sectionsValue.{a,u,r} R U ⋙ sectionLift.{u,r,a,v} R c
  exact (Functor.mapHomotopy F h).homologyMap_eq q

end

lemma liftedSectionModelMap_naturality (f : M ⟶ N)
    (h : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap (intSectionsMap.{u,r,a,v} R c φ) (n : ℤ) ≫
      liftedSectionModelMap.{u,r,a,v} R c J n =
    liftedSectionModelMap.{u,r,a,v} R c I n ≫
      (sectionLift.{u,r,a,v} R c).map ((cohomologyValue.{a,u,r} R U n).map f) := by
  let F := sectionLift.{u,r,a,v} R c
  let g := ((sectionsValue.{a,u,r} R U).mapHomologicalComplex (.up ℕ)).map φ
  let g' := (F.mapHomologicalComplex (.up ℕ)).map g
  have h₁ := HomologicalComplex.extendHomologyIso_hom_naturality g'
    (ComplexShape.embeddingUpIntGE 0) (j := n) (j' := (n : ℤ)) (hj' := by simp)
  have h₂ := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) n).map g) F
  change HomologicalComplex.homologyMap g' n ≫
      (((sectionComplex.{u,r,a} R U J.cocomplex).sc n).mapHomologyIso F).hom =
    (((sectionComplex.{u,r,a} R U I.cocomplex).sc n).mapHomologyIso F).hom ≫
        F.map (HomologicalComplex.homologyMap g n) at h₂
  dsimp only [liftedSectionModelMap]
  change HomologicalComplex.homologyMap
      (HomologicalComplex.extendMap g' (ComplexShape.embeddingUpIntGE 0)) (n : ℤ) ≫ _ = _
  simp only [Category.assoc]
  rw [← Category.assoc, ← Category.assoc]
  erw [h₁]
  have h₂' := congrArg (fun z ↦ z ≫ F.map (sectionModelMap.{u,r,a} R U J n)) h₂
  simp only [Category.assoc] at h₂' ⊢
  erw [h₂']
  have hn := congrArg F.map (sectionModelMap_naturality.{u,r,a} R U f I J φ h n)
  simp only [Functor.map_comp] at hn
  erw [← hn]
  rfl

lemma abutmentIso_naturality (f : M ⟶ N) (h : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    HomologicalComplex.homologyMap (HomologicalComplex₂.total.map
      (doubleComplexIntMap.{u,r,a,v} R c φ) (.up ℤ)) (n : ℤ) ≫
        (abutmentIso.{u,r,a,v} R c J n).hom =
      (abutmentIso.{u,r,a,v} R c I n).hom ≫
        (sectionLift.{u,r,a,v} R c).map ((cohomologyValue.{a,u,r} R U n).map f) := by
  have ha := congrArg (fun g => HomologicalComplex.homologyMap g (n : ℤ))
    (totalAugmentationMap_naturality.{u,r,a,v} R c I J φ)
  simp only [HomologicalComplex.homologyMap_comp] at ha
  apply (cancel_epi (HomologicalComplex.homologyMap (totalAugmentationMap.{u,r,a,v} R c I)
    (n : ℤ))).1
  rw [← Category.assoc, ← ha]
  simp only [abutmentIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Category.assoc, IsIso.hom_inv_id_assoc]
  exact liftedSectionModelMap_naturality.{u,r,a,v} R c I J φ f h n

lemma abutmentPieceMap_naturality (f : M ⟶ N) (h : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0)
    (n : ℕ) (p : ℤ) :
    abutmentPieceMap (filteredMap.{u,r,a,v} R c I J φ) (n : ℤ)
        (abutmentIso.{u,r,a,v} R c I n) (abutmentIso.{u,r,a,v} R c J n) p ≫
      (abutmentPiece (spectralData.{u,r,a,v} R c J).filtration (n : ℤ)
        (abutmentIso.{u,r,a,v} R c J n) p).arrow =
    (abutmentPiece (spectralData.{u,r,a,v} R c I).filtration (n : ℤ)
      (abutmentIso.{u,r,a,v} R c I n) p).arrow ≫
        (sectionLift.{u,r,a,v} R c).map ((cohomologyValue.{a,u,r} R U n).map f) := by
  apply abutmentPieceMap_arrow
  rw [filteredMap, columnFilteredMap_hom]
  exact abutmentIso_naturality.{u,r,a,v} R c I J φ f h n

/-- The identity coefficient map compares the two image filtrations as
subobjects of the same derived section module. -/
lemma abutmentPiece_resolution_eq (I J : InjectiveResolution M) (n : ℕ) (p : ℤ) :
    abutmentPiece (spectralData.{u,r,a,v} R c I).filtration (n : ℤ)
        (abutmentIso.{u,r,a,v} R c I n) p =
      abutmentPiece (spectralData.{u,r,a,v} R c J).filtration (n : ℤ)
        (abutmentIso.{u,r,a,v} R c J n) p := by
  have leOfLift (I₁ I₂ : InjectiveResolution M) :
      abutmentPiece (spectralData.{u,r,a,v} R c I₁).filtration (n : ℤ)
          (abutmentIso.{u,r,a,v} R c I₁ n) p ≤
        abutmentPiece (spectralData.{u,r,a,v} R c I₂).filtration (n : ℤ)
          (abutmentIso.{u,r,a,v} R c I₂ n) p := by
    let φ := InjectiveResolution.desc (𝟙 M) I₂ I₁
    refine Subobject.le_of_comm
      (abutmentPieceMap (filteredMap.{u,r,a,v} R c I₁ I₂ φ) (n : ℤ)
        (abutmentIso.{u,r,a,v} R c I₁ n) (abutmentIso.{u,r,a,v} R c I₂ n) p) ?_
    simpa using abutmentPieceMap_naturality.{u,r,a,v} R c I₁ I₂ φ (𝟙 M)
      (InjectiveResolution.desc_commutes_zero (𝟙 M) I₂ I₁) n p
  exact le_antisymm (leOfLift I J) (leOfLift J I)

lemma verticalComparison_naturality (f : M ⟶ N)
    (h : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    HomologicalComplex.homologyMap
        (((cochainFunctor.{u,r,a,v} R c).mapHomologicalComplex (.up ℕ)).map
          (((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ)) q ≫
      (verticalComparison.{u,r,a,v} R c J q).hom =
    (verticalComparison.{u,r,a,v} R c I q).hom ≫
      (cochainFunctor.{u,r,a,v} R c).map ((localCohomology.{u,r,a} R q).map f) := by
  let F := cochainFunctor.{u,r,a,v} R c
  let g := ((SheafOfModules.forget R).mapHomologicalComplex (.up ℕ)).map φ
  have h₁ := I.isoRightDerivedObj_inv_naturality f J φ h (SheafOfModules.forget R) q
  change (I.isoRightDerivedObj (SheafOfModules.forget R) q).inv ≫
      (localCohomology.{u,r,a} R q).map f =
    HomologicalComplex.homologyMap g q ≫ (J.isoRightDerivedObj (SheafOfModules.forget R) q).inv at h₁
  have h₂ := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map g) F
  change HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map g) q ≫
      (((underlyingComplex.{u,r,a} R J.cocomplex).sc q).mapHomologyIso F).hom =
    (((underlyingComplex.{u,r,a} R I.cocomplex).sc q).mapHomologyIso F).hom ≫
      F.map (HomologicalComplex.homologyMap g q) at h₂
  dsimp only [verticalComparison, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, h₂, Category.assoc, ← Functor.map_comp, ← h₁, Functor.map_comp]
  simp only [Category.assoc]
  rfl

lemma verticalIso_naturality (f : M ⟶ N)
    (h : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    verticalHomologyMap (doubleComplexInt.{u,r,a,v} R c I.cocomplex)
      (doubleComplexIntMap.{u,r,a,v} R c φ) (q : ℤ) ≫ (verticalIso.{u,r,a,v} R c J q).hom =
    (verticalIso.{u,r,a,v} R c I q).hom ≫ localCechComplexIntMap.{u,r,a,v} R c q f := by
  let K := doubleComplex.{u,r,a,v} R c I.cocomplex
  let L := doubleComplex.{u,r,a,v} R c J.cocomplex
  let ψ := doubleComplexMap.{u,r,a,v} R c φ
  let E := (ComplexShape.embeddingUpIntGE 0).extendFunctor
    (CochainModules.{u,r,a,v} R (U := U))
  have hn :
      ((HomologicalComplex.homologyFunctor _ (.up ℕ) q).mapHomologicalComplex (.up ℕ)).map ψ ≫
        (CechToCohomology.verticalHomologyNatIso L q ≪≫ verticalComparison.{u,r,a,v} R c J q).hom =
      (CechToCohomology.verticalHomologyNatIso K q ≪≫ verticalComparison.{u,r,a,v} R c I q).hom ≫
        (cochainFunctor.{u,r,a,v} R c).map ((localCohomology.{u,r,a} R q).map f) := by
    dsimp only [Iso.trans_hom]
    rw [← Category.assoc, verticalHomologyNatIso_naturality, Category.assoc]
    have hh := congrArg (fun g => (CechToCohomology.verticalHomologyNatIso K q).hom ≫ g)
      (verticalComparison_naturality.{u,r,a,v} R c I J φ f h q)
    simp only [Category.assoc] at hh ⊢
    convert hh using 1 <;> rfl
  dsimp only [verticalIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc]
  change (verticalHomologyMap (CechToCohomology.natToIntDoubleComplex K)
      (CechToCohomology.natToIntDoubleComplexMap ψ) (q : ℤ) ≫ _) ≫ _ = _
  rw [natToIntDoubleComplexVerticalHomologyIso_naturality, Category.assoc]
  have hh := congrArg E.map hn
  simp only [Functor.map_comp] at hh
  simp only [Category.assoc]
  convert congrArg (fun g => (CechToCohomology.natToIntDoubleComplexVerticalHomologyIso K q).hom ≫ g)
    hh using 1 <;> rfl

lemma secondPageComparison_naturality (f : M ⟶ N)
    (h : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (p q : ℕ) :
    (pageMap.{u,r,a,v} R c I J φ).map 2 (p : ℤ) ((p : ℤ) + (q : ℤ)) ≫
      (secondPageComparison.{u,r,a,v} R c J (spectralData.{u,r,a,v} R c J)
        (verticalIso.{u,r,a,v} R c J) p q).hom =
    (secondPageComparison.{u,r,a,v} R c I (spectralData.{u,r,a,v} R c I)
      (verticalIso.{u,r,a,v} R c I) p q).hom ≫
        (localCechCohomology.{u,r,a,v} R c p q).map f := by
  have hn := congrArg (fun g => HomologicalComplex.homologyMap g (p : ℤ))
    (verticalIso_naturality.{u,r,a,v} R c I J φ f h q)
  simp only [HomologicalComplex.homologyMap_comp] at hn
  have he := HomologicalComplex.extendHomologyIso_hom_naturality
    ((cochainFunctor.{u,r,a,v} R c).map ((localCohomology.{u,r,a} R q).map f))
    (ComplexShape.embeddingUpIntGE 0) (by simp :
      (ComplexShape.embeddingUpIntGE 0).f p = (p : ℤ))
  dsimp only [pageMap, secondPageComparison, Iso.trans_hom, HomologicalComplex.homologyMapIso,
    Functor.mapIso_hom]
  change _ ≫ (columnSecondPageIso (spectralData.{u,r,a,v} R c J) (p : ℤ) (q : ℤ)).hom ≫
      HomologicalComplex.homologyMap (verticalIso.{u,r,a,v} R c J q).hom (p : ℤ) ≫ _ =
    ((columnSecondPageIso (spectralData.{u,r,a,v} R c I) (p : ℤ) (q : ℤ)).hom ≫ _) ≫ _
  rw [columnSecondPageIso_naturality_assoc]
  simp only [Category.assoc]
  congr 1
  rw [← Category.assoc, hn, Category.assoc]
  congr 1

lemma abutmentLimitIso_naturality (n : ℕ) (r p : ℤ)
    (hs : Stabilized (spectralData.{u,r,a,v} R c I).filtration r p (n : ℤ))
    (ht : Stabilized (spectralData.{u,r,a,v} R c J).filtration r p (n : ℤ)) :
    (pageMap.{u,r,a,v} R c I J φ).map r p (n : ℤ) ≫
        (columnAbutmentLimitIso (spectralData.{u,r,a,v} R c J) (n : ℤ)
          (abutmentIso.{u,r,a,v} R c J n) r p ht).hom =
      (columnAbutmentLimitIso (spectralData.{u,r,a,v} R c I) (n : ℤ)
        (abutmentIso.{u,r,a,v} R c I n) r p hs).hom ≫
          abutmentGradedMap (filteredMap.{u,r,a,v} R c I J φ) (n : ℤ)
            (abutmentIso.{u,r,a,v} R c I n) (abutmentIso.{u,r,a,v} R c J n) p :=
  columnAbutmentLimitIso_naturality (spectralData.{u,r,a,v} R c I)
    (spectralData.{u,r,a,v} R c J) (doubleComplexIntMap.{u,r,a,v} R c φ) (n : ℤ)
    (abutmentIso.{u,r,a,v} R c I n) (abutmentIso.{u,r,a,v} R c J n) r p hs ht

end CoefficientNaturality

def coefficientNaturalityData : _root_.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.NaturalityData.{u,r,a,v} R c where
  data := fun J => spectralData.{u,r,a,v} R c J
  firstQuadrant := fun J ↦ columnSpectralData_firstQuadrant _ _
    (fun p q hpq ↦ natToIntDoubleComplex_inQuadrant (doubleComplex.{u,r,a,v} R c J.cocomplex) p q hpq)
  vertical := fun J => verticalIso.{u,r,a,v} R c J
  exactTuple := fun _ => inferInstance
  vertical_component := fun J => verticalIso_component.{u,r,a,v} R c J
  augmentation := fun J => totalAugmentationMap.{u,r,a,v} R c J
  augmentation_quasiIso := fun _ => inferInstance
  augmentation_formula := fun J => totalAugmentationMap_f.{u,r,a,v} R c J
  abutment := fun J => abutmentIso.{u,r,a,v} R c J
  abutment_formula := by
    intro M J n
    simp [abutmentIso]
  finite := fun J n ↦ abutmentPiece_finite (spectralData.{u,r,a,v} R c J).filtration (n : ℤ)
    (abutmentIso.{u,r,a,v} R c J n) (spectralData.{u,r,a,v} R c J).converges.target
  limit := fun J n r p hs => columnAbutmentLimitIso (spectralData.{u,r,a,v} R c J) (n : ℤ)
    (abutmentIso.{u,r,a,v} R c J n) r p hs
  limit_formula := fun J n r p hs => columnAbutmentLimitIso_representative
    (spectralData.{u,r,a,v} R c J) (n : ℤ) (abutmentIso.{u,r,a,v} R c J n) r p hs
  filteredMap := fun I J φ => filteredMap.{u,r,a,v} R c I J φ
  filteredMap_formula := fun I J φ => CechToCohomology.columnFilteredMap_hom _ _ _
  pageMap := fun I J φ => pageMap.{u,r,a,v} R c I J φ
  page_identity := fun I ↦ pageMap_id.{u,r,a,v} R c I
  page_composition := fun I J K ↦ pageMap_comp.{u,r,a,v} R c I J K
  page_lift_independent := fun f I J φ ψ hf hg r p n hr ↦
    pageMap_lift_independent.{u,r,a,v} R c I J f φ ψ hf hg r p n hr
  page_resolution_iso := fun I J ↦ pageMap_isIso.{u,r,a,v} R c I J
  filtration_eq := fun I J ↦ abutmentPiece_resolution_eq.{u,r,a,v} R c I J

/-- Natural maps on the original Čech spectral sequence and its abutment
use the same normalized identifications for every lift. -/
theorem coefficient_naturality :
    _root_.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.coefficientNaturality.{u,r,a,v} := by
  intro X R U A c _
  let D := coefficientNaturalityData.{u,r,a,v} R c
  refine ⟨D, fun I J φ => totalAugmentationMap_naturality.{u,r,a,v} R c I J φ,
    fun I J φ => abutmentLimitIso_naturality.{u,r,a,v} R c I J φ, ?_⟩
  intro M N I J φ f h
  exact ⟨verticalAugmentation_naturality.{u,r,a,v} R c I J φ f h,
    verticalIso_naturality.{u,r,a,v} R c I J φ f h,
    secondPageComparison_naturality.{u,r,a,v} R c I J φ f h,
    abutmentIso_naturality.{u,r,a,v} R c I J φ f h,
    abutmentPieceMap_naturality.{u,r,a,v} R c I J φ f h⟩

theorem total_lift_independence :
    _root_.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.totalLiftIndependence.{u,r,a,v} := by
  intro X R U A c M N I J φ ψ f hφ hψ n
  exact totalHomologyMap_lift_independent.{u,r,a,v} R c I J φ f ψ hφ hψ n


section RestrictionCompatibility

open CechToCohomology (mapExtendIso mapExtendXIso mapExtendIso_hom_f
  mapHomologyIso_comp_hom homologyπ_mapHomologyIso_assoc)
open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients
  (restrictSections restrictSectionScalars)
open _root_.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
  (IsRestrictionModelComparison)
open private sectionExtendComponent from MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients

private lemma extendHomology_mapComparison {B C : Type*} [Category* B] [Category* C]
    [Abelian B] [Abelian C] (F : B ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (K : CochainComplex B ℕ) (n : ℕ) :
    let e := ComplexShape.embeddingUpNat
    let L := (F.mapHomologicalComplex (.up ℕ)).obj K
    HomologicalComplex.homologyMap (mapExtendIso F K e).hom (n : ℤ) ≫
      (L.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom ≫
        ((K.sc n).mapHomologyIso F).hom =
    (((K.extend e).sc (n : ℤ)).mapHomologyIso F).hom ≫
      F.map (K.extendHomologyIso e (j := n) (j' := (n : ℤ)) rfl).hom := by
  let e := ComplexShape.embeddingUpNat
  let L := (F.mapHomologicalComplex (.up ℕ)).obj K
  let P := (F.mapHomologicalComplex (.up ℤ)).obj (K.extend e)
  let γ := (mapExtendIso F K e).hom
  have he : e.f n = (n : ℤ) := rfl
  dsimp only
  apply (cancel_epi (P.homologyπ (n : ℤ))).1
  simp only [HomologicalComplex.homologyπ_naturality_assoc,
    HomologicalComplex.homologyπ_extendHomologyIso_hom_assoc]
  change HomologicalComplex.cyclesMap γ (n : ℤ) ≫ (L.extendCyclesIso e he).hom ≫
      ((K.sc n).map F).homologyπ ≫ ((K.sc n).mapHomologyIso F).hom =
    (((K.extend e).sc (n : ℤ)).map F).homologyπ ≫
      (((K.extend e).sc (n : ℤ)).mapHomologyIso F).hom ≫
      F.map (K.extendHomologyIso e he).hom
  simp only [CechToCohomology.homologyπ_mapHomologyIso, homologyπ_mapHomologyIso_assoc]
  change _ = (((K.extend e).sc (n : ℤ)).mapCyclesIso F).hom ≫
    F.map ((K.extend e).homologyπ (n : ℤ)) ≫ F.map (K.extendHomologyIso e he).hom
  rw [← Functor.map_comp, HomologicalComplex.homologyπ_extendHomologyIso_hom, Functor.map_comp]
  have hcycles :
      HomologicalComplex.cyclesMap γ (n : ℤ) ≫ (L.extendCyclesIso e he).hom ≫
        ((K.sc n).mapCyclesIso F).hom =
      (((K.extend e).sc (n : ℤ)).mapCyclesIso F).hom ≫ F.map (K.extendCyclesIso e he).hom := by
    apply (cancel_mono (F.map (K.iCycles n))).1
    simp only [Category.assoc]
    change HomologicalComplex.cyclesMap γ (n : ℤ) ≫ (L.extendCyclesIso e he).hom ≫
      ((K.sc n).mapCyclesIso F).hom ≫ F.map (K.sc n).iCycles =
        (((K.extend e).sc (n : ℤ)).mapCyclesIso F).hom ≫
          F.map (K.extendCyclesIso e he).hom ≫ F.map (K.iCycles n)
    rw [← Functor.map_comp, HomologicalComplex.extendCyclesIso_hom_iCycles, Functor.map_comp]
    change _ = (((K.extend e).sc (n : ℤ)).mapCyclesIso F).hom ≫
      F.map (((K.extend e).sc (n : ℤ)).iCycles) ≫ F.map (K.extendXIso e he).hom
    simp only [ShortComplex.mapCyclesIso_hom_iCycles, ShortComplex.mapCyclesIso_hom_iCycles_assoc]
    change HomologicalComplex.cyclesMap γ (n : ℤ) ≫ (L.extendCyclesIso e he).hom ≫ L.iCycles n =
      P.iCycles (n : ℤ) ≫ F.map (K.extendXIso e he).hom
    rw [HomologicalComplex.extendCyclesIso_hom_iCycles, HomologicalComplex.cyclesMap_i_assoc,
      mapExtendIso_hom_f]
  have hh := congrArg (fun g ↦ g ≫ F.map (K.homologyπ n)) hcycles
  simp only [Category.assoc] at hh
  exact hh

private lemma restrictionOnModel_eq {W V : Opens X} (j : op W ⟶ op V)
    (K : CochainComplex (AmbientSheaves.{a} R) ℕ) (n : ℕ) :
    let H := ModuleCat.restrictScalars.{max a u r} (R.obj.map j).hom
    let τ := restrictSections.{a} X R j.unop
    restrictionOnModel.{u,r,a} R j (underlyingComplex.{u,r,a} R K) n =
      HomologicalComplex.homologyMap ((τ.mapHomologicalComplex (.up ℕ)).app K) n ≫
        (((sectionComplex.{u,r,a} R V K).sc n).mapHomologyIso H).hom := by
  let H := ModuleCat.restrictScalars.{max a u r} (R.obj.map j).hom
  let E := PresheafOfModules.evaluation R.obj (op V)
  let S := (underlyingComplex.{u,r,a} R K).sc n
  dsimp only [restrictionOnModel]
  rw [mapHomologyIso_comp_hom S E H]
  simp only [Category.assoc]
  change _ ≫ ((S.map E).mapHomologyIso H).hom ≫ H.map (S.mapHomologyIso E).hom ≫
    H.map (S.mapHomologyIso E).inv = _
  rw [← H.map_comp, Iso.hom_inv_id, H.map_id, Category.comp_id]
  rfl

private lemma sectionExtend_restriction {W V : Opens X} (j : op W ⟶ op V)
    (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    let H := ModuleCat.restrictScalars.{max a u r} (R.obj.map j).hom
    let τ := restrictSections.{a} X R j.unop
    let e := ComplexShape.embeddingUpNat
    (τ.mapHomologicalComplex (.up ℤ)).app (K.extend e) ≫
      (H.mapHomologicalComplex (.up ℤ)).map (sectionExtendIso.{u,r,a} R V K).hom ≫
      (mapExtendIso H (sectionComplex.{u,r,a} R V K) e).hom =
    (sectionExtendIso.{u,r,a} R W K).hom ≫
      HomologicalComplex.extendMap ((τ.mapHomologicalComplex (.up ℕ)).app K) e := by
  let H := ModuleCat.restrictScalars.{max a u r} (R.obj.map j).hom
  let τ := restrictSections.{a} X R j.unop
  let e := ComplexShape.embeddingUpNat
  let L := sectionComplex.{u,r,a} R V K
  dsimp only
  apply HomologicalComplex.hom_ext
  intro i
  change τ.app (HomologicalComplex.extend.X K (e.r i)) ≫
      H.map (sectionExtendComponent.{u,r,a} R V K (e.r i)).hom ≫
      (mapExtendXIso H L (e.r i)).hom =
    (sectionExtendComponent.{u,r,a} R W K (e.r i)).hom ≫
      HomologicalComplex.extend.mapX ((τ.mapHomologicalComplex (.up ℕ)).app K) (e.r i)
  cases e.r i with
  | none => exact (isZero_zero _).eq_of_tgt _ _
  | some k =>
    simp only [sectionExtendComponent, mapExtendXIso, Iso.refl_hom, Category.id_comp]
    rfl

attribute [local instance] HasDerivedCategory.standard

private lemma sectionModelMap_restriction {W V : Opens X} (j : op W ⟶ op V)
    (t : ∀ n : ℕ, cohomologyValue.{a,u,r} R W n ⟶
      cohomologyValue.{a,u,r} R V n ⋙ restrictSectionScalars.{a} X R j.unop)
    (h : IsRestrictionModelComparison.{u,r,a} R j t)
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℕ) :
    let H := restrictSectionScalars.{a} X R j.unop
    sectionModelMap.{u,r,a} R W J n ≫ (t n).app M =
      restrictionOnModel.{u,r,a} R j (underlyingComplex.{u,r,a} R J.cocomplex) n ≫
        H.map (sectionModelMap.{u,r,a} R V J n) := by
  let H := restrictSectionScalars.{a} X R j.unop
  let τ := restrictSections.{a} X R j.unop
  let e := ComplexShape.embeddingUpNat
  let KW := sectionComplex.{u,r,a} R W J.cocomplex
  let KV := sectionComplex.{u,r,a} R V J.cocomplex
  let LV := ((sectionsValue.{a,u,r} R V).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
  let Q := HomologicalComplex.homologyFunctor (ModuleCat.{max a u r} (sectionRing R W)) (.up ℤ) (n : ℤ)
  have he : e.f n = (n : ℤ) := rfl
  let aW := HomologicalComplex.homologyMapIso (sectionExtendIso.{u,r,a} R W J.cocomplex)
      (n : ℤ) ≪≫ KW.extendHomologyIso e he
  let aV := HomologicalComplex.homologyMapIso (sectionExtendIso.{u,r,a} R V J.cocomplex)
      (n : ℤ) ≪≫ KV.extendHomologyIso e he
  have hm := h M J.cochainComplex J.ι' (by infer_instance) (fun _ ↦ inferInstance) n
  have hn := congrArg Q.map (sectionExtend_restriction.{u,r,a} R j J.cocomplex)
  simp only [Functor.map_comp] at hn
  have hc := HomologicalComplex.extendHomologyIso_hom_naturality
    ((τ.mapHomologicalComplex (.up ℕ)).app J.cocomplex) e he
  have hf := extendHomology_mapComparison H KV n
  have hg := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (.up ℤ) (n : ℤ)).map
      (sectionExtendIso.{u,r,a} R V J.cocomplex).hom) H
  change
    Q.map ((H.mapHomologicalComplex (.up ℤ)).map (sectionExtendIso.{u,r,a} R V J.cocomplex).hom) ≫
      (((KV.extend e).sc (n : ℤ)).mapHomologyIso H).hom =
    ((LV.sc (n : ℤ)).mapHomologyIso H).hom ≫
      H.map (HomologicalComplex.homologyMap (sectionExtendIso.{u,r,a} R V J.cocomplex).hom (n : ℤ)) at hg
  let ρ := restrictionOnModel.{u,r,a} R j (underlyingComplex.{u,r,a} R J.cocomplex) n
  let τ' := HomologicalComplex.homologyMap ((τ.mapHomologicalComplex (.up ℤ)).app J.cochainComplex) (n : ℤ)
  let β := (LV.sc (n : ℤ)).mapHomologyIso H
  have hchain : τ' ≫ β.hom ≫ H.map aV.hom = aW.hom ≫ ρ := by
    dsimp only [aW, aV, Iso.trans_hom, HomologicalComplex.homologyMapIso, Functor.mapIso_hom]
    rw [Functor.map_comp]
    change τ' ≫ β.hom ≫ H.map (HomologicalComplex.homologyMap
      (sectionExtendIso.{u,r,a} R V J.cocomplex).hom (n : ℤ)) ≫ H.map (KV.extendHomologyIso e he).hom =
      HomologicalComplex.homologyMap (sectionExtendIso.{u,r,a} R W J.cocomplex).hom (n : ℤ) ≫
        (KW.extendHomologyIso e he).hom ≫ ρ
    rw [← Category.assoc _ (H.map (HomologicalComplex.homologyMap
      (sectionExtendIso.{u,r,a} R V J.cocomplex).hom (n : ℤ))), ← hg, Category.assoc]
    erw [← hf]
    simp only [← Category.assoc]
    erw [hn]
    have hh := congrArg (fun m ↦ Q.map (sectionExtendIso.{u,r,a} R W J.cocomplex).hom ≫
      m ≫ ((KV.sc n).mapHomologyIso H).hom) hc
    simp only [Category.assoc] at hh ⊢
    dsimp only [ρ]
    rw [restrictionOnModel_eq.{u,r,a} R j]
    exact hh
  have hchain' : τ' ≫ β.hom = aW.hom ≫ ρ ≫ H.map aV.inv := by
    have hh := congrArg (fun m ↦ m ≫ H.map aV.inv) hchain
    simp only [Category.assoc] at hh
    rw [← H.map_comp, Iso.hom_inv_id, H.map_id, Category.comp_id] at hh
    exact hh
  let mW := resolutionModelMap (sectionsValue.{a,u,r} R W) J.ι' (by infer_instance) n
  let mV := resolutionModelMap (sectionsValue.{a,u,r} R V) J.ι' (by infer_instance) n
  change mW ≫ (t n).app M = τ' ≫ β.hom ≫ H.map mV at hm
  change (aW.inv ≫ mW) ≫ (t n).app M = ρ ≫ H.map (aV.inv ≫ mV)
  rw [Category.assoc, hm, ← Category.assoc τ' β.hom, hchain']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]


theorem original_restriction_compatibility :
    _root_.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.originalRestrictionCompatibility.{u,r,a} := by
  intro X R _
  refine ⟨originalLocalSectionsIso.{u,r,a} R,
    fun V n _ J ↦ originalLocalSectionsIso_model.{u,r,a} R V n J, ?_⟩
  intro W V j
  have hR : _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients.restrictionMapType.{a,u,r} :=
    SheafCohomologyOriginalCoefficients.restrictionMap
  obtain ⟨t, _, _, ht⟩ := hR X R j.unop
  refine ⟨t, ht, ?_⟩
  intro M n
  let J := injectiveResolution M
  let H := restrictSectionScalars.{a} X R j.unop
  change ((localCohomology.{u,r,a} R n).obj M).map j ≫
      H.map ((originalLocalSectionsIso.{u,r,a} R V n).hom.app M) =
    (originalLocalSectionsIso.{u,r,a} R W n).hom.app M ≫ (t n).app M
  rw [originalLocalSectionsIso_model.{u,r,a} R V n J,
    originalLocalSectionsIso_model.{u,r,a} R W n J, Functor.map_comp, ← Category.assoc]
  have hn := localEvaluationIso_restriction.{u,r,a} R j J n
  dsimp only at hn
  erw [hn]
  simp only [Category.assoc]
  erw [sectionModelMap_restriction.{u,r,a} R j t ht J n]

end RestrictionCompatibility


section VerticalTotalAugmentation

omit [EnoughInjectives (AmbientSheaves.{a} R)]

open CechToCohomology (natToIntDoubleComplexRowIso natToIntDoubleComplexRowIso_hom_f)
open AugmentedDoubleComplexComparison (axisInclusion columnLift)

private abbrev axisEmbedding := ComplexShape.embeddingUpIntGE 0

private def extendZeroRowAugmentation {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) {L : CochainComplex B ℕ}
    (g : L ⟶ K.flip.X 0) :
    L.extend axisEmbedding ⟶ (CechToCohomology.natToIntDoubleComplex K).flip.X 0 :=
  HomologicalComplex.extendMap g axisEmbedding ≫ (natToIntDoubleComplexRowIso K 0).inv

private lemma extendZeroRowAugmentation_f {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) {L : CochainComplex B ℕ}
    (g : L ⟶ K.flip.X 0) (p : ℕ) :
    (extendZeroRowAugmentation K g).f (p : ℤ) =
      (L.extendXIso axisEmbedding (by simp [axisEmbedding] : axisEmbedding.f p = (p : ℤ))).hom ≫
        g.f p ≫ (intBicomplexTermIso K p 0).inv := by
  apply (cancel_mono (intBicomplexTermIso K p 0).hom).1
  have hp : axisEmbedding.f p = (p : ℤ) := by simp [axisEmbedding]
  have h := natToIntDoubleComplexRowIso_hom_f K p 0
  change (natToIntDoubleComplexRowIso K 0).hom.f (p : ℤ) ≫
    ((K.flip.X 0).extendXIso axisEmbedding hp).hom = (intBicomplexTermIso K p 0).hom at h
  have hc : extendZeroRowAugmentation K g ≫ (natToIntDoubleComplexRowIso K 0).hom =
      HomologicalComplex.extendMap g axisEmbedding := by
    simp only [extendZeroRowAugmentation, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hc' := HomologicalComplex.congr_hom hc (p : ℤ)
  simp only [HomologicalComplex.comp_f] at hc'
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h, ← Category.assoc]
  erw [hc', HomologicalComplex.extendMap_f _ _ hp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma extendZeroRowAugmentation_closed {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) {L : CochainComplex B ℕ}
    (g : L ⟶ K.flip.X 0) (hg : ∀ p, g.f p ≫ (K.X p).d 0 1 = 0)
    (p q : ℤ) (h : (ComplexShape.up ℤ).Rel 0 q) :
    (extendZeroRowAugmentation K g).f p ≫ ((CechToCohomology.natToIntDoubleComplex K).X p).d 0 q = 0 := by
  have hq : q = 1 := by change 0 + 1 = q at h; omega
  clear h
  subst q
  by_cases hp : 0 ≤ p
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    let E := (axisEmbedding.extendFunctor B).mapHomologicalComplex (.up ℕ)
    have hp : axisEmbedding.f p = (p : ℤ) := by simp [axisEmbedding]
    have h0 : axisEmbedding.f (0 : ℕ) = (0 : ℤ) := by simp [axisEmbedding]
    have h1 : axisEmbedding.f (1 : ℕ) = (1 : ℤ) := by simp [axisEmbedding]
    let β := (E.obj K).extendXIso axisEmbedding hp
    change (extendZeroRowAugmentation K g).f (p : ℤ) ≫
      (((E.obj K).extend axisEmbedding).X (p : ℤ)).d 0 1 = 0
    apply (cancel_mono (β.hom.f (1 : ℤ))).1
    rw [Category.assoc, ← β.hom.comm 0 1, zero_comp, extendZeroRowAugmentation_f]
    simp only [intBicomplexTermIso, Iso.trans_inv, Functor.mapIso_inv, Category.assoc]
    change _ ≫ g.f p ≫ ((K.X p).extendXIso axisEmbedding h0).inv ≫
      β.inv.f (0 : ℤ) ≫ β.hom.f (0 : ℤ) ≫ ((K.X p).extend axisEmbedding).d 0 1 = 0
    have hb := HomologicalComplex.congr_hom β.inv_hom_id (0 : ℤ)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hb
    rw [HomologicalComplex.extend_d_eq _ _ h0 h1,
      ← Category.assoc (β.inv.f (0 : ℤ)), hb, Category.id_comp]
    simp only [Iso.inv_hom_id_assoc]
    rw [← Category.assoc (g.f p), hg p, zero_comp, comp_zero]
  · exact (L.isZero_extend_X axisEmbedding p (by
      intro i hi
      simp [axisEmbedding] at hi
      omega)).eq_of_src _ _

/-- Assemble the vertical augmentation on the axis where the horizontal
summands in the signed total have coefficient one. -/
private def zeroRowTotalMap {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) {L : CochainComplex B ℕ}
    (g : L ⟶ K.flip.X 0) (hg : ∀ p, g.f p ≫ (K.X p).d 0 1 = 0)
    [(CechToCohomology.natToIntDoubleComplex K).HasTotal (.up ℤ)] :
    L.extend axisEmbedding ⟶ sumTotal (CechToCohomology.natToIntDoubleComplex K) :=
  axisInclusion _ ≫ HomologicalComplex₂.total.map
    (columnLift _ _ (extendZeroRowAugmentation K g) (extendZeroRowAugmentation_closed K g hg)) (.up ℤ)

private lemma zeroRowTotalMap_f {B : Type*} [Category* B] [Abelian B]
    (K : HomologicalComplex₂ B (.up ℕ) (.up ℕ)) {L : CochainComplex B ℕ}
    (g : L ⟶ K.flip.X 0) (hg : ∀ p, g.f p ≫ (K.X p).d 0 1 = 0)
    [(CechToCohomology.natToIntDoubleComplex K).HasTotal (.up ℤ)] (p : ℤ) :
    (zeroRowTotalMap K g hg).f p = (extendZeroRowAugmentation K g).f p ≫
      sumInjection (CechToCohomology.natToIntDoubleComplex K) p 0 p (add_zero p) := by
  simp only [zeroRowTotalMap, HomologicalComplex.comp_f, axisInclusion]
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map]
  change (HomologicalComplex.singleObjXSelf _ _ _).inv ≫
    (HomologicalComplex.mkHomFromSingle
      (K := (CechToCohomology.natToIntDoubleComplex K).X p)
      ((extendZeroRowAugmentation K g).f p) (extendZeroRowAugmentation_closed K g hg p)).f 0 ≫ _ = _
  rw [HomologicalComplex.mkHomFromSingle_f]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

private lemma verticalAugmentation_closed {M : AmbientSheaves.{a} R}
    (J : InjectiveResolution M) (p : ℕ) :
    (verticalAugmentation.{u,r,a,v} R c J).f p ≫
      ((doubleComplex.{u,r,a,v} R c J.cocomplex).X p).d 0 1 = 0 := by
  let F := SheafOfModules.forget R ⋙ cochainFunctor.{u,r,a,v} R c ⋙
    HomologicalComplex.eval (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) p
  change F.map (J.ι.f 0) ≫ F.map (J.cocomplex.d 0 1) = 0
  rw [← F.map_comp]
  have h : J.ι.f 0 ≫ J.cocomplex.d 0 1 = 0 := by
    simpa only [HomologicalComplex.single_obj_d, zero_comp] using J.ι.comm 0 1
  rw [h, F.map_zero]

/-- The map from original full cochains to the signed total of any injective model. -/
def verticalTotalAugmentationMap {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    (cochainComplex.{u,r,a,v} R c M.val).extend axisEmbedding ⟶
      sumTotal (doubleComplexInt.{u,r,a,v} R c J.cocomplex) :=
  zeroRowTotalMap (doubleComplex.{u,r,a,v} R c J.cocomplex)
    (verticalAugmentation.{u,r,a,v} R c J) (verticalAugmentation_closed.{u,r,a,v} R c J)

theorem vertical_total_augmentation :
    _root_.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.verticalTotalAugmentation.{u,r,a,v} := by
  intro X R U A c M J
  refine ⟨verticalTotalAugmentationMap.{u,r,a,v} R c J, fun p ↦ ?_⟩
  dsimp only [verticalTotalAugmentationMap]
  rw [zeroRowTotalMap_f, extendZeroRowAugmentation_f]
  simp only [Category.assoc]

end VerticalTotalAugmentation


section VerticalTotalTransport

omit [EnoughInjectives (AmbientSheaves.{a} R)]

open CechToCohomology (mapExtendIso mapExtendIso_hom_f natToIntDoubleComplex)

private abbrev raisedCoefficientCochains (M : AmbientSheaves.{a} R) :=
  CechToCohomology.cechComplex (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
    ((transport.{a} R).obj M).val

/-- The coefficient-complex comparison also commutes with zero extension. -/
def intCochainIso (M : AmbientSheaves.{a} R) :
    (cochainComplex.{u,r,a,v} R c M.val).extend axisEmbedding ≅
      ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℤ)).obj
        ((raisedCoefficientCochains.{u,r,a,v} R c M).extend axisEmbedding) :=
  (axisEmbedding.extendFunctor _).mapIso (cochainIso.{u,r,a,v} R c M) ≪≫
    (mapExtendIso (originalScalars.{u,r,a,v} R c) (raisedCoefficientCochains.{u,r,a,v} R c M) axisEmbedding).symm

private lemma intCochainIso_coordinate (M : AmbientSheaves.{a} R) (p : ℕ) :
    let hp : axisEmbedding.f p = (p : ℤ) := by simp [axisEmbedding]
    (intCochainIso.{u,r,a,v} R c M).hom.f (p : ℤ) ≫
      (originalScalars.{u,r,a,v} R c).map
        ((raisedCoefficientCochains.{u,r,a,v} R c M).extendXIso axisEmbedding hp).hom =
      ((cochainComplex.{u,r,a,v} R c M.val).extendXIso axisEmbedding hp).hom ≫
        (cochainIso.{u,r,a,v} R c M).hom.f p := by
  let hp : axisEmbedding.f p = (p : ℤ) := by simp [axisEmbedding]
  let S := originalScalars.{u,r,a,v} R c
  let Q := raisedCoefficientCochains.{u,r,a,v} R c M
  let e := mapExtendIso S Q axisEmbedding
  have he : e.inv.f (p : ℤ) ≫ S.map (Q.extendXIso axisEmbedding hp).hom =
      (((S.mapHomologicalComplex (.up ℕ)).obj Q).extendXIso axisEmbedding hp).hom := by
    rw [← mapExtendIso_hom_f S Q axisEmbedding hp]
    have hi := HomologicalComplex.congr_hom e.inv_hom_id (p : ℤ)
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hi
    rw [← Category.assoc, hi, Category.id_comp]
  simp only [intCochainIso, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.comp_f, Category.assoc]
  change (HomologicalComplex.extendMap (cochainIso.{u,r,a,v} R c M).hom axisEmbedding).f (p : ℤ) ≫
      e.inv.f (p : ℤ) ≫ S.map (Q.extendXIso axisEmbedding hp).hom = _
  rw [he, HomologicalComplex.extendMap_f _ _ hp]
  simp only [Category.assoc]
  have hx := ((((S.mapHomologicalComplex (.up ℕ)).obj Q).extendXIso axisEmbedding hp)).inv_hom_id
  change _ ≫ _ ≫ ((((S.mapHomologicalComplex (.up ℕ)).obj Q).extendXIso axisEmbedding hp)).inv ≫
    (((S.mapHomologicalComplex (.up ℕ)).obj Q).extendXIso axisEmbedding hp).hom = _
  rw [hx, Category.comp_id]

private lemma raisedVerticalAugmentation_closed {M : AmbientSheaves.{a} R}
    (J : InjectiveResolution M) (p : ℕ) :
    (raisedVerticalAugmentation.{u,r,a,v} R c J).f p ≫
      ((raisedDouble.{u,r,a,v} R c J.cocomplex).X p).d 0 1 = 0 := by
  let F := transport.{a} R ⋙ SheafOfModules.forget (liftedRing.{a} R) ⋙
    CechToCohomology.cochainFunctor (liftedRing.{a} R) (liftCover.{u,a,r,v} c) ⋙
    HomologicalComplex.eval _ (.up ℕ) p
  change F.map (J.ι.f 0) ≫ F.map (J.cocomplex.d 0 1) = 0
  rw [← F.map_comp]
  have h : J.ι.f 0 ≫ J.cocomplex.d 0 1 = 0 := by
    simpa only [HomologicalComplex.single_obj_d, zero_comp] using J.ι.comm 0 1
  rw [h, F.map_zero]

/-- The corresponding zero-row map of the actual lifted resolution. -/
def raisedVerticalTotalAugmentationMap {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    (raisedCoefficientCochains.{u,r,a,v} R c M).extend axisEmbedding ⟶
      sumTotal (natToIntDoubleComplex (raisedDouble.{u,r,a,v} R c J.cocomplex)) :=
  zeroRowTotalMap (raisedDouble.{u,r,a,v} R c J.cocomplex)
    (raisedVerticalAugmentation.{u,r,a,v} R c J) (raisedVerticalAugmentation_closed.{u,r,a,v} R c J)

lemma verticalTotalAugmentationMap_transport {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    verticalTotalAugmentationMap.{u,r,a,v} R c J ≫ (signedTotalIso.{u,r,a,v} R c J.cocomplex).hom =
      (intCochainIso.{u,r,a,v} R c M).hom ≫
        ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℤ)).map
          (raisedVerticalTotalAugmentationMap.{u,r,a,v} R c J) := by
  letI := ambient_enough_injectives.{a,u,r} X R
  let K := doubleComplex.{u,r,a,v} R c J.cocomplex
  let L := raisedDouble.{u,r,a,v} R c J.cocomplex
  let P := cochainComplex.{u,r,a,v} R c M.val
  let Q := raisedCoefficientCochains.{u,r,a,v} R c M
  let S := originalScalars.{u,r,a,v} R c
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : 0 ≤ n
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    let hp : axisEmbedding.f p = (p : ℤ) := by simp [axisEmbedding]
    let eK := intBicomplexTermIso K p 0
    let eL := intBicomplexTermIso L p 0
    let f := (verticalAugmentation.{u,r,a,v} R c J).f p
    let g := (raisedVerticalAugmentation.{u,r,a,v} R c J).f p
    let eNat := (cochainIso.{u,r,a,v} R c M).hom.f p
    let eInt := (intCochainIso.{u,r,a,v} R c M).hom.f (p : ℤ)
    let dNat := ((doubleIso.{u,r,a,v} R c J.cocomplex).hom.f p).f 0
    let dInt := ((doubleIntIso.{u,r,a,v} R c J.cocomplex).hom.f (p : ℤ)).f 0
    let ιL := sumInjection (natToIntDoubleComplex L) (p : ℤ) 0 (p : ℤ) (add_zero _)
    have hd : dInt ≫ S.map eL.hom = eK.hom ≫ dNat :=
      comparedBicomplexTerm S (doubleIso.{u,r,a,v} R c J.cocomplex) p 0
    have he : eK.inv ≫ dInt = dNat ≫ S.map eL.inv := by
      apply (cancel_mono (S.map eL.hom)).1
      simp only [Category.assoc, hd, Iso.inv_hom_id_assoc, ← S.map_comp, Iso.inv_hom_id, S.map_id]
      exact (Category.comp_id dNat).symm
    have haf : f ≫ dNat = eNat ≫ S.map g := by
      have h := HomologicalComplex.congr_hom
        (cochainIso_naturality.{u,r,a,v} R c (J.ι.f 0)) p
      exact h
    have hb : eInt ≫ S.map (Q.extendXIso axisEmbedding hp).hom =
        (P.extendXIso axisEmbedding hp).hom ≫ eNat :=
      intCochainIso_coordinate.{u,r,a,v} R c M p
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      verticalTotalAugmentationMap, raisedVerticalTotalAugmentationMap,
      zeroRowTotalMap_f, extendZeroRowAugmentation_f, Category.assoc]
    change (P.extendXIso axisEmbedding hp).hom ≫ f ≫ eK.inv ≫
        sumInjection (doubleComplexInt.{u,r,a,v} R c J.cocomplex) (p : ℤ) 0 (p : ℤ) (add_zero _) ≫
          (signedTotalIso.{u,r,a,v} R c J.cocomplex).hom.f (p : ℤ) =
      eInt ≫ S.map ((Q.extendXIso axisEmbedding hp).hom ≫ g ≫ eL.inv ≫ ιL)
    rw [signedTotalIso_injection.{u,r,a,v} R c J.cocomplex]
    change (P.extendXIso axisEmbedding hp).hom ≫ f ≫ eK.inv ≫ dInt ≫ S.map ιL =
      eInt ≫ S.map ((Q.extendXIso axisEmbedding hp).hom ≫ g ≫ eL.inv ≫ ιL)
    rw [← Category.assoc eK.inv dInt, he]
    simp only [Category.assoc, Functor.map_comp]
    rw [← Category.assoc f dNat, haf, Category.assoc,
      ← Category.assoc (P.extendXIso axisEmbedding hp).hom, ← hb]
    simp only [Category.assoc]
  · exact (P.isZero_extend_X axisEmbedding n (by
      intro i hi
      simp [axisEmbedding] at hi
      omega)).eq_of_src _ _

theorem vertical_signed_total_transport :
    _root_.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.verticalSignedTotalTransport.{u,r,a,v} := by
  intro X R U A c M J
  letI := ambient_enough_injectives.{a,u,r} X R
  refine ⟨doubleIntIso.{u,r,a,v} R c J.cocomplex, signedTotalIso.{u,r,a,v} R c J.cocomplex,
    intCochainIso.{u,r,a,v} R c M, verticalTotalAugmentationMap.{u,r,a,v} R c J,
    raisedVerticalTotalAugmentationMap.{u,r,a,v} R c J,
    signedTotalIso_injection.{u,r,a,v} R c J.cocomplex, ?_, ?_, ?_, ?_,
    verticalTotalAugmentationMap_transport.{u,r,a,v} R c J⟩
  · intro p q x
    exact heq_of_eq (doubleIntIso_apply.{u,r,a,v} R c J.cocomplex p q x)
  · intro p x
    apply heq_of_eq
    rw [Category.assoc, intCochainIso_coordinate, Iso.inv_hom_id_assoc]
    rfl
  · intro p
    simp only [verticalTotalAugmentationMap, zeroRowTotalMap_f, extendZeroRowAugmentation_f, Category.assoc]
  · intro p
    simp only [raisedVerticalTotalAugmentationMap, zeroRowTotalMap_f, extendZeroRowAugmentation_f, Category.assoc]

end VerticalTotalTransport

section SectionCarrier

open CategoryTheory.Functor

open _root_.Specs.AdvancedHomologicalAlgebra.SheafCohomologyOriginalCoefficients (cohomologyValue)
open CechToCohomology (mapHomologyIso_comp_hom localH01SectionsIso
  localH01SectionsIso_computation sectionCohomologyResolutionIso_eq sectionResolutionIsoNat)

private abbrev transportedSectionScalars (W : Opens (liftedSpace.{max a u r} X))
    (V : Opens X) (h : opensEquiv.{max a u r} X W = V) :=
  ModuleCat.restrictScalars.{max a u r} (ringAt.{u,r,a} R W V h).toRingHom

/-- Original evaluation and transport followed by lifted evaluation use the
same section and the prescribed section-ring isomorphism. -/
def presheafEvaluationIso (W : Opens (liftedSpace.{max a u r} X)) (V : Opens X)
    (h : opensEquiv.{max a u r} X W = V) :
    PresheafOfModules.evaluation R.obj (op V) ≅
      transportPresheaf.{a} R ⋙ PresheafOfModules.evaluation (liftedRing.{a} R).obj (op W) ⋙
        transportedSectionScalars.{u,r,a} R W V h :=
  NatIso.ofComponents (fun F ↦
    ({ toAddEquiv := presheafSectionAt.{u,r,a} R F W V h
       map_smul' := fun b s ↦ by subst V; rfl } :
      F.obj (op V) ≃ₗ[sectionRing R V]
        (transportedSectionScalars.{u,r,a} R W V h).obj
          (((transportPresheaf.{a} R).obj F).obj (op W))).toModuleIso)
    (by
      intro F G f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      exact presheafSectionAt_map.{u,r,a} R f h s)

private instance (W : Opens (liftedSpace.{max a u r} X)) (V : Opens X)
    (h : opensEquiv.{max a u r} X W = V) :
    (transportedSectionScalars.{u,r,a} R W V h).IsEquivalence :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    (ringAt.{u,r,a} R W V h)).isEquivalence_functor

/-- The comparison between the two actual derived section functors. -/
def sectionCarrierComparison (W : Opens (liftedSpace.{max a u r} X)) (V : Opens X)
    (h : opensEquiv.{max a u r} X W = V) (q : ℕ) :
    cohomologyValue.{a,u,r} R V q ≅ transport.{a} R ⋙
      sectionCohomology (liftedRing.{a} R) W q ⋙ transportedSectionScalars.{u,r,a} R W V h :=
  let H := transportedSectionScalars.{u,r,a} R W V h
  let E := PresheafOfModules.evaluation (liftedRing.{a} R).obj (op W)
  (originalLocalSectionsIso.{u,r,a} R V q).symm ≪≫
    isoWhiskerLeft _ (presheafEvaluationIso.{u,r,a} R W V h) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (localPresheafComparison.{u,r,a} R q) (E ⋙ H) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (localH01SectionsIso (liftedRing.{a} R) W q) H)

set_option maxHeartbeats 2200000 in
/-- The section comparison preserves the derived unit and the given
resolution augmentation. -/
lemma sectionCarrierComparison_model (W : Opens (liftedSpace.{max a u r} X))
    (V : Opens X) (h : opensEquiv.{max a u r} X W = V)
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) (n : ℕ) :
    let H := transportedSectionScalars.{u,r,a} R W V h
    let R' := liftedRing.{a} R
    let M' := (transport.{a} R).obj M
    let J' := raisedResolution.{u,r,a} R J
    let K' := CechToCohomology.sectionComplex R' (U := W) M' J'
    let η := (NatIso.mapHomologicalComplex (presheafEvaluationIso.{u,r,a} R W V h)
      (.up ℕ)).app (underlyingComplex.{u,r,a} R J.cocomplex)
    sectionModelMap.{u,r,a} R V J n ≫ (sectionCarrierComparison.{u,r,a} R W V h n).hom.app M =
      HomologicalComplex.homologyMap η.hom n ≫ ((K'.sc n).mapHomologyIso H).hom ≫
        H.map (CechToCohomology.sectionCohomologyResolutionIso R' W M' J' n).inv := by
  let H := transportedSectionScalars.{u,r,a} R W V h
  let R' := liftedRing.{a} R
  let M' := (transport.{a} R).obj M
  let J' := raisedResolution.{u,r,a} R J
  let P := transportPresheaf.{a} R
  let E := PresheafOfModules.evaluation R.obj (op V)
  let G := PresheafOfModules.evaluation R'.obj (op W)
  let C := (underlyingComplex.{u,r,a} R J.cocomplex).sc n
  let i := J.isoRightDerivedObj (SheafOfModules.forget R) n
  let j := J'.isoRightDerivedObj (SheafOfModules.forget R') n
  let η := presheafEvaluationIso.{u,r,a} R W V h
  let l := originalLocalSectionsIso.{u,r,a} R V n
  let l' := localH01SectionsIso R' W n
  let s := CechToCohomology.sectionCohomologyResolutionIso R' W M' J' n
  let e := localPresheafComparison.{u,r,a} R n
  have ha : sectionModelMap.{u,r,a} R V J n ≫ (l.inv.app M) =
      (C.mapHomologyIso E).hom ≫ E.map i.inv := by
    have hl := originalLocalSectionsIso_model.{u,r,a} R V n J
    change l.hom.app M = (E.map i.hom ≫ (C.mapHomologyIso E).inv) ≫
      sectionModelMap.{u,r,a} R V J n at hl
    rw [← cancel_epi (E.map i.hom ≫ (C.mapHomologyIso E).inv)]
    rw [← Category.assoc, ← hl, Iso.hom_inv_id_app]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← E.map_comp, Iso.hom_inv_id, E.map_id]
    rfl
  have hb : l'.hom.app M' = G.map j.hom ≫ ((C.map P).mapHomologyIso G).inv ≫ s.inv := by
    apply (cancel_mono s.hom).1
    have hl := localH01SectionsIso_computation R' W M' J' n
    change l'.hom.app M' ≫ s.hom = G.map j.hom ≫ ((C.map P).mapHomologyIso G).inv at hl
    rw [hl]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : e.hom.app M = P.map i.hom ≫ (C.mapHomologyIso P).inv ≫ j.inv := by
    exact congrArg Iso.hom (localPresheafComparison_model.{u,r,a} R J n)
  have hη : (sectionCarrierComparison.{u,r,a} R W V h n).hom.app M =
      l.inv.app M ≫ η.hom.app _ ≫ (G ⋙ H).map (e.hom.app M) ≫ H.map (l'.hom.app M') := by
    simp only [sectionCarrierComparison, Iso.trans_hom, NatTrans.comp_app,
      Iso.symm_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
      whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.assoc, Category.id_comp]
    rfl
  have hc : ((C.map P).mapHomologyIso G).hom ≫ G.map j.inv ≫ l'.hom.app M' = s.inv := by
    rw [hb, ← Category.assoc (G.map j.inv), ← G.map_comp, Iso.inv_hom_id, G.map_id,
      Category.id_comp, Iso.hom_inv_id_assoc]
  dsimp only
  rw [hη, ← Category.assoc, ha, he]
  have hd := compareExactModel P E G H C η i j
  have hd' := congrArg (fun g ↦ g ≫ H.map (l'.hom.app M')) hd
  simp only [Category.assoc] at hd'
  change (C.mapHomologyIso E).hom ≫ E.map i.inv ≫ η.hom.app _ ≫
    (G ⋙ H).map (P.map i.hom ≫ (C.mapHomologyIso P).inv ≫ j.inv) ≫ H.map (l'.hom.app M') = _
  rw [hd', ← H.map_comp, Category.assoc, hc]
  rfl

end SectionCarrier

open CechToCohomology (resolutionAbutmentIso resolutionAbutmentIso_agrees resolutionTotalAugmentation)

theorem abutment_transport :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.abutmentTransport.{u,r,a,v} := by
  intro X R U A c _
  let W := (opensEquiv.{max a u r} X).symm U
  let h := (opensEquiv.{max a u r} X).apply_symm_apply U
  let R' := liftedRing.{a} R
  let c' := liftCover.{u,a,r,v} c
  refine ⟨fun n ↦ sectionCarrierComparison.{u,r,a} R W U h n, ?_⟩
  intro M J
  let M' := (transport.{a} R).obj M
  let J' := raisedResolution.{u,r,a} R J
  refine ⟨J', rfl, heq_of_eq (raisedResolution_ι_zero.{u,r,a} R J),
    doubleIntIso.{u,r,a,v} R c J.cocomplex, signedTotalIso.{u,r,a,v} R c J.cocomplex,
    totalAugmentationMap.{u,r,a,v} R c J, resolutionTotalAugmentation R' c' M' J',
    fun p q x ↦ heq_of_eq (doubleIntIso_apply.{u,r,a,v} R c J.cocomplex p q x),
    signedTotalIso_injection.{u,r,a,v} R c J.cocomplex, totalAugmentationMap_f.{u,r,a,v} R c J,
    CechToCohomology.resolutionTotalAugmentation_f R' c' M' J', ?_⟩
  intro n
  refine ⟨abutmentIso.{u,r,a,v} R c J n, resolutionAbutmentIso R' c' M' J' n, ?_, ?_, ?_⟩
  · simp [abutmentIso]
  · rw [← CechToCohomology.sectionCohomologyResolutionIso_eq]
    exact resolutionAbutmentIso_agrees R' c' M' J' n
  · have hη : (NatIso.mapHomologicalComplex (presheafEvaluationIso.{u,r,a} R W U h)
          (.up ℕ)).app (underlyingComplex.{u,r,a} R J.cocomplex) =
        sectionScalarIso.{u,r,a} R (U := U) J.cocomplex := by
      apply Iso.ext
      apply HomologicalComplex.hom_ext
      intro q
      apply ModuleCat.hom_ext
      ext x : 1
      rfl
    have hτ := sectionCarrierComparison_model.{u,r,a} R W U h J n
    dsimp only at hτ
    rw [hη] at hτ
    have hA := abutmentIso_transport.{u,r,a,v} R c J n
      ((sectionCarrierComparison.{u,r,a} R W U h n).app M) hτ.symm
    refine ⟨hA, ?_⟩
    intro D E p
    let S := originalScalars.{u,r,a,v} R c
    let t := signedTotalIso.{u,r,a,v} R c J.cocomplex
    let g := abutmentIso.{u,r,a,v} R c J n
    let g' := resolutionAbutmentIso R' c' M' J' n
    have hp := signedTotalIso_filtration.{u,r,a,v} R c J.cocomplex D E
    have ht := limiting_transport S D.filtration E.filtration t hp D.pages E.pages
    obtain ⟨z, f, g₀, hz, hf, hπ, hc, hl⟩ := ht (n : ℤ) g g'
    refine ⟨f p, ?_⟩
    rw [hf p]
    congr 1
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc]
    change g.inv ≫ HomologicalComplex.homologyMap t.hom (n : ℤ) ≫ _ ≫ S.map g'.hom = _
    rw [hA, Iso.inv_hom_id_assoc]
    rfl

section VerticalCarrier

open CechToCohomology (cechTerm resolutionDoubleComplex resolutionDoubleComplexInt
  resolutionColumnIso resolutionVerticalComponent resolutionVerticalIntIso
  resolutionVerticalIntIso_component localCechComplexInt
  mapExtendIso mapExtendIso_hom_f)
open CategoryTheory.Functor

variable {M : AmbientSheaves.{a} R} (J : InjectiveResolution M)

private def localCochainIntIso (q : ℕ) :
    CechSequenceOriginal.localCechComplexInt.{u,r,a,v} R c M q ≅
      ((originalScalars.{u,r,a,v} R c).mapHomologicalComplex (.up ℤ)).obj
        (CechToCohomology.localCechComplexInt (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
          ((transport.{a} R).obj M) q) :=
  let T := originalScalars.{u,r,a,v} R c
  let ee := ComplexShape.embeddingUpIntGE 0
  (ee.extendFunctor _).mapIso (localCochainIso.{u,r,a,v} R c J q) ≪≫
    (mapExtendIso T _ ee).symm

private lemma localCochainIntIso_hom_f (p q : ℕ) :
    let S := originalScalars.{u,r,a,v} R c
    let ee := ComplexShape.embeddingUpIntGE 0
    let hp : ee.f p = (p : ℤ) := by simp [ee]
    let L := cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)
    let L' := CechToCohomology.cechComplex (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
      ((CechToCohomology.localCohomology (liftedRing.{a} R) q).obj ((transport.{a} R).obj M))
    (localCochainIntIso.{u,r,a,v} R c J q).hom.f (p : ℤ) ≫ S.map (L'.extendXIso ee hp).hom =
      (L.extendXIso ee hp).hom ≫ (localCochainIso.{u,r,a,v} R c J q).hom.f p := by
  let ee := ComplexShape.embeddingUpIntGE 0
  let S := originalScalars.{u,r,a,v} R c
  let L' := CechToCohomology.cechComplex (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
    ((CechToCohomology.localCohomology (liftedRing.{a} R) q).obj ((transport.{a} R).obj M))
  let e := mapExtendIso S L' ee
  let hp : ee.f p = (p : ℤ) := by simp [ee]
  have h : e.inv.f (p : ℤ) ≫ S.map (L'.extendXIso ee hp).hom =
      (((S.mapHomologicalComplex (.up ℕ)).obj L').extendXIso ee hp).hom := by
    rw [← cancel_epi (e.hom.f (p : ℤ)), ← Category.assoc]
    have hi := HomologicalComplex.congr_hom e.hom_inv_id (p : ℤ)
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f] at hi
    rw [hi, Category.id_comp]
    exact (mapExtendIso_hom_f S L' ee hp).symm
  dsimp only [localCochainIntIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    HomologicalComplex.comp_f, ComplexShape.Embedding.extendFunctor_map]
  rw [Category.assoc, h, HomologicalComplex.extendMap_f _ _ hp]
  simp only [Category.assoc]
  have hc : ((((S.mapHomologicalComplex (.up ℕ)).obj L').extendXIso ee hp).inv ≫
      (((S.mapHomologicalComplex (.up ℕ)).obj L').extendXIso ee hp).hom) = 𝟙 _ :=
    (((S.mapHomologicalComplex (.up ℕ)).obj L').extendXIso ee hp).inv_hom_id
  rw [hc, Category.comp_id]

private lemma verticalComponent_nat_transport (p q : ℕ) :
    let S := originalScalars.{u,r,a,v} R c
    let J' := raisedResolution.{u,r,a} R J
    let c' := liftCover.{u,a,r,v} c
    let R' := liftedRing.{a} R
    let G := CechToCohomology.cechTerm R' c' p
    let F := cochainFunctor.{u,r,a,v} R c ⋙ HomologicalComplex.eval _ (.up ℕ) p
    let K := underlyingComplex.{u,r,a} R J.cocomplex
    let L := CechToCohomology.underlyingComplex R' J'.cocomplex
    HomologicalComplex.homologyMap ((doubleIso.{u,r,a,v} R c J.cocomplex).hom.f p) q ≫
      ((((resolutionDoubleComplex R' c' ((transport.{a} R).obj M) J').X p).sc q).mapHomologyIso S).hom ≫
      S.map (((L.sc q).mapHomologyIso G).hom ≫
        G.map (J'.isoRightDerivedObj (SheafOfModules.forget R') q).inv) =
    ((K.sc q).mapHomologyIso F).hom ≫
      F.map (J.isoRightDerivedObj (SheafOfModules.forget R) q).inv ≫
      (localCochainIso.{u,r,a,v} R c J q).hom.f p := by
  let S := originalScalars.{u,r,a,v} R c
  let R' := liftedRing.{a} R
  let c' := liftCover.{u,a,r,v} c
  let J' := raisedResolution.{u,r,a} R J
  let G := CechToCohomology.cechTerm R' c' p
  let eval := HomologicalComplex.eval (CochainModules.{u,r,a,v} R (U := U)) (.up ℕ) p
  let F := cochainFunctor.{u,r,a,v} R c ⋙ eval
  let K := underlyingComplex.{u,r,a} R J.cocomplex
  let η : F ≅ transportPresheaf.{a} R ⋙ G ⋙ S :=
    isoWhiskerRight (presheafCochainIso.{u,r,a,v} R c) eval
  have h : ((doubleIso.{u,r,a,v} R c J.cocomplex).hom.f p) =
      ((NatIso.mapHomologicalComplex η (.up ℕ)).app K).hom := by
    apply HomologicalComplex.hom_ext
    intro n
    rfl
  dsimp only
  rw [h]
  simp only [← Category.assoc]
  exact (compareExactModel (transportPresheaf.{a} R) F G S (K.sc q) η
    (J.isoRightDerivedObj (SheafOfModules.forget R) q)
    (J'.isoRightDerivedObj (SheafOfModules.forget R') q)).symm

end VerticalCarrier

section ExtendedColumnHomology

open CechToCohomology (mapExtendIso)
open HomologicalComplex

variable {B D : Type*} [Category* B] [Category* D] [Abelian B] [Abelian D]
  (S : B ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]

private lemma compareExtendedHomology {K : CochainComplex D ℕ} {L : CochainComplex B ℕ}
    {KI : CochainComplex D ℤ} {LI : CochainComplex B ℤ}
    (k : KI ≅ K.extend embedding) (l : LI ≅ L.extend embedding)
    (f : K ⟶ (S.mapHomologicalComplex (.up ℕ)).obj L)
    (fi : KI ⟶ (S.mapHomologicalComplex (.up ℤ)).obj LI)
    (h : fi ≫ (S.mapHomologicalComplex (.up ℤ)).map l.hom ≫ (mapExtendIso S L embedding).hom =
      k.hom ≫ extendMap f embedding)
    (q : ℕ) :
    let hq : embedding.f q = (q : ℤ) := by simp [embedding]
    homologyMap fi (q : ℤ) ≫ ((LI.sc (q : ℤ)).mapHomologyIso S).hom ≫
      S.map (homologyMap l.hom (q : ℤ) ≫ (L.extendHomologyIso embedding hq).hom) =
    homologyMap k.hom (q : ℤ) ≫ (K.extendHomologyIso embedding hq).hom ≫
      homologyMap f q ≫ ((L.sc q).mapHomologyIso S).hom := by
  dsimp only
  let H := S.mapHomologicalComplex (.up ℤ)
  let hq : embedding.f q = (q : ℤ) := by simp [embedding]
  let F := HomologicalComplex.shortComplexFunctor B (.up ℤ) (q : ℤ)
  have hl : ((LI.sc (q : ℤ)).mapHomologyIso S).hom ≫ S.map (homologyMap l.hom (q : ℤ)) =
      homologyMap (H.map l.hom) (q : ℤ) ≫
        ((((L.extend embedding).sc (q : ℤ))).mapHomologyIso S).hom :=
    (ShortComplex.mapHomologyIso_hom_naturality (F.map l.hom) S).symm
  have he := extendHomologyIso_mapHomologyIso S L q
  have hh := congrArg (fun g ↦ homologyMap g (q : ℤ)) h
  simp only [homologyMap_comp, Category.assoc] at hh
  rw [S.map_comp, ← Category.assoc (((LI.sc (q : ℤ)).mapHomologyIso S).hom),
    hl, Category.assoc, ← he]
  rw [← Category.assoc (homologyMap (H.map l.hom) _),
    ← Category.assoc (homologyMap fi _), hh, Category.assoc]
  rw [HomologicalComplex.extendHomologyIso_hom_naturality_assoc]

end ExtendedColumnHomology

section IntegerVerticalCarrier

open CechToCohomology (resolutionColumnIso resolutionVerticalIntIso resolutionVerticalComponent
  resolutionVerticalIntIso_component)
open DoubleComplexFirstPages (verticalHomology)

variable {M : AmbientSheaves.{a} R} (J : InjectiveResolution M)

set_option maxHeartbeats 2600000 in
private lemma verticalIso_carrierTransport (q : ℕ) :
    let S := originalScalars.{u,r,a,v} R c
    let R' := liftedRing.{a} R
    let c' := liftCover.{u,a,r,v} c
    let M' := (transport.{a} R).obj M
    let J' := raisedResolution.{u,r,a} R J
    (verticalHomologyTransportIso S (doubleIntIso.{u,r,a,v} R c J.cocomplex) (q : ℤ)).hom ≫
        (S.mapHomologicalComplex (.up ℤ)).map (resolutionVerticalIntIso R' c' M' J' q).hom =
      (verticalIso.{u,r,a,v} R c J q).hom ≫ (localCochainIntIso.{u,r,a,v} R c J q).hom := by
  dsimp only
  let S := originalScalars.{u,r,a,v} R c
  let R' := liftedRing.{a} R
  let c' := liftCover.{u,a,r,v} c
  let M' := (transport.{a} R).obj M
  let J' := raisedResolution.{u,r,a} R J
  let K := doubleComplex.{u,r,a,v} R c J.cocomplex
  let L := raisedDouble.{u,r,a,v} R c J.cocomplex
  let C := CechSequenceOriginal.localCechComplexInt.{u,r,a,v} R c M q
  let v := verticalIso.{u,r,a,v} R c J q
  let w := resolutionVerticalIntIso R' c' M' J' q
  let u := localCochainIntIso.{u,r,a,v} R c J q
  apply HomologicalComplex.hom_ext
  intro p
  by_cases hp : 0 ≤ p
  · let n := p.toNat
    have hn : (n : ℤ) = p := Int.toNat_of_nonneg hp
    rw [← hn]
    let P := CechToCohomology.cechComplex R' c' ((CechToCohomology.localCohomology R' q).obj M')
    let e := (P.extendXIso embedding (by simp [embedding] :
      embedding.f n = (n : ℤ))).hom
    apply (cancel_mono (S.map e)).1
    let E := doubleIntIso.{u,r,a,v} R c J.cocomplex
    let z := verticalHomologyTransportIso S E (q : ℤ)
    let rk := (resolutionVerticalComponent R' c' M' J' n q).hom
    let ok := (verticalComponent.{u,r,a,v} R c J n q).hom
    let f := (localCochainIso.{u,r,a,v} R c J q).hom.f n
    have hv : v.hom.f (n : ℤ) ≫ _ = ok :=
      verticalIso_component.{u,r,a,v} R c J n q
    have hw : w.hom.f (n : ℤ) ≫ e = rk :=
      resolutionVerticalIntIso_component R' c' M' J' n q
    have hu := localCochainIntIso_hom_f.{u,r,a,v} R c J n q
    change (z.hom.f (n : ℤ) ≫ S.map (w.hom.f (n : ℤ))) ≫ S.map e =
      (v.hom.f (n : ℤ) ≫ u.hom.f (n : ℤ)) ≫ S.map e
    rw [Category.assoc, ← S.map_comp, hw, Category.assoc, hu, ← Category.assoc (v.hom.f (n : ℤ)), hv]
    let ek := extendedColumnIso K n
    let el := extendedColumnIso L n
    have hcol := comparedBicomplexColumn S (doubleIso.{u,r,a,v} R c J.cocomplex) n
    have hcomp := compareExtendedHomology S ek el ((doubleIso.{u,r,a,v} R c J.cocomplex).hom.f n)
      (E.hom.f (n : ℤ)) hcol q
    let Z := underlyingComplex.{u,r,a} R J.cocomplex
    let Z' := CechToCohomology.underlyingComplex R' J'.cocomplex
    let G := CechToCohomology.cechTerm R' c' n
    let F := cochainFunctor.{u,r,a,v} R c ⋙ HomologicalComplex.eval _ (.up ℕ) n
    let a := ((Z.sc q).mapHomologyIso F).hom ≫ F.map (J.isoRightDerivedObj (SheafOfModules.forget R) q).inv
    let b := ((Z'.sc q).mapHomologyIso G).hom ≫ G.map (J'.isoRightDerivedObj (SheafOfModules.forget R') q).inv
    let hq : embedding.f q = (q : ℤ) := by simp [embedding]
    let k := HomologicalComplex.homologyMap ek.hom (q : ℤ) ≫ ((K.X n).extendHomologyIso embedding hq).hom
    let l := HomologicalComplex.homologyMap el.hom (q : ℤ) ≫ ((L.X n).extendHomologyIso embedding hq).hom
    let g := HomologicalComplex.homologyMap ((doubleIso.{u,r,a,v} R c J.cocomplex).hom.f n) q ≫
      (((L.X n).sc q).mapHomologyIso S).hom
    have ht : g ≫ S.map b = a ≫ f := by
      have h' := verticalComponent_nat_transport.{u,r,a,v} R c J n q
      dsimp only at h'
      change (_ ≫ _) ≫ S.map b = (_ ≫ _) ≫ f
      rw [Category.assoc, Category.assoc]
      exact h'
    have hx : z.hom.f (n : ℤ) ≫ S.map l = k ≫ g := by
      dsimp only [z, verticalHomologyTransportIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
        transportedHomology, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom, asIso_hom]
      simpa only [k, g, Category.assoc] using hcomp
    have hL : rk = l ≫ b := by
      simp only [rk, l, b, resolutionVerticalComponent, Iso.trans_hom, Functor.mapIso_hom,
        HomologicalComplex.homologyMapIso_hom, Category.assoc]
      rfl
    have hK : ok = k ≫ a := by
      simp only [ok, k, a, verticalComponent, Iso.trans_hom, Functor.mapIso_hom,
        HomologicalComplex.homologyMapIso_hom, Category.assoc]
      rfl
    rw [hL, hK, S.map_comp, ← Category.assoc, hx, Category.assoc, ht, Category.assoc]
    change k ≫ a ≫ f = (k ≫ a) ≫ f
    exact (Category.assoc _ _ _).symm
  · have hC : IsZero (C.X p) := HomologicalComplex.isZero_extend_X _ embedding _ (fun n h ↦ by
      have hs : embedding.f n = (n : ℤ) := by simp [embedding]
      rw [hs] at h
      omega)
    have h0 := hC.of_iso ((HomologicalComplex.eval _ (.up ℤ) p).mapIso v)
    exact h0.eq_of_src _ _

end IntegerVerticalCarrier

section SecondPageCarrier

open CechToCohomology (resolutionDoubleComplexInt resolutionVerticalIntIso
  resolutionSpectralData resolutionSecondPageIso resolutionSecondIntIso mapExtendIso)
open DoubleComplexFirstPages (page verticalHomology)

variable {M : AmbientSheaves.{a} R} (J : InjectiveResolution M)

/-- The local Čech cohomology comparison is the homology of the same
alternating restriction complex over the original section ring. -/
def localCechHomologyTransport (p q : ℕ) :
    (CechSequenceOriginal.localCechCohomology.{u,r,a,v} R c p q).obj M ≅
      (originalScalars.{u,r,a,v} R c).obj
        ((CechToCohomology.localCechCohomology (liftedRing.{a} R)
          (liftCover.{u,a,r,v} c) p q).obj ((transport.{a} R).obj M)) :=
  let L := CechToCohomology.cechComplex (liftedRing.{a} R) (liftCover.{u,a,r,v} c)
    ((CechToCohomology.localCohomology (liftedRing.{a} R) q).obj ((transport.{a} R).obj M))
  HomologicalComplex.homologyMapIso (localCochainIso.{u,r,a,v} R c J q) p ≪≫
    (L.sc p).mapHomologyIso (originalScalars.{u,r,a,v} R c)

private lemma localCechHomologyTransport_extend (p q : ℕ) :
    let S := originalScalars.{u,r,a,v} R c
    let R' := liftedRing.{a} R
    let c' := liftCover.{u,a,r,v} c
    let M' := (transport.{a} R).obj M
    let L := cochainComplex.{u,r,a,v} R c ((CechSequenceOriginal.localCohomology.{u,r,a} R q).obj M)
    let L' := CechToCohomology.cechComplex R' c' ((CechToCohomology.localCohomology R' q).obj M')
    let hp : embedding.f p = (p : ℤ) := by simp [embedding]
    (transportedHomology S (localCochainIntIso.{u,r,a,v} R c J q) (p : ℤ)).hom ≫
      S.map (L'.extendHomologyIso embedding hp).hom =
      (L.extendHomologyIso embedding hp).hom ≫ (localCechHomologyTransport.{u,r,a,v} R c J p q).hom := by
  let S := originalScalars.{u,r,a,v} R c
  let R' := liftedRing.{a} R
  let c' := liftCover.{u,a,r,v} c
  let M' := (transport.{a} R).obj M
  let L := cochainComplex.{u,r,a,v} R c ((CechSequenceOriginal.localCohomology.{u,r,a} R q).obj M)
  let L' := CechToCohomology.cechComplex R' c' ((CechToCohomology.localCohomology R' q).obj M')
  let w := localCochainIso.{u,r,a,v} R c J q
  let e := mapExtendIso S L' embedding
  let v := localCochainIntIso.{u,r,a,v} R c J q
  have h : v.hom ≫ (S.mapHomologicalComplex (.up ℤ)).map (Iso.refl (L'.extend embedding)).hom ≫ e.hom =
      (Iso.refl (L.extend embedding)).hom ≫ HomologicalComplex.extendMap w.hom embedding := by
    change ((HomologicalComplex.extendMap w.hom embedding) ≫ e.inv) ≫
      (S.mapHomologicalComplex (.up ℤ)).map (𝟙 _) ≫ e.hom = 𝟙 _ ≫ _
    have hid := (S.mapHomologicalComplex (.up ℤ)).map_id (L'.extend embedding)
    rw [hid]
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h' := compareExtendedHomology S (Iso.refl (L.extend embedding))
    (Iso.refl (L'.extend embedding)) w.hom v.hom h p
  simp only [Iso.refl_hom, HomologicalComplex.homologyMap_id, Category.id_comp] at h'
  exact h'

set_option maxHeartbeats 2600000 in
/-- The actual second-page map of the signed total filtration agrees with
the induced map of Čech cohomology of the original local cohomology presheaf. -/
theorem secondPageComparison_transport (p q : ℕ) :
    let S := originalScalars.{u,r,a,v} R c
    let R' := liftedRing.{a} R
    let c' := liftCover.{u,a,r,v} c
    let M' := (transport.{a} R).obj M
    let J' := raisedResolution.{u,r,a} R J
    let D := spectralData.{u,r,a,v} R c J
    let E := resolutionSpectralData R' c' M' J'
    let h := signedTotalIso_filtration.{u,r,a,v} R c J.cocomplex D E
    let t := signedTotalIso.{u,r,a,v} R c J.cocomplex
    let θ := pageTransportIso S D.filtration E.filtration t h D.pages E.pages
      2 (by omega) (p : ℤ) ((p : ℤ) + (q : ℤ))
    θ.hom ≫ S.map (resolutionSecondPageIso R' c' M' J' p q).hom =
      (secondPageComparison.{u,r,a,v} R c J D (verticalIso.{u,r,a,v} R c J) p q).hom ≫
        (localCechHomologyTransport.{u,r,a,v} R c J p q).hom := by
  let S := originalScalars.{u,r,a,v} R c
  let R' := liftedRing.{a} R
  let c' := liftCover.{u,a,r,v} c
  let M' := (transport.{a} R).obj M
  let J' := raisedResolution.{u,r,a} R J
  let D := spectralData.{u,r,a,v} R c J
  let E := resolutionSpectralData R' c' M' J'
  let h := signedTotalIso_filtration.{u,r,a,v} R c J.cocomplex D E
  let t := signedTotalIso.{u,r,a,v} R c J.cocomplex
  let e := doubleIntIso.{u,r,a,v} R c J.cocomplex
  let z := verticalHomologyTransportIso S e (q : ℤ)
  let w := localCochainIntIso.{u,r,a,v} R c J q
  let v := verticalIso.{u,r,a,v} R c J q
  let v' := resolutionVerticalIntIso R' c' M' J' q
  have hcol := columnSecondIso_transport S D E e t h
    (signedTotalIso_injection.{u,r,a,v} R c J.cocomplex) (p : ℤ) (q : ℤ)
  have hv := transportedHomology_natural S z w v.hom v'.hom
    (verticalIso_carrierTransport.{u,r,a,v} R c J q).symm (p : ℤ)
  have he := localCechHomologyTransport_extend.{u,r,a,v} R c J p q
  dsimp only [resolutionSecondPageIso, resolutionSecondIntIso, secondPageComparison,
    Iso.trans_hom, HomologicalComplex.homologyMapIso_hom, Functor.mapIso_hom]
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, hcol, Category.assoc,
    ← Category.assoc ((CechToCohomology.columnSecondPageIso D (p : ℤ) (q : ℤ)).hom),
    Category.assoc, ← Category.assoc (transportedHomology S z (p : ℤ)).hom]
  change (CechToCohomology.columnSecondPageIso D (p : ℤ) (q : ℤ)).hom ≫
      ((transportedHomology S z (p : ℤ)).hom ≫
        S.map (HomologicalComplex.homologyMap v'.hom (p : ℤ))) ≫ _ = _
  rw [← hv, specifiedColumnSecondIso_eq D]
  simp only [Category.assoc]
  rw [he]

end SecondPageCarrier

set_option maxHeartbeats 2600000 in
theorem second_page_transport :
    Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients.secondPageCarrierTransport.{u,r,a,v} := by
  intro X R U A c _
  let R' := liftedRing.{a} R
  let c' := liftCover.{u,a,r,v} c
  let S := originalScalars.{u,r,a,v} R c
  refine ⟨inferInstance, inferInstance, coefficientNaturalityData.{u,r,a,v} R c,
    CechToCohomology.cechSpectralSequence R' c', presheafCochainIso.{u,r,a,v} R c,
    fun _ _ _ _ ↦ rfl, ?_⟩
  intro M J
  let D := spectralData.{u,r,a,v} R c J
  let E := CechToCohomology.resolutionSpectralData R' c' ((transport.{a} R).obj M)
    (raisedResolution.{u,r,a} R J)
  let t := signedTotalIso.{u,r,a,v} R c J.cocomplex
  let h := signedTotalIso_filtration.{u,r,a,v} R c J.cocomplex D E
  refine ⟨doubleIntIso.{u,r,a,v} R c J.cocomplex, t,
    fun p q x ↦ heq_of_eq (doubleIntIso_apply.{u,r,a,v} R c J.cocomplex p q x),
    signedTotalIso_injection.{u,r,a,v} R c J.cocomplex, ?_⟩
  intro p q
  let n := (p : ℤ) + (q : ℤ)
  exact ⟨almostCycleTransportIso S D.filtration E.filtration t h 2 (p : ℤ) n,
    pageTransportIso S D.filtration E.filtration t h D.pages E.pages 2 (by omega) (p : ℤ) n,
    almostCycleTransportIso_arrow S D.filtration E.filtration t h 2 (p : ℤ) n,
    pageTransportIso_representative S D.filtration E.filtration t h D.pages E.pages
      2 (by omega) (p : ℤ) n,
    secondPageComparison_transport.{u,r,a,v} R c J p q⟩

section InjectiveCarrier
private def ringLiftForgetIso :
    ringLift.{b,max a u r} ⋙ forget₂ RingCat.{max b a u r} AddCommGrpCat.{max b a u r} ≅
      forget₂ RingCat.{max a u r} AddCommGrpCat.{max a u r} ⋙
        AddCommGrpCat.uliftFunctor.{b,max a u r} :=
  Iso.refl _

private instance ringLiftPreservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{u,u} (ringLift.{b,max a u r}) where
  preserves_filtered_colimits := by
    intro J _ _
    let F := ringLift.{b,max a u r}
    let G := forget₂ RingCat.{max b a u r} AddCommGrpCat.{max b a u r}
    let H := forget₂ RingCat.{max a u r} AddCommGrpCat.{max a u r}
    letI : PreservesFilteredColimitsOfSize.{u,u} G := preservesFilteredColimitsOfSize_shrink G
    letI : PreservesFilteredColimitsOfSize.{u,u} H := preservesFilteredColimitsOfSize_shrink H
    haveI : PreservesColimitsOfShape J (F ⋙ G) :=
      preservesColimitsOfShape_of_natIso (ringLiftForgetIso.{u,r,a,b}).symm
    let _ : HasColimitsOfShape J RingCat.{max a b u r} :=
      ⟨fun F ↦ HasColimit.mk ⟨_, RingCat.FilteredColimits.colimitCoconeIsColimit.{u,max a b u r} F⟩⟩
    let _ : ReflectsColimitsOfShape J G := reflectsColimitsOfShape_of_reflectsIsomorphisms
    exact preservesColimitsOfShape_of_reflects_of_preserves F G

variable (x : X)

private def stalkRingDiagramIso :
    ringNeighborhoods.{a} R x ⋙ ringLift.{b} ≅ ringNeighborhoods.{max a b} R x :=
  NatIso.ofComponents (fun i ↦
    ((ULift.ringEquiv.trans ULift.ringEquiv).trans ULift.ringEquiv.symm).toRingCatIso)
    (by intro i j f; ext z; rfl)

private def liftedStalkRingIso :
    (ringLift.{b}).obj (originalStalkRing.{a} R x) ≅ originalStalkRing.{max a b} R x :=
  let _ : PreservesFilteredColimitsOfSize.{u,u} (ringLift.{b,max a u r}) :=
    ringLiftPreservesFilteredColimits.{u,r,a,b}
  let e := stalkRingDiagramIso.{u,r,a,b} R x
  letI := hasColimit_of_iso e
  preservesColimitIso (ringLift.{b,max a u r}) (ringNeighborhoods.{a} R x) ≪≫ HasColimit.isoOfNatIso e

private def loweredStalkRingEquiv :
    originalStalkRing.{max a b} R x ≃+* originalStalkRing.{a} R x :=
  (liftedStalkRingIso.{u,r,a,b} R x).symm.ringCatIsoToRingEquiv.trans ULift.ringEquiv

private lemma loweredStalkRingEquiv_germ (V : Opens X) (hx : x ∈ V)
    (z : R.obj.obj (op V)) :
    loweredStalkRingEquiv.{u,r,a,b} R x (originalRingGerm.{max a b} R x V hx z) =
      originalRingGerm.{a} R x V hx z := by
  let L := ringLift.{b,max a u r}
  let D := ringNeighborhoods.{a} R x
  let i := op (⟨V, hx⟩ : OpenNhds x)
  let e := stalkRingDiagramIso.{u,r,a,b} R x
  let _ : HasColimit D := inferInstanceAs (HasColimit (ringNeighborhoods.{a} R x))
  let _ : HasColimit (D ⋙ L) := hasColimit_of_iso e
  let _ : PreservesFilteredColimitsOfSize.{u,u} L := ringLiftPreservesFilteredColimits.{u,r,a,b}
  have h : L.map (colimit.ι D i) ≫ (liftedStalkRingIso.{u,r,a,b} R x).hom =
      e.hom.app i ≫ colimit.ι (ringNeighborhoods.{max a b} R x) i := by
    dsimp only [liftedStalkRingIso, Iso.trans_hom]
    rw [ι_preservesColimitIso_hom_assoc, HasColimit.ι_isoOfNatIso_hom]
  have w := congr($(h) (ULift.up (ULift.up z)))
  change (liftedStalkRingIso.{u,r,a,b} R x).hom (ULift.up (originalRingGerm.{a} R x V hx z)) =
    originalRingGerm.{max a b} R x V hx z at w
  rw [← w]
  exact congrArg ULift.down
    (congr($((liftedStalkRingIso.{u,r,a,b} R x).hom_inv_id) (ULift.up (originalRingGerm.{a} R x V hx z))))

private def liftStalkModule :
    ModuleCat.{max a u r} (originalStalkRing.{a} R x) ⥤
      ModuleCat.{max a b u r} (originalStalkRing.{max a b} R x) :=
  ModuleCat.uliftFunctor.{b} _ ⋙ ModuleCat.restrictScalars
    (loweredStalkRingEquiv.{u,r,a,b} R x).toRingHom

private lemma liftStalkModule_injective (N : ModuleCat.{max a u r} (originalStalkRing.{a} R x))
    [Injective N] : Injective ((liftStalkModule.{u,r,a,b} R x).obj N) := by
  letI : (ModuleCat.restrictScalars.{max a b u r}
    (loweredStalkRingEquiv.{u,r,a,b} R x).toRingHom).IsEquivalence :=
      ModuleCat.restrictScalars_isEquivalence_of_ringEquiv _
  letI : Small.{max a u r} (originalStalkRing.{a} R x) := small_self _
  let F := ModuleCat.uliftFunctor.{b,max a u r} (originalStalkRing.{a} R x)
  let G := ModuleCat.restrictScalars.{max a b u r} (loweredStalkRingEquiv.{u,r,a,b} R x).toRingHom
  have h : Injective (F.obj N) := Functor.injective_obj (ModuleCat.uliftFunctor.{b,max a u r} _) N
  let _ : G.PreservesInjectiveObjects := inferInstanceAs
    ((ModuleCat.restrictScalars.{max a b u r} (loweredStalkRingEquiv.{u,r,a,b} R x).toRingHom).PreservesInjectiveObjects)
  exact G.injective_obj_of_injective h

private def liftSkyscraperIso (N : ModuleCat.{max a u r} (originalStalkRing.{a} R x)) :
    (liftSheafCoefficients.{b,u,r,max a u r} R).obj
        ((originalSkyscraperFunctor.{a} R x).obj N) ≅
      (originalSkyscraperFunctor.{max a b} R x).obj ((liftStalkModule.{u,r,a,b} R x).obj N) := by
  apply (SheafOfModules.fullyFaithfulForget R).preimageIso
  refine PresheafOfModules.isoMk (fun V ↦ ?_) ?_
  · let A := ((liftCoefficients.{b,u,r,max a u r} R.obj).obj
        (originalSkyscraperPresheaf.{a} R x N)).obj V
    let B := (originalSkyscraperPresheaf.{max a b} R x
      ((liftStalkModule.{u,r,a,b} R x).obj N)).obj V
    exact @LinearEquiv.toModuleIso _ _ A B A.isAddCommGroup B.isAddCommGroup A.isModule B.isModule (by
      refine
        { toFun := fun s hx ↦ ULift.up (s.down hx)
          invFun := fun s ↦ ULift.up (fun hx ↦ (s hx).down)
          left_inv := fun s ↦ rfl
          right_inv := fun s ↦ rfl
          map_add' := fun s t ↦ rfl
          map_smul' := fun c s ↦ ?_ }
      funext hx
      change ULift.up (originalRingGerm.{a} R x V.unop hx.down c • s.down hx) =
        ULift.up (loweredStalkRingEquiv.{u,r,a,b} R x
          (originalRingGerm.{max a b} R x V.unop hx.down c) • s.down hx)
      rw [loweredStalkRingEquiv_germ])
  · intros
    ext s
    funext hx
    rfl

private lemma liftSheafPreservesProducts :
    PreservesLimitsOfShape (Discrete X) (liftSheafCoefficients.{b,u,r,max a u r} R) := by
  let F := liftSheafCoefficients.{b,u,r,max a u r} R
  let G := SheafOfModules.forget.{max a b u r} R ⋙
    PresheafOfModules.toPresheaf.{max a b u r} R.obj
  let H := SheafOfModules.forget.{max a u r} R ⋙
    PresheafOfModules.toPresheaf.{max a u r} R.obj
  let J := (Functor.whiskeringRight ((Opens X)ᵒᵖ) _ _).obj AddCommGrpCat.uliftFunctor.{b,max a u r}
  haveI : PreservesLimitsOfShape (Discrete X) (F ⋙ G) := by
    change PreservesLimitsOfShape (Discrete X) (H ⋙ J)
    infer_instance
  letI : ReflectsLimitsOfShape (Discrete X) G := reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves F G

private lemma liftSheafCoefficients_injective (M : AmbientSheaves.{a} R) [Injective M] :
    Injective ((liftSheafCoefficients.{b,u,r,max a u r} R).obj M) := by
  let F := liftSheafCoefficients.{b,u,r,max a u r} R
  let N (x : X) := Injective.under ((originalStalkFunctor.{a} R x).obj M)
  let P (x : X) := (originalSkyscraperFunctor.{a} R x).obj (N x)
  let Q (x : X) := (originalSkyscraperFunctor.{max a b} R x).obj ((liftStalkModule.{u,r,a,b} R x).obj (N x))
  let f : M ⟶ ∏ᶜ P := originalStalkProductMap.{a} N (fun x ↦ Injective.ι _)
  letI : Mono f := originalStalkProductMap_mono.{a} N (fun x ↦ Injective.ι _)
  letI (x : X) : Injective (Q x) :=
    (originalStalkSkyscraperAdjunction.{max a b} R x).map_injective _
      (liftStalkModule_injective R x (N x))
  letI (x : X) : Injective (F.obj (P x)) :=
    Injective.of_iso (liftSkyscraperIso.{u,r,a,b} R x (N x)).symm inferInstance
  letI : Injective (∏ᶜ (fun x ↦ F.obj (P x))) := inferInstance
  letI := liftSheafPreservesProducts.{u,r,a,b} R
  letI : Injective (F.obj (∏ᶜ P)) := Injective.of_iso (PreservesProduct.iso F P).symm inferInstance
  let retract : Retract M (∏ᶜ P) := ⟨f, Injective.factorThru (𝟙 M) f, Injective.comp_factorThru _ _⟩
  exact (retract.map F).injective

end InjectiveCarrier

section CarrierLift

open CategoryTheory.Functor
open HomologicalComplex
open CechToCohomology (natToIntDoubleComplex mapExtendIso)
open FiniteDiagonalFiltrations

set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cochainCarrierLift.{u,r,a,v,b} R c
set_option quotPrecheck false in
set_option hygiene false in
local notation "L" => sheafCarrierLift.{u,r,a,b} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "P" => presheafCarrierLift.{u,r,a,b} R

private instance carrierLiftPreservesColimits :
    PreservesColimitsOfSize.{0,0} S :=
  moduleLiftPreservesSmallColimits.{r,max a u v,b} (sectionRing R U)

private instance presheafCarrierLimits : PreservesFiniteLimits P :=
  (coefficient_lift_presheaf_exact.{b,u,r,max a u r} X R.obj).1

private instance presheafCarrierColimits : PreservesFiniteColimits P :=
  (coefficient_lift_presheaf_exact.{b,u,r,max a u r} X R.obj).2

private instance sheafCarrierLimits : PreservesFiniteLimits L :=
  (coefficient_lift_ambient_sheaf_exact.{b,u,r,a} X R).1

private instance sheafCarrierColimits : PreservesFiniteColimits L :=
  (coefficient_lift_ambient_sheaf_exact.{b,u,r,a} X R).2

private instance sheafCarrierPreservesInjectives : (L).PreservesInjectiveObjects where
  injective_obj {M} h := by
    let _ := h
    exact liftSheafCoefficients_injective.{u,r,a,b} R M

@[simp]
lemma carrierLiftResolution_ι_zero {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    (carrierLiftResolution.{u,r,a,b} R J).ι.f 0 = (L).map (J.ι.f 0) := by
  simp only [carrierLiftResolution, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Functor.mapHomologicalComplex_map_f]
  rfl

/-- The full unrestricted product of section carrier lifts, including its differential. -/
def cochainLiftNatIso :
    cochainFunctor.{u,r,a,v} R c ⋙ (S).mapHomologicalComplex (.up ℕ) ≅
      P ⋙ cochainFunctor.{u,r,max a b,v} R c :=
  orderedCochainLiftIso.{u,r,max a u r,v,b} R c

set_option quotPrecheck false in
set_option hygiene false in
local notation "T" => (cochainLiftNatIso.{u,r,a,v,b} R c)

/-- At bidegree (p,q) the inverse comparison lifts each original tuple section. -/
def doubleCarrierIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    doubleComplex.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K) ≅
      (mapDouble S).obj (doubleComplex.{u,r,a,v} R c K) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun p ↦
    HomologicalComplex.Hom.isoOfComponents (fun q ↦
      (HomologicalComplex.eval _ (.up ℕ) p).mapIso ((T).app (K.X q).val).symm) ?_) ?_
  · intro q q' _
    exact congrArg (fun f ↦ f.f p) ((T).inv.naturality (K.d q q').val).symm
  · intro p p' _
    apply HomologicalComplex.hom_ext
    intro q
    exact ((T).inv.app (K.X q).val).comm p p'

/-- Zero extension of the carrier comparison on the same tuple sections. -/
def doubleCarrierIntIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    doubleComplexInt.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K) ≅
      (mapIntDouble S).obj (doubleComplexInt.{u,r,a,v} R c K) :=
  (embedding.extendFunctor _).mapIso
    (((embedding.extendFunctor _).mapHomologicalComplex (.up ℕ)).mapIso
      (doubleCarrierIso.{u,r,a,v,b} R c K)) ≪≫
    (mapIntDoubleIso S _).symm

lemma doubleCarrierIntIso_apply (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (p q : ℕ) (s : Cochains R ((liftSheafComplex.{u,r,a,b} R K).X q).val c p) :
    let e := doubleCarrierIntIso.{u,r,a,v,b} R c K
    let I := intBicomplexTermIso (doubleComplex.{u,r,max a b,v} R c
      (liftSheafComplex.{u,r,a,b} R K)) p q
    let J := intBicomplexTermIso (doubleComplex.{u,r,a,v} R c K) p q
    ((I.inv ≫ (e.hom.f (p : ℤ)).f (q : ℤ) ≫ (S).map J.hom) s) =
      ULift.up (fun t ↦ (s t).down) := by
  dsimp only
  let K' := doubleComplex.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K)
  let L' := doubleComplex.{u,r,a,v} R c K
  have h : ((doubleCarrierIntIso.{u,r,a,v,b} R c K).hom.f (p : ℤ)).f (q : ℤ) ≫
      (S).map (intBicomplexTermIso L' p q).hom =
      (intBicomplexTermIso K' p q).hom ≫ ((doubleCarrierIso.{u,r,a,v,b} R c K).hom.f p).f q :=
    comparedBicomplexTerm S (doubleCarrierIso.{u,r,a,v,b} R c K) p q
  rw [h, Iso.inv_hom_id_assoc]
  rfl

/-- The signed total comparison is induced by the same tuple lift on each summand. -/
def signedTotalCarrierIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    sumTotal (doubleComplexInt.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K)) ≅
      ((S).mapHomologicalComplex (.up ℤ)).obj (sumTotal (doubleComplexInt.{u,r,a,v} R c K)) :=
  HomologicalComplex₂.total.mapIso (doubleCarrierIntIso.{u,r,a,v,b} R c K) (.up ℤ) ≪≫
    totalScalarIso S _

lemma signedTotalCarrierIso_injection (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (p q n : ℤ) (h : p + q = n) :
    sumInjection (doubleComplexInt.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K))
        p q n h ≫ (signedTotalCarrierIso.{u,r,a,v,b} R c K).hom.f n =
      ((doubleCarrierIntIso.{u,r,a,v,b} R c K).hom.f p).f q ≫
        (S).map (sumInjection (doubleComplexInt.{u,r,a,v} R c K) p q n h) := by
  dsimp only [signedTotalCarrierIso, Iso.trans_hom, HomologicalComplex.comp_f,
    HomologicalComplex₂.total.mapIso]
  rw [← Category.assoc, HomologicalComplex₂.ιTotal_map, Category.assoc, totalScalarIso_injection]

lemma signedTotalCarrierIso_filtration (K : CochainComplex (AmbientSheaves.{a} R) ℕ)
    (D : ColumnSpectralData (doubleComplexInt.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K)))
    (E : ColumnSpectralData (doubleComplexInt.{u,r,a,v} R c K))
    (p n : ℤ) :
    Subobject.mk ((D.filtration.piece p n).arrow ≫ (signedTotalCarrierIso.{u,r,a,v,b} R c K).hom.f n) =
      Subobject.mk ((S).map (E.filtration.piece p n).arrow) := by
  let e := doubleCarrierIntIso.{u,r,a,v,b} R c K
  let f (p q : ℤ) := (HomologicalComplex.eval _ (.up ℤ) q).mapIso
    ((HomologicalComplex.eval _ (.up ℤ) p).mapIso e)
  exact filtration_piece_transport S D.filtration E.filtration D.formula E.formula
    (signedTotalCarrierIso.{u,r,a,v,b} R c K) f
    (signedTotalCarrierIso_injection.{u,r,a,v,b} R c K) p n

/-- Swap the two successive carrier lifts on sections, preserving the original
section-ring action. -/
def sectionLiftsIso (V : Opens X) :
    ModuleCat.uliftFunctor.{b,max a u r} (sectionRing R V) ⋙
        ModuleCat.uliftFunctor.{v,max a b u r} (sectionRing R V) ≅
      ModuleCat.uliftFunctor.{v,max a u r} (sectionRing R V) ⋙
        ModuleCat.uliftFunctor.{b,max a u r v} (sectionRing R V) :=
  NatIso.ofComponents (fun N ↦
    ({ toFun := fun x ↦ ULift.up (ULift.up x.down.down)
       invFun := fun x ↦ ULift.up (ULift.up x.down.down)
       left_inv := fun _ ↦ rfl
       right_inv := fun _ ↦ rfl
       map_add' := fun _ _ ↦ rfl
       map_smul' := fun _ _ ↦ rfl } :
      ((ModuleCat.uliftFunctor.{b,max a u r} (sectionRing R V) ⋙
          ModuleCat.uliftFunctor.{v,max a b u r} (sectionRing R V)).obj N) ≃ₗ[sectionRing R V]
        ((ModuleCat.uliftFunctor.{v,max a u r} (sectionRing R V) ⋙
          ModuleCat.uliftFunctor.{b,max a u r v} (sectionRing R V)).obj N)).toModuleIso)
    (by intro M N f; ext x; rfl)

/-- Lift the section comparison to the original ring in the cover universe. -/
private def liftedSectionCarrierNatIso :
    L ⋙ sectionsValue.{max a b,u,r} R U ⋙ sectionLift.{u,r,max a b,v} R c ≅
      sectionsValue.{a,u,r} R U ⋙ sectionLift.{u,r,a,v} R c ⋙ S :=
  isoWhiskerLeft (sectionsValue.{a,u,r} R U) (sectionLiftsIso.{u,r,a,v,b} R U)

private def liftedSectionCarrierIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    liftedSections.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K) ≅
      ((S).mapHomologicalComplex (.up ℕ)).obj (liftedSections.{u,r,a,v} R c K) :=
  (NatIso.mapHomologicalComplex (liftedSectionCarrierNatIso.{u,r,a,v,b} R c) (.up ℕ)).app K

private def intSectionCarrierIso (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    intSections.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K) ≅
      ((S).mapHomologicalComplex (.up ℤ)).obj (intSections.{u,r,a,v} R c K) :=
  (embedding.extendFunctor _).mapIso (liftedSectionCarrierIso.{u,r,a,v,b} R c K) ≪≫
    (mapExtendIso S _ embedding).symm

lemma horizontalAugmentation_carrier (K : CochainComplex (AmbientSheaves.{a} R) ℕ) :
    horizontalAugmentation.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K) ≫
        (doubleCarrierIso.{u,r,a,v,b} R c K).hom.f 0 =
      (liftedSectionCarrierIso.{u,r,a,v,b} R c K).hom ≫
        ((S).mapHomologicalComplex (.up ℕ)).map (horizontalAugmentation.{u,r,a,v} R c K) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

lemma verticalAugmentation_carrier {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    let J' := carrierLiftResolution.{u,r,a,b} R J
    let e := doubleCarrierIso.{u,r,a,v,b} R c J.cocomplex
    verticalAugmentation.{u,r,max a b,v} R c J' ≫
      ((HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)).map e.hom).f 0 =
      ((T).inv.app M.val) ≫
        ((S).mapHomologicalComplex (.up ℕ)).map (verticalAugmentation.{u,r,a,v} R c J) := by
  dsimp only
  apply HomologicalComplex.hom_ext
  intro p
  -- The inverse tuple lift is natural for the genuine augmentation.
  have h := congrArg (fun f ↦ f.f p) ((T).inv.naturality (J.ι.f 0).val)
  change ((cochainFunctor.{u,r,max a b,v} R c).map
      ((carrierLiftResolution.{u,r,a,b} R J).ι.f 0).val).f p ≫
        ((T).inv.app (J.cocomplex.X 0).val).f p = _
  rw [carrierLiftResolution_ι_zero]
  exact h

lemma totalAugmentationMap_carrier [EnoughInjectives (AmbientSheaves.{max a b} R)]
    {M : AmbientSheaves.{a} R} (J : InjectiveResolution M) :
    let J' := carrierLiftResolution.{u,r,a,b} R J
    totalAugmentationMap.{u,r,max a b,v} R c J' ≫ (signedTotalCarrierIso.{u,r,a,v,b} R c J.cocomplex).hom =
      (intSectionCarrierIso.{u,r,a,v,b} R c J.cocomplex).hom ≫
        ((S).mapHomologicalComplex (.up ℤ)).map (totalAugmentationMap.{u,r,a,v} R c J) := by
  let K := J.cocomplex
  have h :
      intHorizontalAugmentation.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K) ≫
          (doubleCarrierIntIso.{u,r,a,v,b} R c K).hom.f 0 =
        (intSectionCarrierIso.{u,r,a,v,b} R c K).hom ≫
          ((S).mapHomologicalComplex (.up ℤ)).map (intHorizontalAugmentation.{u,r,a,v} R c K) :=
    intZeroColumnTransport S (doubleCarrierIso.{u,r,a,v,b} R c K)
      (liftedSectionCarrierIso.{u,r,a,v,b} R c K) _ _
      (horizontalAugmentation_carrier.{u,r,a,v,b} R c K)
  have hn (n : ℤ) := HomologicalComplex.congr_hom h n
  dsimp only
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    totalAugmentationMap_f, Category.assoc, Functor.map_comp]
  change (intHorizontalAugmentation.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K)).f n ≫
      sumInjection (doubleComplexInt.{u,r,max a b,v} R c (liftSheafComplex.{u,r,a,b} R K))
        0 n n (zero_add n) ≫ (signedTotalCarrierIso.{u,r,a,v,b} R c K).hom.f n =
    (intSectionCarrierIso.{u,r,a,v,b} R c K).hom.f n ≫
      (S).map ((intHorizontalAugmentation.{u,r,a,v} R c K).f n) ≫
        (S).map (sumInjection (doubleComplexInt.{u,r,a,v} R c K) 0 n n (zero_add n))
  rw [signedTotalCarrierIso_injection.{u,r,a,v,b} R c K 0 n n (zero_add n)]
  have h' := congrArg (fun f => f ≫ (S).map
    (sumInjection (doubleComplexInt.{u,r,a,v} R c K) 0 n n (zero_add n))) (hn n)
  simpa only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc] using h'

end CarrierLift

section CarrierLocalCohomology

open CategoryTheory.Functor
open HomologicalComplex
open CechToCohomology (mapExtendIso mapExtendIso_hom_f mapHomologyIso_comp_hom columnSecondPageIso)
open DoubleComplexFirstPages (verticalHomology page)

set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cochainCarrierLift.{u,r,a,v,b} R c
set_option quotPrecheck false in
set_option hygiene false in
local notation "L" => sheafCarrierLift.{u,r,a,b} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "P" => presheafCarrierLift.{u,r,a,b} R

variable [EnoughInjectives (AmbientSheaves.{max a b} R)]
variable {M : AmbientSheaves.{a} R} (J : InjectiveResolution M)

namespace ExactLift

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  [Abelian C] [Abelian C'] [Abelian D] [Abelian D']
  (E : C ⥤ C') (F : C ⥤ D) (G : C' ⥤ D') (H : D ⥤ D')
  [E.Additive] [F.Additive] [G.Additive] [H.Additive]
  [PreservesFiniteLimits E] [PreservesFiniteLimits F] [PreservesFiniteLimits G] [PreservesFiniteLimits H]
  [PreservesFiniteColimits E] [PreservesFiniteColimits F] [PreservesFiniteColimits G] [PreservesFiniteColimits H]

private lemma homology_comparison (K : ShortComplex C) (η : F ⋙ H ≅ E ⋙ G)
    {M : C} {N : C'} (i : M ≅ K.homology) (j : N ≅ (K.map E).homology) :
    let α := ((K.map E).mapHomologyIso G).hom ≫ G.map j.inv
    let β := (K.mapHomologyIso F).hom ≫ F.map i.inv
    let γ := j.hom ≫ (K.mapHomologyIso E).hom ≫ E.map i.inv
    α ≫ G.map γ ≫ η.inv.app M =
      ShortComplex.homologyMap (K.mapNatTrans η.inv) ≫ ((K.map F).mapHomologyIso H).hom ≫ H.map β := by
  dsimp only
  simp only [Category.assoc]
  rw [← G.map_comp_assoc, Iso.inv_hom_id_assoc, G.map_comp, Category.assoc]
  change ((K.map E).mapHomologyIso G).hom ≫ G.map (K.mapHomologyIso E).hom ≫
      (E ⋙ G).map i.inv ≫ η.inv.app M = _
  rw [η.inv.naturality, ← reassoc_of% (mapHomologyIso_comp_hom K E G)]
  rw [η.inv.app_homology K]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, mapHomologyIso_comp_hom K F H, H.map_comp]
  rfl

end ExactLift

/-- Coefficient lift of the local presheaf, defined on the same augmented model. -/
def localPresheafCarrierIso (q : ℕ) :
    (P).obj ((localCohomology.{u,r,a} R q).obj M) ≅
      (localCohomology.{u,r,max a b} R q).obj ((L).obj M) :=
  let K := underlyingComplex.{u,r,a} R J.cocomplex
  let J' := carrierLiftResolution.{u,r,a,b} R J
  (P).mapIso (J.isoRightDerivedObj (SheafOfModules.forget R) q) ≪≫
    ((K.sc q).mapHomologyIso P).symm ≪≫
    (J'.isoRightDerivedObj (SheafOfModules.forget R) q).symm

/-- Transport of the alternating local cohomology cochains uses the original tuple product. -/
def localCochainCarrierIso (q : ℕ) :
    cochainComplex.{u,r,max a b,v} R c ((localCohomology.{u,r,max a b} R q).obj ((L).obj M)) ≅
      ((S).mapHomologicalComplex (.up ℕ)).obj
        (cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)) :=
  (cochainFunctor.{u,r,max a b,v} R c).mapIso (localPresheafCarrierIso.{u,r,a,b} R J q).symm ≪≫
    ((cochainLiftNatIso.{u,r,a,v,b} R c).app ((localCohomology.{u,r,a} R q).obj M)).symm

private def localIntCochainCarrierIso (q : ℕ) :
    localCechComplexInt.{u,r,max a b,v} R c ((L).obj M) q ≅
      ((S).mapHomologicalComplex (.up ℤ)).obj (localCechComplexInt.{u,r,a,v} R c M q) :=
  (embedding.extendFunctor _).mapIso (localCochainCarrierIso.{u,r,a,v,b} R c J q) ≪≫
    (mapExtendIso S _ embedding).symm

private lemma localIntCochainCarrierIso_f (p q : ℕ) :
    let h : embedding.f p = (p : ℤ) := by simp [embedding]
    let C := cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)
    let C' := cochainComplex.{u,r,max a b,v} R c ((localCohomology.{u,r,max a b} R q).obj ((L).obj M))
    (localIntCochainCarrierIso.{u,r,a,v,b} R c J q).hom.f (p : ℤ) ≫
      (S).map (C.extendXIso embedding h).hom =
      (C'.extendXIso embedding h).hom ≫ (localCochainCarrierIso.{u,r,a,v,b} R c J q).hom.f p := by
  let h : embedding.f p = (p : ℤ) := by simp [embedding]
  let C := cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)
  let w := localCochainCarrierIso.{u,r,a,v,b} R c J q
  let e := mapExtendIso S C embedding
  dsimp only [localIntCochainCarrierIso, Iso.trans_hom, Iso.symm_hom, HomologicalComplex.comp_f]
  change ((HomologicalComplex.extendMap w.hom embedding).f (p : ℤ) ≫ e.inv.f (p : ℤ)) ≫ _ = _
  rw [Category.assoc, HomologicalComplex.extendMap_f w.hom embedding h]
  have he : e.inv.f (p : ℤ) ≫ (S).map (C.extendXIso embedding h).hom =
      ((((S).mapHomologicalComplex (.up ℕ)).obj C).extendXIso embedding h).hom := by
    rw [← mapExtendIso_hom_f S C embedding h, ← Category.assoc]
    simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.id_comp] using
      congrArg (fun f ↦ f ≫ ((((S).mapHomologicalComplex (.up ℕ)).obj C).extendXIso embedding h).hom)
        (HomologicalComplex.congr_hom e.inv_hom_id (p : ℤ))
  rw [he]
  let z := ((((S).mapHomologicalComplex (.up ℕ)).obj C).extendXIso embedding h)
  change _ ≫ _ ≫ z.inv ≫ z.hom = _
  simp only [Iso.inv_hom_id, Category.comp_id]
  rfl

private lemma verticalCarrier_nat (p q : ℕ) :
    let J' := carrierLiftResolution.{u,r,a,b} R J
    let F := cochainFunctor.{u,r,a,v} R c ⋙ HomologicalComplex.eval _ (.up ℕ) p
    let G := cochainFunctor.{u,r,max a b,v} R c ⋙ HomologicalComplex.eval _ (.up ℕ) p
    let K := underlyingComplex.{u,r,a} R J.cocomplex
    let K' := underlyingComplex.{u,r,max a b} R J'.cocomplex
    let a := ((K.sc q).mapHomologyIso F).hom ≫ F.map (J.isoRightDerivedObj (SheafOfModules.forget R) q).inv
    let b := ((K'.sc q).mapHomologyIso G).hom ≫ G.map (J'.isoRightDerivedObj (SheafOfModules.forget R) q).inv
    let e := (doubleCarrierIso.{u,r,a,v,b} R c J.cocomplex).hom.f p
    (b ≫ (localCochainCarrierIso.{u,r,a,v,b} R c J q).hom.f p) =
      homologyMap e q ≫ ((((doubleComplex.{u,r,a,v} R c J.cocomplex).X p).sc q).mapHomologyIso S).hom ≫ (S).map a := by
  let J' := carrierLiftResolution.{u,r,a,b} R J
  let F := cochainFunctor.{u,r,a,v} R c ⋙ HomologicalComplex.eval _ (.up ℕ) p
  let G := cochainFunctor.{u,r,max a b,v} R c ⋙ HomologicalComplex.eval _ (.up ℕ) p
  let K := underlyingComplex.{u,r,a} R J.cocomplex
  let η : F ⋙ S ≅ P ⋙ G :=
    isoWhiskerRight (cochainLiftNatIso.{u,r,a,v,b} R c) (HomologicalComplex.eval _ (.up ℕ) p)
  dsimp only
  simp only [localCochainCarrierIso, localPresheafCarrierIso, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.trans_inv, Functor.mapIso_inv, HomologicalComplex.comp_f,
    Category.assoc]
  exact ExactLift.homology_comparison P F G S (K.sc q) η
    (J.isoRightDerivedObj (SheafOfModules.forget R) q)
    (J'.isoRightDerivedObj (SheafOfModules.forget R) q)

private lemma verticalIso_coefficientCarrier (q : ℕ) :
    let J' := carrierLiftResolution.{u,r,a,b} R J
    (verticalHomologyTransportIso S (doubleCarrierIntIso.{u,r,a,v,b} R c J.cocomplex) (q : ℤ)).hom ≫
        ((S).mapHomologicalComplex (.up ℤ)).map (verticalIso.{u,r,a,v} R c J q).hom =
      (verticalIso.{u,r,max a b,v} R c J' q).hom ≫
        (localIntCochainCarrierIso.{u,r,a,v,b} R c J q).hom := by
  dsimp only
  let J' := carrierLiftResolution.{u,r,a,b} R J
  let K := doubleComplex.{u,r,max a b,v} R c J'.cocomplex
  let L₀ := doubleComplex.{u,r,a,v} R c J.cocomplex
  let C := localCechComplexInt.{u,r,a,v} R c M q
  let v := verticalIso.{u,r,max a b,v} R c J' q
  let w := verticalIso.{u,r,a,v} R c J q
  let u := localIntCochainCarrierIso.{u,r,a,v,b} R c J q
  apply HomologicalComplex.hom_ext
  intro p
  by_cases hp : 0 ≤ p
  · let n := p.toNat
    have hn : (n : ℤ) = p := Int.toNat_of_nonneg hp
    rw [← hn]
    let Q := cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)
    let e := (Q.extendXIso embedding (by simp [embedding] :
      embedding.f n = (n : ℤ))).hom
    apply (cancel_mono ((S).map e)).1
    let E := doubleCarrierIntIso.{u,r,a,v,b} R c J.cocomplex
    let z := verticalHomologyTransportIso S E (q : ℤ)
    let rk := (verticalComponent.{u,r,a,v} R c J n q).hom
    let ok := (verticalComponent.{u,r,max a b,v} R c J' n q).hom
    let f := (localCochainCarrierIso.{u,r,a,v,b} R c J q).hom.f n
    have hv : v.hom.f (n : ℤ) ≫ _ = ok :=
      verticalIso_component.{u,r,max a b,v} R c J' n q
    have hw : w.hom.f (n : ℤ) ≫ e = rk :=
      verticalIso_component.{u,r,a,v} R c J n q
    have hu := localIntCochainCarrierIso_f.{u,r,a,v,b} R c J n q
    change (z.hom.f (n : ℤ) ≫ (S).map (w.hom.f (n : ℤ))) ≫ (S).map e =
      (v.hom.f (n : ℤ) ≫ u.hom.f (n : ℤ)) ≫ (S).map e
    rw [Category.assoc, ← (S).map_comp, hw, Category.assoc, hu, ← Category.assoc (v.hom.f (n : ℤ)), hv]
    let ek := extendedColumnIso K n
    let el := extendedColumnIso L₀ n
    have hcol := comparedBicomplexColumn S (doubleCarrierIso.{u,r,a,v,b} R c J.cocomplex) n
    have hcomp := compareExtendedHomology S ek el ((doubleCarrierIso.{u,r,a,v,b} R c J.cocomplex).hom.f n)
      (E.hom.f (n : ℤ)) hcol q
    let Z := underlyingComplex.{u,r,max a b} R J'.cocomplex
    let Z' := underlyingComplex.{u,r,a} R J.cocomplex
    let G := cochainFunctor.{u,r,a,v} R c ⋙ HomologicalComplex.eval _ (.up ℕ) n
    let F := cochainFunctor.{u,r,max a b,v} R c ⋙ HomologicalComplex.eval _ (.up ℕ) n
    let a := ((Z.sc q).mapHomologyIso F).hom ≫ F.map (J'.isoRightDerivedObj (SheafOfModules.forget R) q).inv
    let b := ((Z'.sc q).mapHomologyIso G).hom ≫ G.map (J.isoRightDerivedObj (SheafOfModules.forget R) q).inv
    let hq : embedding.f q = (q : ℤ) := by simp [embedding]
    let k := homologyMap ek.hom (q : ℤ) ≫ ((K.X n).extendHomologyIso embedding hq).hom
    let l := homologyMap el.hom (q : ℤ) ≫ ((L₀.X n).extendHomologyIso embedding hq).hom
    let g := homologyMap ((doubleCarrierIso.{u,r,a,v,b} R c J.cocomplex).hom.f n) q ≫
      (((L₀.X n).sc q).mapHomologyIso S).hom
    have ht : g ≫ (S).map b = a ≫ f := (verticalCarrier_nat.{u,r,a,v,b} R c J n q).symm
    have hx : z.hom.f (n : ℤ) ≫ (S).map l = k ≫ g := by
      dsimp only [z, verticalHomologyTransportIso, HomologicalComplex.Hom.isoOfComponents_hom_f,
        transportedHomology, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom, asIso_hom]
      simpa only [k, g, Category.assoc] using hcomp
    have hL : rk = l ≫ b := by
      simp only [rk, l, b, verticalComponent, Iso.trans_hom, Functor.mapIso_hom,
        HomologicalComplex.homologyMapIso_hom, Category.assoc]
      rfl
    have hK : ok = k ≫ a := by
      simp only [ok, k, a, verticalComponent, Iso.trans_hom, Functor.mapIso_hom,
        HomologicalComplex.homologyMapIso_hom, Category.assoc]
      rfl
    rw [hL, hK, (S).map_comp, ← Category.assoc, hx, Category.assoc, ht, Category.assoc]
    change k ≫ a ≫ f = (k ≫ a) ≫ f
    exact (Category.assoc _ _ _).symm
  · have hC : IsZero ((localCechComplexInt.{u,r,max a b,v} R c ((L).obj M) q).X p) := HomologicalComplex.isZero_extend_X _ embedding _ (fun n h ↦ by
      have hs : embedding.f n = (n : ℤ) := by simp [embedding]
      rw [hs] at h
      omega)
    have h0 := hC.of_iso ((HomologicalComplex.eval _ (.up ℤ) p).mapIso v)
    exact h0.eq_of_src _ _


/-- Cohomology of the alternating restriction complex, with the canonical lift
of its module carrier. -/
def localCechCarrierIso (p q : ℕ) :
    (localCechCohomology.{u,r,max a b,v} R c p q).obj ((L).obj M) ≅
      (S).obj ((localCechCohomology.{u,r,a,v} R c p q).obj M) :=
  let C := cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)
  homologyMapIso (localCochainCarrierIso.{u,r,a,v,b} R c J q) p ≪≫ (C.sc p).mapHomologyIso S

private lemma localCechCarrierIso_extend (p q : ℕ) :
    let C := cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)
    let C' := cochainComplex.{u,r,max a b,v} R c ((localCohomology.{u,r,max a b} R q).obj ((L).obj M))
    let hp : embedding.f p = (p : ℤ) := by simp [embedding]
    (transportedHomology S (localIntCochainCarrierIso.{u,r,a,v,b} R c J q) (p : ℤ)).hom ≫
      (S).map (C.extendHomologyIso embedding hp).hom =
      (C'.extendHomologyIso embedding hp).hom ≫ (localCechCarrierIso.{u,r,a,v,b} R c J p q).hom := by
  let C := cochainComplex.{u,r,a,v} R c ((localCohomology.{u,r,a} R q).obj M)
  let C' := cochainComplex.{u,r,max a b,v} R c ((localCohomology.{u,r,max a b} R q).obj ((L).obj M))
  let w := localCochainCarrierIso.{u,r,a,v,b} R c J q
  let e := mapExtendIso S C embedding
  let v := localIntCochainCarrierIso.{u,r,a,v,b} R c J q
  have h : v.hom ≫ ((S).mapHomologicalComplex (.up ℤ)).map (Iso.refl (C.extend embedding)).hom ≫ e.hom =
      (Iso.refl (C'.extend embedding)).hom ≫ HomologicalComplex.extendMap w.hom embedding := by
    change ((HomologicalComplex.extendMap w.hom embedding) ≫ e.inv) ≫
      ((S).mapHomologicalComplex (.up ℤ)).map (𝟙 _) ≫ e.hom = 𝟙 _ ≫ _
    rw [((S).mapHomologicalComplex (.up ℤ)).map_id]
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h' := compareExtendedHomology S (Iso.refl (C'.extend embedding))
    (Iso.refl (C.extend embedding)) w.hom v.hom h p
  simp only [Iso.refl_hom, HomologicalComplex.homologyMap_id, Category.id_comp] at h'
  exact h'

set_option maxHeartbeats 2500000 in
lemma secondPageComparison_carrier (p q : ℕ) :
    let J' := carrierLiftResolution.{u,r,a,b} R J
    let D := spectralData.{u,r,max a b,v} R c J'
    let E := spectralData.{u,r,a,v} R c J
    let h := signedTotalCarrierIso_filtration.{u,r,a,v,b} R c J.cocomplex D E
    let t := signedTotalCarrierIso.{u,r,a,v,b} R c J.cocomplex
    let θ := pageTransportIso S D.filtration E.filtration t h D.pages E.pages
      2 (by omega) (p : ℤ) ((p : ℤ) + (q : ℤ))
    θ.hom ≫ (S).map (secondPageComparison.{u,r,a,v} R c J E (verticalIso.{u,r,a,v} R c J) p q).hom =
      (secondPageComparison.{u,r,max a b,v} R c J' D (verticalIso.{u,r,max a b,v} R c J') p q).hom ≫
        (localCechCarrierIso.{u,r,a,v,b} R c J p q).hom := by
  let J' := carrierLiftResolution.{u,r,a,b} R J
  let D := spectralData.{u,r,max a b,v} R c J'
  let E := spectralData.{u,r,a,v} R c J
  let h := signedTotalCarrierIso_filtration.{u,r,a,v,b} R c J.cocomplex D E
  let t := signedTotalCarrierIso.{u,r,a,v,b} R c J.cocomplex
  let e := doubleCarrierIntIso.{u,r,a,v,b} R c J.cocomplex
  let z := verticalHomologyTransportIso S e (q : ℤ)
  let w := localIntCochainCarrierIso.{u,r,a,v,b} R c J q
  let v := verticalIso.{u,r,max a b,v} R c J' q
  let v' := verticalIso.{u,r,a,v} R c J q
  have hc := columnSecondIso_transport S D E e t h
    (signedTotalCarrierIso_injection.{u,r,a,v,b} R c J.cocomplex) (p : ℤ) (q : ℤ)
  have hv := transportedHomology_natural S z w v.hom v'.hom
    (verticalIso_coefficientCarrier.{u,r,a,v,b} R c J q).symm (p : ℤ)
  have he := localCechCarrierIso_extend.{u,r,a,v,b} R c J p q
  dsimp only [secondPageComparison, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom]
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, specifiedColumnSecondIso_eq E, hc,
    Category.assoc, ← Category.assoc ((columnSecondPageIso D (p : ℤ) (q : ℤ)).hom),
    Category.assoc, ← Category.assoc (transportedHomology S z (p : ℤ)).hom]
  change (columnSecondPageIso D (p : ℤ) (q : ℤ)).hom ≫
      ((transportedHomology S z (p : ℤ)).hom ≫ (S).map (homologyMap v'.hom (p : ℤ))) ≫ _ = _
  rw [← hv, specifiedColumnSecondIso_eq D]
  simp only [Category.assoc]
  rw [he]

end CarrierLocalCohomology

section CarrierSections

open HomologicalComplex
open CechToCohomology (mapExtendIso mapHomologyIso_comp_hom abutmentPiece)

set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cochainCarrierLift.{u,r,a,v,b} R c
set_option quotPrecheck false in
set_option hygiene false in
local notation "L" => sheafCarrierLift.{u,r,a,b} R
set_option quotPrecheck false in
set_option hygiene false in
local notation "P" => presheafCarrierLift.{u,r,a,b} R

variable [EnoughInjectives (AmbientSheaves.{max a b} R)]
variable {M : AmbientSheaves.{a} R} (J : InjectiveResolution M)

/-- The section module comparison is normalized by the actual derived-unit
maps of the two resolutions on each original open. -/
def sectionDerivedCarrierIso (V : Opens X) (n : ℕ) :
    (cohomologyValue.{max a b,u,r} R V n).obj ((L).obj M) ≅
      (ModuleCat.uliftFunctor.{b,max a u r} (sectionRing R V)).obj
        ((cohomologyValue.{a,u,r} R V n).obj M) :=
  let H := ModuleCat.uliftFunctor.{b,max a u r} (sectionRing R V)
  let K := sectionComplex.{u,r,a} R V J.cocomplex
  let J' := carrierLiftResolution.{u,r,a,b} R J
  (asIso (sectionModelMap.{u,r,max a b} R V J' n)).symm ≪≫
    (K.sc n).mapHomologyIso H ≪≫ H.mapIso (asIso (sectionModelMap.{u,r,a} R V J n))

lemma localPresheafCarrierIso_sections (V : Opens X) (q : ℕ) :
    let H := ModuleCat.uliftFunctor.{b,max a u r} (sectionRing R V)
    let E := PresheafOfModules.evaluation.{max a b u r} R.obj (op V)
    let J' := carrierLiftResolution.{u,r,a,b} R J
    E.map (localPresheafCarrierIso.{u,r,a,b} R J q).inv ≫
      H.map ((originalLocalSectionsIso.{u,r,a} R V q).hom.app M) =
    (originalLocalSectionsIso.{u,r,max a b} R V q).hom.app ((L).obj M) ≫
      (sectionDerivedCarrierIso.{u,r,a,b} R J V q).hom := by
  let H := ModuleCat.uliftFunctor.{b,max a u r} (sectionRing R V)
  let E := PresheafOfModules.evaluation.{max a b u r} R.obj (op V)
  let F := PresheafOfModules.evaluation.{max a u r} R.obj (op V)
  let J' := carrierLiftResolution.{u,r,a,b} R J
  let K := underlyingComplex.{u,r,a} R J.cocomplex
  let K' := underlyingComplex.{u,r,max a b} R J'.cocomplex
  let i := J.isoRightDerivedObj (SheafOfModules.forget R) q
  let j := J'.isoRightDerivedObj (SheafOfModules.forget R) q
  let η : F ⋙ H ≅ P ⋙ E := Iso.refl _
  let α := ((K'.sc q).mapHomologyIso E).hom ≫ E.map j.inv
  let β := ((K.sc q).mapHomologyIso F).hom ≫ F.map i.inv
  have hb : β ≫ (originalLocalSectionsIso.{u,r,a} R V q).hom.app M =
      sectionModelMap.{u,r,a} R V J q := by
    rw [originalLocalSectionsIso_model.{u,r,a} R V q J]
    dsimp only [β, localEvaluationIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    let w := (K.sc q).mapHomologyIso F
    simp only [Category.assoc]
    change w.hom ≫ F.map i.inv ≫ F.map i.hom ≫ w.inv ≫ _ = _
    rw [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp, Iso.hom_inv_id_assoc]
  have ha : α ≫ (originalLocalSectionsIso.{u,r,max a b} R V q).hom.app ((L).obj M) =
      sectionModelMap.{u,r,max a b} R V J' q := by
    rw [originalLocalSectionsIso_model.{u,r,max a b} R V q J']
    dsimp only [α, localEvaluationIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    let w := (K'.sc q).mapHomologyIso E
    simp only [Category.assoc]
    change w.hom ≫ E.map j.inv ≫ E.map j.hom ≫ w.inv ≫ _ = _
    rw [← E.map_comp_assoc, Iso.inv_hom_id, E.map_id, Category.id_comp, Iso.hom_inv_id_assoc]
  let _ : IsIso α := by dsimp only [α]; infer_instance
  have h := ExactLift.homology_comparison P F E H (K.sc q) η i j
  have h' : α ≫ E.map (localPresheafCarrierIso.{u,r,a,b} R J q).inv =
      (((sectionComplex.{u,r,a} R V J.cocomplex).sc q).mapHomologyIso H).hom ≫ H.map β := by
    have hid : (K.sc q).mapNatTrans η.inv = 𝟙 _ := by
      ext <;> rfl
    simp only [hid, ShortComplex.homologyMap_id] at h
    change α ≫ E.map (j.hom ≫ ((K.sc q).mapHomologyIso P).hom ≫ (P).map i.inv) ≫ 𝟙 _ =
      𝟙 _ ≫ (((sectionComplex.{u,r,a} R V J.cocomplex).sc q).mapHomologyIso H).hom ≫ H.map β at h
    rw [Category.comp_id, Category.id_comp] at h
    simpa only [localPresheafCarrierIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      Category.assoc] using h
  apply (cancel_epi α).1
  rw [← Category.assoc, ← Category.assoc, h', ha]
  simp only [sectionDerivedCarrierIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
    Functor.mapIso_hom, Category.assoc]
  let w := (((sectionComplex.{u,r,a} R V J.cocomplex).sc q).mapHomologyIso H).hom
  let g := (originalLocalSectionsIso.{u,r,a} R V q).hom.app M
  let s := sectionModelMap.{u,r,max a b} R V J' q
  change w ≫ H.map β ≫ H.map g = s ≫ inv s ≫ w ≫ H.map (sectionModelMap.{u,r,a} R V J q)
  rw [← H.map_comp, hb, IsIso.hom_inv_id_assoc]

/-- The target comparison in the cover universe, over the same section ring. -/
def abutmentTargetCarrierIso (n : ℕ) :
    (sectionLift.{u,r,max a b,v} R c).obj ((cohomologyValue.{max a b,u,r} R U n).obj ((L).obj M)) ≅
      (S).obj ((sectionLift.{u,r,a,v} R c).obj ((cohomologyValue.{a,u,r} R U n).obj M)) :=
  (sectionLift.{u,r,max a b,v} R c).mapIso (sectionDerivedCarrierIso.{u,r,a,b} R J U n) ≪≫
    (sectionLiftsIso.{u,r,a,v,b} R U).app _

private lemma liftedSectionCarrier_natHomology (n : ℕ) :
    let J' := carrierLiftResolution.{u,r,a,b} R J
    let C := sectionComplex.{u,r,a} R U J.cocomplex
    let C' := sectionComplex.{u,r,max a b} R U J'.cocomplex
    let F := sectionLift.{u,r,a,v} R c
    let F' := sectionLift.{u,r,max a b,v} R c
    let Y := liftedSections.{u,r,a,v} R c J.cocomplex
    homologyMap (liftedSectionCarrierIso.{u,r,a,v,b} R c J.cocomplex).hom n ≫
        ((Y.sc n).mapHomologyIso S).hom ≫ (S).map
          (((C.sc n).mapHomologyIso F).hom ≫ F.map (sectionModelMap.{u,r,a} R U J n)) =
      ((C'.sc n).mapHomologyIso F').hom ≫ F'.map (sectionModelMap.{u,r,max a b} R U J' n) ≫
        (abutmentTargetCarrierIso.{u,r,a,v,b} R c J n).hom := by
  let J' := carrierLiftResolution.{u,r,a,b} R J
  let C := sectionComplex.{u,r,a} R U J.cocomplex
  let F := sectionLift.{u,r,a,v} R c
  let F' := sectionLift.{u,r,max a b,v} R c
  let H := ModuleCat.uliftFunctor.{b,max a u r} (sectionRing R U)
  let η := sectionLiftsIso.{u,r,a,v,b} R U
  let a := sectionModelMap.{u,r,a} R U J n
  let a' := sectionModelMap.{u,r,max a b} R U J' n
  have h : homologyMap (liftedSectionCarrierIso.{u,r,a,v,b} R c J.cocomplex).hom n =
      ShortComplex.homologyMap ((C.sc n).mapNatTrans η.hom) := rfl
  change _ ≫ (((C.sc n).map F).mapHomologyIso S).hom ≫ (S).map
      (((C.sc n).mapHomologyIso F).hom ≫ F.map a) =
    (((C.sc n).map H).mapHomologyIso F').hom ≫ F'.map a' ≫ _
  rw [h, (S).map_comp, ← reassoc_of% (mapHomologyIso_comp_hom (C.sc n) F S)]
  have ht : ((C.sc n).mapHomologyIso (H ⋙ F')).hom ≫ η.hom.app (C.sc n).homology =
      ShortComplex.homologyMap ((C.sc n).mapNatTrans η.hom) ≫
        ((C.sc n).mapHomologyIso (F ⋙ S)).hom := by
    rw [η.hom.app_homology, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% ht, mapHomologyIso_comp_hom (C.sc n) H F']
  simp only [abutmentTargetCarrierIso, sectionDerivedCarrierIso, Functor.mapIso_hom,
    Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom, F'.map_comp, Category.assoc]
  rw [← F'.map_comp_assoc]
  let w := (((C.sc n).map H).mapHomologyIso F').hom
  let k := ((C.sc n).mapHomologyIso H).hom
  change w ≫ F'.map k ≫ η.hom.app _ ≫ (F ⋙ S).map a =
    w ≫ F'.map (a' ≫ inv a' ≫ k ≫ H.map a) ≫ η.hom.app _
  rw [IsIso.hom_inv_id_assoc, F'.map_comp, Category.assoc]
  exact congrArg (fun f ↦ w ≫ F'.map k ≫ f) (η.hom.naturality a).symm

lemma liftedSectionModelMap_carrier (n : ℕ) :
    let J' := carrierLiftResolution.{u,r,a,b} R J
    (transportedHomology S (intSectionCarrierIso.{u,r,a,v,b} R c J.cocomplex) (n : ℤ)).hom ≫
      (S).map (liftedSectionModelMap.{u,r,a,v} R c J n) =
    liftedSectionModelMap.{u,r,max a b,v} R c J' n ≫
      (abutmentTargetCarrierIso.{u,r,a,v,b} R c J n).hom := by
  let J' := carrierLiftResolution.{u,r,a,b} R J
  let Y := liftedSections.{u,r,a,v} R c J.cocomplex
  let Y' := liftedSections.{u,r,max a b,v} R c J'.cocomplex
  let e := liftedSectionCarrierIso.{u,r,a,v,b} R c J.cocomplex
  let r := intSectionCarrierIso.{u,r,a,v,b} R c J.cocomplex
  let t := mapExtendIso S Y embedding
  let hp : embedding.f n = (n : ℤ) := by simp [embedding]
  have h : r.hom ≫ ((S).mapHomologicalComplex (.up ℤ)).map (Iso.refl (Y.extend embedding)).hom ≫ t.hom =
      (Iso.refl (Y'.extend embedding)).hom ≫ extendMap e.hom embedding := by
    change (extendMap e.hom embedding ≫ t.inv) ≫
      ((S).mapHomologicalComplex (.up ℤ)).map (𝟙 _) ≫ t.hom = 𝟙 _ ≫ _
    rw [((S).mapHomologicalComplex (.up ℤ)).map_id]
    simp only [Category.id_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have he : homologyMap r.hom (n : ℤ) ≫ (((Y.extend embedding).sc (n : ℤ)).mapHomologyIso S).hom ≫
      (S).map (Y.extendHomologyIso embedding hp).hom =
      (Y'.extendHomologyIso embedding hp).hom ≫ homologyMap e.hom n ≫ ((Y.sc n).mapHomologyIso S).hom := by
    have hi : 𝟙 ((Y.extend embedding).homology (n : ℤ)) ≫
        (Y.extendHomologyIso embedding hp).hom = (Y.extendHomologyIso embedding hp).hom := Category.id_comp _
    simpa only [Iso.refl_hom, homologyMap_id, Category.id_comp, hi] using
      compareExtendedHomology S (Iso.refl (Y'.extend embedding))
        (Iso.refl (Y.extend embedding)) e.hom r.hom h n
  have hn := liftedSectionCarrier_natHomology.{u,r,a,v,b} R c J n
  dsimp only [transportedHomology, Iso.trans_hom, homologyMapIso_hom, liftedSectionModelMap]
  change (_ ≫ _) ≫ (S).map ((Y.extendHomologyIso embedding hp).hom ≫ _) = _ ≫ _
  rw [(S).map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% he, hn]

lemma abutmentIso_carrier (n : ℕ) :
    let J' := carrierLiftResolution.{u,r,a,b} R J
    (transportedHomology S (signedTotalCarrierIso.{u,r,a,v,b} R c J.cocomplex) (n : ℤ)).hom ≫
        (S).map (abutmentIso.{u,r,a,v} R c J n).hom =
      (abutmentIso.{u,r,max a b,v} R c J' n).hom ≫ (abutmentTargetCarrierIso.{u,r,a,v,b} R c J n).hom := by
  let J' := carrierLiftResolution.{u,r,a,b} R J
  let x := totalAugmentationMap.{u,r,max a b,v} R c J'
  let y := totalAugmentationMap.{u,r,a,v} R c J
  let t := signedTotalCarrierIso.{u,r,a,v,b} R c J.cocomplex
  let e := intSectionCarrierIso.{u,r,a,v,b} R c J.cocomplex
  have h := transportedHomology_natural S e t x y
    (totalAugmentationMap_carrier.{u,r,a,v,b} R c J) (n : ℤ)
  dsimp only
  apply (cancel_epi (homologyMap x (n : ℤ))).1
  rw [← Category.assoc, h]
  have hx : homologyMap x (n : ℤ) ≫ (abutmentIso.{u,r,max a b,v} R c J' n).hom =
      liftedSectionModelMap.{u,r,max a b,v} R c J' n := by
    simp [abutmentIso, x]
  have hy : homologyMap y (n : ℤ) ≫ (abutmentIso.{u,r,a,v} R c J n).hom =
      liftedSectionModelMap.{u,r,a,v} R c J n := by
    simp [abutmentIso, y]
  rw [Category.assoc, ← (S).map_comp, hy, ← Category.assoc, hx]
  exact liftedSectionModelMap_carrier.{u,r,a,v,b} R c J n

end CarrierSections

section LimitingCarrierPages

open _root_.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients (limitClass limitQuotient)
open CechToCohomology (columnAbutmentLimitIso columnAbutmentLimitIso_representative)
open FiniteDiagonalFiltrations
open FiniteFiltrationConvergence (closedToPage closedToPage_epi closed_le_almost Stabilized)
open FilteredPage (almost toPage)

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [SubobjectComparison G]
  {K : Bicomplex D} {L : Bicomplex C} [K.HasTotal (.up ℤ)] [(L).HasTotal (.up ℤ)]
  (DK : ColumnSpectralData K) (DL : ColumnSpectralData L)
  (e : sumTotal K ≅ (G.mapHomologicalComplex (.up ℤ)).obj (sumTotal L))
  (he : ∀ p n : ℤ,
    Subobject.mk ((DK.filtration.piece p n).arrow ≫ e.hom.f n) =
      Subobject.mk (G.map (DL.filtration.piece p n).arrow))

private lemma pageTransportIso_closed (r : ℤ) (hr : 1 ≤ r) (p n : ℤ) :
    closedToPage DK.filtration DK.pages r p n ≫
        (pageTransportIso G DK.filtration DL.filtration e he DK.pages DL.pages r hr p n).hom =
      (transportedClosed G DK.filtration DL.filtration e he p n).hom ≫
        G.map (closedToPage DL.filtration DL.pages r p n) := by
  let a := almostCycleTransportIso G DK.filtration DL.filtration e he r p n
  let z := transportedClosed G DK.filtration DL.filtration e he p n
  have h : Subobject.ofLE _ _ (closed_le_almost DK.filtration r p n) ≫ a.hom =
      z.hom ≫ G.map (Subobject.ofLE _ _ (closed_le_almost DL.filtration r p n)) := by
    apply (cancel_mono (G.map (almost DL.filtration r p n).arrow)).1
    dsimp only [a, z]
    rw [Category.assoc, almostCycleTransportIso_arrow, ← Category.assoc, Subobject.ofLE_arrow,
      Category.assoc, ← G.map_comp, Subobject.ofLE_arrow, transportedClosed_arrow]
  dsimp only [closedToPage]
  rw [Category.assoc, pageTransportIso_representative, ← Category.assoc, h,
    Category.assoc, ← G.map_comp]

private lemma pageTransportIso_limit (r : ℤ) (hr : 1 ≤ r) (p n : ℤ)
    {H : D} {J : C} (a : (sumTotal K).homology n ≅ H) (b : (sumTotal L).homology n ≅ J)
    (hs : Stabilized DK.filtration r p n) (ht : Stabilized DL.filtration r p n) :
    (pageTransportIso G DK.filtration DL.filtration e he DK.pages DL.pages r hr p n).hom ≫
        G.map (columnAbutmentLimitIso DL n b r p ht).hom =
      (columnAbutmentLimitIso DK n a r p hs).hom ≫
        (transportedAbutmentGraded G DK.filtration DL.filtration e he n a b p).hom := by
  let _ := closedToPage_epi DK.filtration DK.pages r p n hs.1
  apply (cancel_epi (closedToPage DK.filtration DK.pages r p n)).1
  rw [← Category.assoc, pageTransportIso_closed, Category.assoc, ← G.map_comp,
    columnAbutmentLimitIso_representative DL n b r p ht, reassoc_of% (columnAbutmentLimitIso_representative DK n a r p hs)]
  simpa only [limitClass, Category.assoc] using
    (transportedLimitClass G DK.filtration DL.filtration e he n a b p).symm

end LimitingCarrierPages

section CoefficientSizeTransport

open _root_.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
  (CarrierModelComparison coefficientSizeTransport)

set_option quotPrecheck false in
set_option hygiene false in
local notation "S" => cochainCarrierLift.{u,r,a,v,b} R c

variable [EnoughInjectives (AmbientSheaves.{max a b} R)]

set_option maxHeartbeats 8000000 in
/-- All comparison maps use the same tuple comparison and the image of the same augmented model. -/
def carrierModelComparison {M : AmbientSheaves.{a} R} (I : InjectiveResolution M) :
    CarrierModelComparison.{u,r,a,v,b} R c
      (coefficientNaturalityData.{u,r,a,v} R c) (coefficientNaturalityData.{u,r,max a b,v} R c) I := by
  let K := I.cocomplex
  let I' := carrierLiftResolution.{u,r,a,b} R I
  let D := spectralData.{u,r,a,v} R c I
  let E := spectralData.{u,r,max a b,v} R c I'
  let t := signedTotalCarrierIso.{u,r,a,v,b} R c K
  let h := signedTotalCarrierIso_filtration.{u,r,a,v,b} R c K E D
  refine {
    double := doubleCarrierIntIso.{u,r,a,v,b} R c K
    double_formula := doubleCarrierIntIso_apply.{u,r,a,v,b} R c K
    total := t
    total_formula := signedTotalCarrierIso_injection.{u,r,a,v,b} R c K
    filtration := h
    sections := intSectionCarrierIso.{u,r,a,v,b} R c K
    augmentation := totalAugmentationMap_carrier.{u,r,a,v,b} R c I
    localPresheaf := localPresheafCarrierIso.{u,r,a,b} R I
    local_formula := fun _ ↦ rfl
    localTuples := fun F ↦ ((cochainLiftNatIso.{u,r,a,v,b} R c).app F).symm
    localTuples_formula := fun _ _ _ ↦ rfl
    verticalAugmentation_formula := ⟨doubleCarrierIso.{u,r,a,v,b} R c K,
      fun _ _ _ ↦ rfl, verticalAugmentation_carrier.{u,r,a,v,b} R c I⟩
    pages := pageTransportIso S E.filtration D.filtration t h E.pages D.pages
    representatives := fun r hr p n ↦ ⟨
      almostCycleTransportIso S E.filtration D.filtration t h r p n,
      almostCycleTransportIso_arrow S E.filtration D.filtration t h r p n,
      pageTransportIso_representative S E.filtration D.filtration t h E.pages D.pages r hr p n⟩
    differential := pageTransportIso_differential S E.filtration D.filtration t h E.pages D.pages
    second := secondPageComparison_carrier.{u,r,a,v,b} R c I
    sectionComparison := sectionDerivedCarrierIso.{u,r,a,b} R I
    section_model := ?_
    local_sections := ?_
    target := abutmentTargetCarrierIso.{u,r,a,v,b} R c I
    target_sections := fun _ _ ↦ rfl
    target_formula := abutmentIso_carrier.{u,r,a,v,b} R c I
    limits := limiting_transport S E.filtration D.filtration t h E.pages D.pages
    limit_pages := ?_ }
  · dsimp only
    intro V n
    simp only [sectionDerivedCarrierIso, Iso.trans_hom, Iso.symm_hom, asIso_inv, asIso_hom,
      Functor.mapIso_hom, Category.assoc, IsIso.hom_inv_id_assoc]
  · dsimp only
    intro V n
    have hn := localPresheafCarrierIso_sections.{u,r,a,b} R I V n
    dsimp only at hn ⊢
    rw [originalLocalSectionsIso_model.{u,r,a} R V n I,
      originalLocalSectionsIso_model.{u,r,max a b} R V n I'] at hn
    simpa only [Category.assoc] using hn
  · dsimp only
    intro n p
    let e := abutmentIso.{u,r,max a b,v} R c I' n
    let d := abutmentIso.{u,r,a,v} R c I n
    exact ⟨transportedAbutmentGraded S E.filtration D.filtration t h (n : ℤ) e d p,
      ⟨transportedClosed S E.filtration D.filtration t h p (n : ℤ),
        transportedClosed_arrow S E.filtration D.filtration t h p (n : ℤ),
        transportedLimitClass S E.filtration D.filtration t h (n : ℤ) e d p⟩,
      fun r hr hs ht ↦ pageTransportIso_limit S E D t h r hr p (n : ℤ) e d hs ht⟩

theorem coefficient_size_transport : coefficientSizeTransport.{u,r,a,v,b} := by
  intro X R U A c _ _
  refine ⟨sheafCarrierPreservesInjectives.{u,r,a,b} R, inferInstance, inferInstance,
    coefficientNaturalityData.{u,r,a,v} R c, coefficientNaturalityData.{u,r,max a b,v} R c, ?_⟩
  intro M I
  exact ⟨carrierModelComparison.{u,r,a,v,b} R c I⟩

end CoefficientSizeTransport

section MixedCoefficientNaturality

open _root_.Specs.AdvancedHomologicalAlgebra.CechSequenceOriginalCoefficients
  (mixedCoefficientNaturality)
open CechToCohomology (abutmentPiece abutmentPieceMap abutmentPieceMap_arrow)

private lemma conjugate_comm {C : Type*} [Category* C]
    {A A' B B' X X' Y Y' : C}
    (a : A ≅ A') (b : B ≅ B') (x : X ≅ X') (y : Y ≅ Y')
    (f : A ⟶ B) (g : X ⟶ Y)
    (i : A ⟶ X) (j : B ⟶ Y) (i' : A' ⟶ X') (j' : B' ⟶ Y')
    (hi : a.hom ≫ i' = i ≫ x.hom) (hj : b.hom ≫ j' = j ≫ y.hom)
    (h : f ≫ j = i ≫ g) :
    (a.inv ≫ f ≫ b.hom) ≫ j' = i' ≫ (x.inv ≫ g ≫ y.hom) := by
  apply (cancel_epi a.hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hi]
  rw [hj, ← Category.assoc, h, Category.assoc]

set_option maxHeartbeats 4000000 in
theorem mixed_coefficient_naturality : mixedCoefficientNaturality.{u,r,a,v,b} := by
  intro X R U A c _ _ _
  refine ⟨sheafCarrierPreservesInjectives.{u,r,a,b} R, sheafCarrierPreservesInjectives.{u,r,b,a} R,
    inferInstance, inferInstance, inferInstance, inferInstance, coefficientNaturalityData.{u,r,a,v} R c,
    coefficientNaturalityData.{u,r,b,v} R c, coefficientNaturalityData.{u,r,max a b,v} R c, ?_⟩
  intro M N f I J
  let I' := carrierLiftResolution.{u,r,a,b} R I
  let J' := carrierLiftResolution.{u,r,b,a} R J
  let f' := mixedCoefficientMap.{u,r,a,b} R f
  let φ := InjectiveResolution.desc f' J' I'
  have hφ := InjectiveResolution.desc_commutes_zero f' J' I'
  let D₁ := spectralData.{u,r,a,v} R c I
  let D₂ := spectralData.{u,r,b,v} R c J
  let E₁ := spectralData.{u,r,max a b,v} R c I'
  let E₂ := spectralData.{u,r,max a b,v} R c J'
  let S₁ := cochainCarrierLift.{u,r,a,v,b} R c
  let S₂ := cochainCarrierLift.{u,r,b,v,a} R c
  let A₁ := carrierModelComparison.{u,r,a,v,b} R c I
  let A₂ := carrierModelComparison.{u,r,b,v,a} R c J
  let a₁ := abutmentIso.{u,r,a,v} R c I
  let a₂ := abutmentIso.{u,r,b,v} R c J
  let b₁ := abutmentIso.{u,r,max a b,v} R c I'
  let b₂ := abutmentIso.{u,r,max a b,v} R c J'
  let t₁ := signedTotalCarrierIso.{u,r,a,v,b} R c I.cocomplex
  let t₂ := signedTotalCarrierIso.{u,r,b,v,a} R c J.cocomplex
  let h₁ := signedTotalCarrierIso_filtration.{u,r,a,v,b} R c I.cocomplex E₁ D₁
  let h₂ := signedTotalCarrierIso_filtration.{u,r,b,v,a} R c J.cocomplex E₂ D₂
  let s₁ (n : ℕ) := transportedAbutmentPiece S₁ E₁.filtration D₁.filtration t₁ h₁ (n : ℤ) (b₁ n) (a₁ n)
  let s₂ (n : ℕ) := transportedAbutmentPiece S₂ E₂.filtration D₂.filtration t₂ h₂ (n : ℤ) (b₂ n) (a₂ n)
  let u₁ (n : ℕ) := abutmentPiece D₁.filtration (n : ℤ) (a₁ n)
  let u₂ (n : ℕ) := abutmentPiece D₂.filtration (n : ℤ) (a₂ n)
  let w₁ (n : ℕ) := abutmentPiece E₁.filtration (n : ℤ) (b₁ n)
  let w₂ (n : ℕ) := abutmentPiece E₂.filtration (n : ℤ) (b₂ n)
  let C (n : ℕ) := (sectionLift.{u,r,max a b,v} R c).map ((cohomologyValue.{max a b,u,r} R U n).map f')
  let θ₁ (p q : ℕ) := localCechCarrierIso.{u,r,a,v,b} R c I p q
  let θ₂ (p q : ℕ) := localCechCarrierIso.{u,r,b,v,a} R c J p q
  let pg (r : ℤ) (hr : 2 ≤ r) (p n : ℤ) :=
    (A₁.pages r (by omega) p n).inv ≫ (pageMap.{u,r,max a b,v} R c I' J' φ).map r p n ≫
      (A₂.pages r (by omega) p n).hom
  let loc (p q : ℕ) := (θ₁ p q).inv ≫ (localCechCohomology.{u,r,max a b,v} R c p q).map f' ≫ (θ₂ p q).hom
  let tgt (n : ℕ) := (A₁.target n).inv ≫ C n ≫ (A₂.target n).hom
  let st (n : ℕ) (p : ℤ) :=
    (s₁ n p).inv ≫ abutmentPieceMap (filteredMap.{u,r,max a b,v} R c I' J' φ)
      (n : ℤ) (b₁ n) (b₂ n) p ≫ (s₂ n p).hom
  have hs₁ (n : ℕ) (p : ℤ) :
      (s₁ n p).hom ≫ S₁.map (u₁ n p).arrow = (w₁ n p).arrow ≫ (A₁.target n).hom := by
    rw [transportedAbutmentPiece_arrow]
    dsimp only [transportedAbutment, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    have hA : (transportedHomology S₁ t₁ (n : ℤ)).hom ≫ S₁.map (a₁ n).hom =
        (b₁ n).hom ≫ (A₁.target n).hom :=
      abutmentIso_carrier.{u,r,a,v,b} R c I n
    rw [hA, Iso.inv_hom_id_assoc]
  have hs₂ (n : ℕ) (p : ℤ) :
      (s₂ n p).hom ≫ S₂.map (u₂ n p).arrow = (w₂ n p).arrow ≫ (A₂.target n).hom := by
    rw [transportedAbutmentPiece_arrow]
    dsimp only [transportedAbutment, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    have hA : (transportedHomology S₂ t₂ (n : ℤ)).hom ≫ S₂.map (a₂ n).hom =
        (b₂ n).hom ≫ (A₂.target n).hom :=
      abutmentIso_carrier.{u,r,b,v,a} R c J n
    rw [hA, Iso.inv_hom_id_assoc]
  refine ⟨A₁, A₂, s₁, s₂,
    fun r hr p n ↦ originalCarrierMap (pg r hr p n).hom,
    fun p q ↦ originalCarrierMap (loc p q).hom,
    fun n ↦ originalCarrierMap (tgt n).hom,
    fun n p ↦ originalCarrierMap (st n p).hom,
    fun _ _ _ ↦ rfl, fun n p ↦ ⟨hs₁ n p, hs₂ n p⟩,
    fun _ _ ↦ rfl, fun _ _ _ ↦ rfl, ?_, ?_, ?_, ?_⟩
  · intro r hr p n x
    have h := conjugate_comm (A₁.pages r (by omega) p n) (A₂.pages r (by omega) p n)
      (A₁.pages r (by omega) (p+r) (n+1)) (A₂.pages r (by omega) (p+r) (n+1))
      _ _ _ _ _ _ (A₁.differential r (by omega) p n).symm (A₂.differential r (by omega) p n).symm
      ((pageMap.{u,r,max a b,v} R c I' J' φ).differential_comm r (by omega) p n)
    exact congrArg ULift.down (congr($(h) (ULift.up x)))
  · intro p q x
    let n := (p : ℤ) + (q : ℤ)
    let τ₁ := secondPageComparison.{u,r,a,v} R c I D₁ (verticalIso.{u,r,a,v} R c I) p q
    let τ₂ := secondPageComparison.{u,r,b,v} R c J D₂ (verticalIso.{u,r,b,v} R c J) p q
    have h := conjugate_comm (A₁.pages 2 (by omega) (p : ℤ) n) (A₂.pages 2 (by omega) (p : ℤ) n)
      (θ₁ p q) (θ₂ p q) _ _ _ _ (S₁.map τ₁.hom) (S₂.map τ₂.hom)
      (A₁.second p q) (A₂.second p q)
      (secondPageComparison_naturality.{u,r,max a b,v} R c I' J' φ f' hφ p q)
    exact congrArg ULift.down (congr($(h) (ULift.up x)))
  · intro n p x
    have hp := abutmentPieceMap_naturality.{u,r,max a b,v} R c I' J' φ f' hφ n p
    have h := conjugate_comm (s₁ n p) (s₂ n p) (A₁.target n) (A₂.target n)
      _ (C n) _ _ _ _ (hs₁ n p) (hs₂ n p) hp
    exact congrArg ULift.down (congr($(h) (ULift.up x)))
  · intro ψ hψ
    refine ⟨?_, ?_, abutmentLimitIso_naturality.{u,r,max a b,v} R c I' J' ψ⟩
    · intro r hr p n x
      have h := pageMap_lift_independent.{u,r,max a b,v} R c I' J' f' ψ φ hψ hφ r p n (by omega)
      change ((A₁.pages r (by omega) p n).inv ≫ (pageMap.{u,r,max a b,v} R c I' J' ψ).map r p n ≫
        (A₂.pages r (by omega) p n).hom) (ULift.up x) = _
      rw [h] <;> rfl
    · intro n p x
      have h : abutmentPieceMap (filteredMap.{u,r,max a b,v} R c I' J' ψ) (n : ℤ) (b₁ n) (b₂ n) p =
          abutmentPieceMap (filteredMap.{u,r,max a b,v} R c I' J' φ) (n : ℤ) (b₁ n) (b₂ n) p := by
        apply (cancel_mono (w₂ n p).arrow).1
        exact (abutmentPieceMap_naturality.{u,r,max a b,v} R c I' J' ψ f' hψ n p).trans
          (abutmentPieceMap_naturality.{u,r,max a b,v} R c I' J' φ f' hφ n p).symm
      change ((s₁ n p).inv ≫ abutmentPieceMap (filteredMap.{u,r,max a b,v} R c I' J' ψ)
          (n : ℤ) (b₁ n) (b₂ n) p ≫ (s₂ n p).hom) (ULift.up x) = _
      rw [h] <;> rfl

end MixedCoefficientNaturality

end AdvancedHomologicalAlgebra.CechSequenceOriginal
