import MathGenome.Internal.AdvancedHomologicalAlgebra.Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction
import MathGenome.Internal.AdvancedHomologicalAlgebra.AdvancedHomologicalAlgebra.CechCochains
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AdvancedHomologicalAlgebra.SheafTheory AdvancedHomologicalAlgebra.Cech
open AdvancedHomologicalAlgebra.CechChains
universe u v
namespace AdvancedHomologicalAlgebra.InjectiveCechExactness

section ChainAndHom

variable {X : TopCat.{u}} (R : RingSheaf X)

attribute [local instance] largeSheafification largeSheafificationLocalEquivalences

open SheafInjectivesAndRestriction in
private abbrev freeAt (V : Opens X) : PresheafOfModules.{u} R.obj :=
  (PresheafOfModules.free R.obj).obj (yoneda.obj V)

private def liftPresheafMap {A B : PresheafOfModules.{u} R.obj} (f : A ⟶ B) :
    liftPresheaf.{u, v} R A ⟶ liftPresheaf.{u, v} R B where
  app W := (ModuleCat.uliftFunctor.{v, u} (R.obj.obj W)).map (f.app W)
  naturality := by
    intro V W j
    ext s
    apply ULift.ext
    exact PresheafOfModules.naturality_apply f j s.down

open SheafInjectivesAndRestriction in
/-- The free presheaf maps to the given extended unit through sheafification. -/
private def freeToUnit (V : Opens X) : freeAt R V ⟶ (openUnit R V).val :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _)
    (openUnitFreeIso R V).inv

private lemma freeToUnit_generator (V : Opens X) :
    (freeToUnit R V).app (op V) (ModuleCat.freeMk (𝟙 V)) = openUnitGenerator R V := by
  change SheafInjectivesAndRestriction.freeOnOpenHom R V (openUnit R V)
    (SheafInjectivesAndRestriction.openUnitFreeIso R V).inv = _
  unfold SheafInjectivesAndRestriction.openUnitFreeIso
  rw [Equiv.apply_symm_apply, SheafInjectivesAndRestriction.homOpenUnit_eval]
  rfl

private instance freeToUnitLocallyInjective (V : Opens X) :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) (freeToUnit R V) := by
  change Presheaf.IsLocallyInjective _ ((PresheafOfModules.toPresheaf R.obj).map (freeToUnit R V))
  unfold freeToUnit
  rw [PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  have : IsIso ((PresheafOfModules.toPresheaf R.obj).map
      (SheafInjectivesAndRestriction.openUnitFreeIso R V).inv.val) := by
    change IsIso ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map
      (SheafInjectivesAndRestriction.openUnitFreeIso R V).inv)
    infer_instance
  have : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X) (freeAt R V).presheaf) := by
    exact ((Opens.grothendieckTopology X).W_toSheafify
      (freeAt R V).presheaf).isLocallyInjective
  exact Presheaf.isLocallyInjective_comp (Opens.grothendieckTopology X) _ _

private instance freeToUnitLocallySurjective (V : Opens X) :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) (freeToUnit R V) := by
  change Presheaf.IsLocallySurjective _ ((PresheafOfModules.toPresheaf R.obj).map (freeToUnit R V))
  unfold freeToUnit
  rw [PresheafOfModules.sheafificationAdjunction_homEquiv_apply,
    PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def]
  have : IsIso ((PresheafOfModules.toPresheaf R.obj).map
      (SheafInjectivesAndRestriction.openUnitFreeIso R V).inv.val) := by
    change IsIso ((SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj).map
      (SheafInjectivesAndRestriction.openUnitFreeIso R V).inv)
    infer_instance
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (toSheafify (Opens.grothendieckTopology X) (freeAt R V).presheaf) := by
    exact ((Opens.grothendieckTopology X).W_toSheafify
      (freeAt R V).presheaf).isLocallySurjective
  exact Presheaf.isLocallySurjective_comp (Opens.grothendieckTopology X) _ _

private instance liftPresheafMapLocallyInjective {A B : PresheafOfModules.{u} R.obj}
    (f : A ⟶ B) [PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X) f] :
    PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology X)
      (liftPresheafMap.{u, v} R f) where
  equalizerSieve_mem {W} a b h := by
    have eq : Presheaf.equalizerSieve (F := (liftPresheaf.{u, v} R A).presheaf) a b =
        Presheaf.equalizerSieve (F := A.presheaf) a.down b.down := by
      ext T j
      exact ULift.ext_iff
    rw [eq]
    have h' : (f.app W) a.down = (f.app W) b.down := by
      change (⟨(f.app W) a.down⟩ : ULift.{v} (B.obj W)) =
        ⟨(f.app W) b.down⟩ at h
      exact congrArg ULift.down h
    exact Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf R.obj).map f)
      a.down b.down h'

private instance liftPresheafMapLocallySurjective {A B : PresheafOfModules.{u} R.obj}
    (f : A ⟶ B) [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X) f] :
    PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology X)
      (liftPresheafMap.{u, v} R f) where
  imageSieve_mem {W} b := by
    refine (Opens.grothendieckTopology X).superset_covering ?_
      (Presheaf.imageSieve_mem _ ((PresheafOfModules.toPresheaf R.obj).map f) b.down)
    rintro T j ⟨a, ha⟩
    exact ⟨⟨a⟩, ULift.ext ha⟩

private def liftedFreeDesc (V : Opens X) (M : PresheafOfModules.{max u v} R.obj)
    (s : M.obj (op V)) : liftPresheaf.{u, v} R (freeAt R V) ⟶ M where
  app W := ModuleCat.ofHom
    ((Finsupp.linearCombination (R.obj.obj W) (fun a : W.unop ⟶ V ↦ M.map a.op s)).comp
      ULift.moduleEquiv.toLinearMap)
  naturality := by
    intro W Z j
    apply ModuleCat.hom_ext
    apply (LinearMap.cancel_right ULift.moduleEquiv.symm.surjective).mp
    apply Finsupp.lhom_ext'
    intro a
    apply LinearMap.ext_ring
    symm
    change M.map j ((Finsupp.linearCombination (R.obj.obj W)
      (fun a : W.unop ⟶ V ↦ M.map a.op s)) (Finsupp.single a 1)) =
        (Finsupp.linearCombination (R.obj.obj Z) (fun a : Z.unop ⟶ V ↦ M.map a.op s))
          ((freeAt R V).map j (ModuleCat.freeMk a))
    have h :
        (freeAt R V).map j (ModuleCat.freeMk a) = ModuleCat.freeMk (j.unop ≫ a) := by
      simp [PresheafOfModules.freeObj]
    rw [h]
    change M.map j ((Finsupp.linearCombination (R.obj.obj W)
      (fun a : W.unop ⟶ V ↦ M.map a.op s)) (Finsupp.single a 1)) =
        (Finsupp.linearCombination (R.obj.obj Z) (fun a : Z.unop ⟶ V ↦ M.map a.op s))
          (Finsupp.single (j.unop ≫ a) 1)
    simp only [Finsupp.linearCombination_single, one_smul, ← M.map_comp_apply, op_comp, Quiver.Hom.op_unop]

private lemma liftedFreeDesc_generator (V : Opens X) (M : PresheafOfModules.{max u v} R.obj)
    (s : M.obj (op V)) :
    (liftedFreeDesc R V M s).app (op V) ⟨ModuleCat.freeMk (𝟙 V)⟩ = s := by
  change Finsupp.linearCombination (R.obj.obj (op V)) (fun a : V ⟶ V ↦ M.map a.op s)
    (Finsupp.single (𝟙 V) 1) = s
  simp only [Finsupp.linearCombination_single, one_smul, op_id]
  change M.presheaf.map (𝟙 (op V)) s = s
  rw [M.presheaf.map_id]
  rfl

private lemma liftedFree_hom_ext (V : Opens X) (M : PresheafOfModules.{max u v} R.obj)
    (f g : liftPresheaf.{u, v} R (freeAt R V) ⟶ M)
    (h : f.app (op V) ⟨ModuleCat.freeMk (𝟙 V)⟩ = g.app (op V) ⟨ModuleCat.freeMk (𝟙 V)⟩) :
    f = g := by
  ext1 W
  apply ModuleCat.hom_ext
  apply (LinearMap.cancel_right ULift.moduleEquiv.symm.surjective).mp
  apply Finsupp.lhom_ext'
  intro a
  apply LinearMap.ext_ring
  have ha : (liftPresheaf.{u, v} R (freeAt R V)).map a.op ⟨ModuleCat.freeMk (𝟙 V)⟩ =
      ⟨ModuleCat.freeMk a⟩ := by
    apply ULift.ext
    simp [liftPresheaf, PresheafOfModules.freeObj]
  change f.app W ⟨ModuleCat.freeMk a⟩ = g.app W ⟨ModuleCat.freeMk a⟩
  rw [← ha, PresheafOfModules.naturality_apply, PresheafOfModules.naturality_apply, h]

private def liftedFreeEquiv (V : Opens X) (M : PresheafOfModules.{max u v} R.obj) :
    (liftPresheaf.{u, v} R (freeAt R V) ⟶ M) ≃ M.obj (op V) where
  toFun f := f.app (op V) ⟨ModuleCat.freeMk (𝟙 V)⟩
  invFun := liftedFreeDesc R V M
  left_inv _ := liftedFree_hom_ext R V M _ _ (liftedFreeDesc_generator R V M _)
  right_inv := liftedFreeDesc_generator R V M

private def openUnitEvaluation (V : Opens X) (M : SheafOfModules.{max u v} R) :
    (largeOpenUnit.{u, v} R V ⟶ M) ≃ M.val.obj (op V) :=
  (SheafOfModules.fullyFaithfulForget R).homEquiv.trans
    ((PresheafOfModules.homEquivOfIsLocallyBijective
      (f := liftPresheafMap.{u, v} R (freeToUnit R V)) M.isSheaf).trans
      (liftedFreeEquiv R V M.val))

private lemma openUnitEvaluation_apply (V : Opens X) (M : SheafOfModules.{max u v} R)
    (f : largeOpenUnit.{u, v} R V ⟶ M) :
    openUnitEvaluation R V M f = f.val.app (op V) (largeOpenUnitGenerator.{u, v} R V) := by
  change f.val.app (op V) ⟨(freeToUnit R V).app (op V) (ModuleCat.freeMk (𝟙 V))⟩ = _
  rw [freeToUnit_generator]
  rfl

/-- Evaluation at the lifted adjunction generator corepresents sections in the
enlarged coefficient category over the original ring sheaf. -/
def presentation : SectionPresentation.{u, v} R where
  equiv V M :=
    { __ := openUnitEvaluation R V M
      map_add' f g := by
        change openUnitEvaluation R V M (f + g) =
          openUnitEvaluation R V M f + openUnitEvaluation R V M g
        simp only [openUnitEvaluation_apply]; rfl }
  naturality V M N f g := by
    change openUnitEvaluation R V N (f ≫ g) = g.val.app (op V) (openUnitEvaluation R V M f)
    simp only [openUnitEvaluation_apply]
    rfl
  evaluation := openUnitEvaluation_apply R

theorem presentation_exists :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.presentationExistsType.{u, v} :=
  fun R ↦ ⟨presentation R⟩

private def unitAtTopEquiv (M : Modules R) :
    (SheafOfModules.unit R ⟶ M) ≃ M.val.obj (op (⊤ : Opens X)) :=
  M.unitHomEquiv.trans
    (sectionsAtInitial M.val (op ⊤) ((isTerminalTop (α := Opens X)).op _))

private lemma unitAtTopEquiv_apply (M : Modules R) (f : SheafOfModules.unit R ⟶ M) :
    unitAtTopEquiv R M f = f.val.app (op (⊤ : Opens X)) (1 : sectionRing R ⊤) := rfl

open SheafInjectivesAndRestriction in
private def smallTopUnitIso : openUnit R ⊤ ≅ SheafOfModules.unit R where
  hom := (homOpenUnit R ⊤ (SheafOfModules.unit R)).symm (1 : sectionRing R ⊤)
  inv := (unitAtTopEquiv R (openUnit R ⊤)).symm (openUnitGenerator R ⊤)
  hom_inv_id := by
    apply (homOpenUnit R ⊤ _).injective
    rw [homOpenUnit_naturality, Equiv.apply_symm_apply, ← unitAtTopEquiv_apply,
      Equiv.apply_symm_apply, homOpenUnit_eval]
    rfl
  inv_hom_id := by
    apply (unitAtTopEquiv R _).injective
    rw [unitAtTopEquiv_apply]
    change ((homOpenUnit R ⊤ (SheafOfModules.unit R)).symm (1 : sectionRing R ⊤)).val.app
      (op ⊤) (((unitAtTopEquiv R (openUnit R ⊤)).symm
        (openUnitGenerator R ⊤)).val.app (op ⊤) (1 : sectionRing R ⊤)) = _
    rw [← unitAtTopEquiv_apply, Equiv.apply_symm_apply, ← homOpenUnit_eval,
      Equiv.apply_symm_apply, unitAtTopEquiv_apply]
    rfl

/-- The top-open comparison is the lift of the original unit comparison. -/
def topUnitIso : largeOpenUnit.{u, v} R ⊤ ≅ liftSheaf.{u, v} R (SheafOfModules.unit R) where
  hom := liftSheafMap.{u, v} R (smallTopUnitIso R).hom
  inv := liftSheafMap.{u, v} R (smallTopUnitIso R).inv
  hom_inv_id := by
    ext1
    ext W s
    apply ULift.ext
    exact congr($((show (smallTopUnitIso R).hom ≫ (smallTopUnitIso R).inv = 𝟙 _ from
      (smallTopUnitIso R).hom_inv_id)).val.app W (s.down))
  inv_hom_id := by
    ext1
    ext W s
    apply ULift.ext
    exact congr($((show (smallTopUnitIso R).inv ≫ (smallTopUnitIso R).hom = 𝟙 _ from
      (smallTopUnitIso R).inv_hom_id)).val.app W (s.down))

open SheafInjectivesAndRestriction in
lemma topUnitIso_generator :
    (topUnitIso.{u, v} R).hom.val.app (op (⊤ : Opens X)) (largeOpenUnitGenerator.{u, v} R ⊤) =
      ⟨(1 : sectionRing R ⊤)⟩ := by
  apply ULift.ext
  change (smallTopUnitIso R).hom.val.app (op (⊤ : Opens X)) (openUnitGenerator R ⊤) = _
  rw [← homOpenUnit_eval]
  exact Equiv.apply_symm_apply (homOpenUnit R ⊤ (SheafOfModules.unit R)) _

variable {R} (e : SectionPresentation.{u, v} R)

lemma inclusion_restrict {V W : Opens X} (h : V ≤ W) (M : SheafOfModules.{max u v} R)
    (f : largeOpenUnit.{u, v} R W ⟶ M) :
    e.equiv V M (e.inclusion h ≫ f) = M.val.map (homOfLE h).op (e.equiv W M f) := by
  rw [e.naturality]
  simp only [SectionPresentation.inclusion, AddEquiv.apply_symm_apply]
  rw [PresheafOfModules.naturality_apply]
  rw [← e.naturality]
  simp only [Category.id_comp]


/-- The inclusion determined by evaluation is the lift of the canonical
extension-by-zero map between the original open units. -/
lemma inclusion_eq_lift {V W : Opens X} (h : V ≤ W) :
    e.inclusion h = liftSheafMap.{u, v} R
      (SheafInjectivesAndRestriction.openUnitMap R (homOfLE h)) := by
  apply (e.equiv V _).injective
  rw [e.evaluation, e.evaluation, e.inclusion_on_generator]
  apply ULift.ext
  exact (SheafInjectivesAndRestriction.openUnitMap_generator R (homOfLE h)).symm

lemma inclusion_id (V : Opens X) : e.inclusion (le_refl V) = 𝟙 _ := by
  apply (e.equiv V _).injective
  rw [SectionPresentation.inclusion, AddEquiv.apply_symm_apply]
  change (largeOpenUnit.{u, v} R V).val.presheaf.map (𝟙 (op V)) _ = _
  exact congr($( (largeOpenUnit.{u, v} R V).val.presheaf.map_id (op V)) _)

lemma inclusion_comp {V W Z : Opens X} (h : V ≤ W) (k : W ≤ Z) :
    e.inclusion h ≫ e.inclusion k = e.inclusion (h.trans k) := by
  apply (e.equiv V _).injective
  rw [inclusion_restrict]
  simp only [SectionPresentation.inclusion, AddEquiv.apply_symm_apply]
  exact ((largeOpenUnit.{u, v} R Z).val.map_comp_apply (homOfLE k).op (homOfLE h).op _).symm

variable {U : Opens X} {I : Type v} (c : Cover U I)

lemma hom_reindex (M : SheafOfModules.{max u v} R) {p q : ℕ}
    (f : Fin (p + 1) → Fin (q + 1)) (g : term (R := R) c p ⟶ M) :
    e.homCochains c M q (e.reindex c f ≫ g) =
      Cech.reindex R M.val c f (e.homCochains c M p g) := by
  funext t
  change e.equiv (tupleOpen c t) M (Sigma.ι (fun t : Fin (q + 1) → I ↦ largeOpenUnit.{u, v} R (tupleOpen c t)) t ≫ (e.reindex c f ≫ g)) = _
  rw [← Category.assoc]
  simp only [SectionPresentation.reindex, Sigma.ι_comp_desc, Category.assoc]
  exact inclusion_restrict e _ M _

lemma hom_boundary (M : SheafOfModules.{max u v} R) (p : ℕ) (f : term (R := R) c p ⟶ M) :
    e.homCochains c M (p + 1) (e.boundary c p ≫ f) =
      differential R M.val c p (e.homCochains c M p f) := by
  simp only [SectionPresentation.boundary, Preadditive.sum_comp, Preadditive.zsmul_comp,
    map_sum, map_zsmul, hom_reindex, differential, LinearMap.sum_apply,
    LinearMap.smul_apply]

lemma hom_augmentation (M : SheafOfModules.{max u v} R) (f : largeOpenUnit.{u, v} R U ⟶ M) :
    e.homCochains c M 0 (e.augmentation c ≫ f) =
      Cech.augmentation R M.val c (e.equiv U M f) := by
  funext t
  change e.equiv (tupleOpen c t) M (Sigma.ι (fun t : Fin 1 → I ↦ largeOpenUnit.{u, v} R (tupleOpen c t)) t ≫ (e.augmentation c ≫ f)) = _
  rw [← Category.assoc]
  simp only [SectionPresentation.augmentation, Sigma.ι_comp_desc]
  exact inclusion_restrict e _ M _

theorem hom_identification :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.homIdentification R c e :=
  ⟨hom_augmentation e c, hom_boundary e c⟩

lemma boundary_augmentation : e.boundary c 0 ≫ e.augmentation c = 0 := by
  apply (e.homCochains c _ 1).injective
  rw [hom_boundary]
  have h := LinearMap.congr_fun (CechCochains.augmentation_closed R
    (largeOpenUnit.{u, v} R U).val c) (e.equiv U _ (𝟙 _))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [← hom_augmentation, Category.comp_id] at h
  exact h.trans (map_zero _).symm

lemma boundary_squared (p : ℕ) : e.boundary c (p + 1) ≫ e.boundary c p = 0 := by
  apply (e.homCochains c _ (p + 2)).injective
  rw [hom_boundary]
  have h := LinearMap.congr_fun (CechCochains.differential_squared R
    (term (R := R) c p).val c p) (e.homCochains c _ p (𝟙 _))
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h
  rw [← hom_boundary, Category.comp_id] at h
  exact h.trans (map_zero _).symm

theorem chain_identities :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.chainIdentities R c e :=
  ⟨boundary_augmentation e c, boundary_squared e c⟩



/-- The chain complex of the full ordered-tuple coproducts. -/
def complex : ChainComplex (SheafOfModules.{max u v} R) ℕ :=
  ChainComplex.of (term R c) (e.boundary c) (boundary_squared e c)

theorem complex_construction :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.complexConstruction R c e := by
  refine ⟨complex e c, fun _ ↦ Iso.refl _, ?_⟩
  intro p
  change ChainComplex.of.d (term R c) (e.boundary c) (p + 1) p ≫ 𝟙 _ =
    𝟙 _ ≫ e.boundary c p
  rw [ChainComplex.of_d, Category.comp_id, Category.id_comp]

private lemma openRightMul_generator (V : Opens X) (r : sectionRing R V) :
    (openRightMul R V r).val.app (op V) (openUnitGenerator R V) =
      r • openUnitGenerator R V := by
  have h := SheafInjectivesAndRestriction.homOpenUnit_smul R V
    (openUnit R V) r (𝟙 _)
  rw [Category.comp_id, SheafInjectivesAndRestriction.homOpenUnit_eval,
    SheafInjectivesAndRestriction.homOpenUnit_eval] at h
  exact h

lemma hom_right_mul (M : SheafOfModules.{max u v} R) (p : ℕ) (r : sectionRing R U)
    (f : term R c p ⟶ M) :
    e.homCochains c M p (termRightMul R c p r ≫ f) =
      r • e.homCochains c M p f := by
  funext t
  let V := tupleOpen c t
  let ι : largeOpenUnit.{u, v} R V ⟶ term R c p :=
    Sigma.ι (fun t : Fin (p + 1) → I ↦ largeOpenUnit.{u, v} R (tupleOpen c t)) t
  let a : sectionRing R V := R.obj.map (homOfLE (tupleOpen_le c t)).op r
  change e.equiv V M (ι ≫ (termRightMul R c p r ≫ f)) = a • e.equiv V M (ι ≫ f)
  have hι : ι ≫ termRightMul R c p r =
      liftSheafMap.{u, v} R (openRightMul R V a) ≫ ι :=
    Sigma.ι_comp_desc _ _
  rw [← Category.assoc, hι, Category.assoc, e.evaluation, e.evaluation]
  change (ι ≫ f).val.app (op V)
    (⟨(openRightMul R V a).val.app (op V) (openUnitGenerator R V)⟩ :
      (largeOpenUnit.{u, v} R V).val.obj (op V)) = _
  rw [openRightMul_generator]
  exact ((ι ≫ f).val.app (op V)).hom.map_smul a (largeOpenUnitGenerator.{u, v} R V)

/-- Precomposition by restricted right multiplication gives the action on Hom. -/
theorem hom_linear_identification :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.homLinearIdentification R c e := by
  intro M p
  let E := e.homCochains c M p
  refine ⟨E.module (sectionRing R U), ?_⟩
  constructor
  · let _ := E.module (sectionRing R U)
    intro r f
    apply E.injective
    change E (r • f) = e.homCochains c M p (termRightMul R c p r ≫ f)
    rw [hom_right_mul]
    exact (E.linearEquiv (sectionRing R U)).map_smul r f
  · exact ⟨E.linearEquiv (sectionRing R U), fun _ ↦ rfl⟩

end ChainAndHom

attribute [local instance] largeSheafification largeSheafificationLocalEquivalences

section Stalk

variable {X : TopCat.{u}} (R : RingSheaf X) (x : X)

private abbrev neighbourhoodDiagram (M : SheafOfModules.{max u v} R) :
    (OpenNhds x)ᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  (OpenNhds.inclusion x).op ⋙ M.val.presheaf

private instance largeStalkModule (M : SheafOfModules.{max u v} R) :
    Module (stalkRing R x) ((largeStalk.{u, v} R x).obj M) :=
  letI (i : (OpenNhds x)ᵒᵖ) : Module (((OpenNhds.inclusion x).op ⋙ R.obj).obj i)
      ((neighbourhoodDiagram.{u, v} R x M).obj i) := (M.val.obj _).isModule
  Limits.IsColimit.module ((OpenNhds.inclusion x).op ⋙ R.obj) (neighbourhoodDiagram R x M)
    (fun f r m ↦ M.val.map_smul ((OpenNhds.inclusion x).op.map f) r m) (colimit.isColimit _) (colimit.isColimit _)

private lemma largeGerm_smul (M : SheafOfModules.{max u v} R) (W : Opens X)
    (hx : x ∈ W) (r : R.obj.obj (op W)) (m : M.val.obj (op W)) :
    largeGerm R M x W hx (r • m) =
      TopCat.Presheaf.germ R.obj W x hx r • largeGerm R M x W hx m :=
  letI (i : (OpenNhds x)ᵒᵖ) : Module (((OpenNhds.inclusion x).op ⋙ R.obj).obj i)
      ((neighbourhoodDiagram.{u, v} R x M).obj i) := (M.val.obj _).isModule
  Limits.IsColimit.ι_smul ((OpenNhds.inclusion x).op ⋙ R.obj)
    (neighbourhoodDiagram R x M) (fun f r m ↦ M.val.map_smul ((OpenNhds.inclusion x).op.map f) r m)
    (colimit.isColimit _) (colimit.isColimit _) (op ⟨W, hx⟩) r m

private lemma exists_largeGerm (M : SheafOfModules.{max u v} R)
    (m : (largeStalk.{u, v} R x).obj M) :
    ∃ (W : Opens X) (hx : x ∈ W) (s : M.val.obj (op W)), largeGerm R M x W hx s = m := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink.{u, v, u, v} _
  obtain ⟨i, s, hs⟩ := Types.jointly_surjective_of_isColimit
    (isColimitOfPreserves (forget AddCommGrpCat.{max u v})
      (colimit.isColimit (neighbourhoodDiagram R x M))) m
  exact ⟨i.unop.1, i.unop.2, s, hs⟩

private lemma largeGerm_res (M : SheafOfModules.{max u v} R) {V W : Opens X}
    (j : V ⟶ W) (hx : x ∈ V) (m : M.val.obj (op W)) :
    largeGerm R M x V hx (M.val.map j.op m) =
      largeGerm R M x W (leOfHom j hx) m := by
  let k : (⟨V, hx⟩ : OpenNhds x) ⟶ ⟨W, leOfHom j hx⟩ := homOfLE (leOfHom j)
  exact congr($(colimit.w (neighbourhoodDiagram R x M) k.op) m)

private lemma largeGerm_map {M N : SheafOfModules.{max u v} R} (f : M ⟶ N) (W : Opens X)
    (hx : x ∈ W) (m : M.val.obj (op W)) :
    (largeStalk.{u, v} R x).map f (largeGerm R M x W hx m) =
      largeGerm R N x W hx (f.val.app (op W) m) := by
  let F : (OpenNhds x)ᵒᵖ ⥤ (Opens X)ᵒᵖ := (OpenNhds.inclusion x).op
  let g := Functor.whiskerLeft F ((PresheafOfModules.toPresheaf R.obj).map f.val)
  exact congr($(ι_colimMap g (op ⟨W, hx⟩)) m)

private lemma largeStalkGermsJoint (M : SheafOfModules.{max u v} R)
    (r : stalkRing R x) (m : (largeStalk.{u, v} R x).obj M) :
    ∃ (W : Opens X) (hx : x ∈ W) (a : R.obj.obj (op W)) (s : M.val.obj (op W)),
      TopCat.Presheaf.germ R.obj W x hx a = r ∧ largeGerm R M x W hx s = m := by
  obtain ⟨V, hV, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq R.obj r
  obtain ⟨W, hW, s, rfl⟩ := exists_largeGerm R x M m
  refine ⟨V ⊓ W, ⟨hV, hW⟩, R.obj.map (homOfLE inf_le_left).op a,
    M.val.map (homOfLE inf_le_right).op s, ?_, ?_⟩
  · exact TopCat.Presheaf.germ_res_apply R.obj _ x _ a
  · exact largeGerm_res R x M _ _ s

/-- The module stalk has the additive stalk from the specification as its underlying group. -/
def linearStalk : SheafOfModules.{max u v} R ⥤ ModuleCat.{max u v} (stalkRing R x) where
  obj M := ModuleCat.of _ ((largeStalk.{u, v} R x).obj M)
  map {M N} f := ModuleCat.ofHom {
    toFun := (largeStalk.{u, v} R x).map f
    map_add' := map_add _
    map_smul' := by
      intro r m
      obtain ⟨W, hx, a, s, rfl, rfl⟩ := largeStalkGermsJoint R x M r m
      change (largeStalk.{u, v} R x).map f (TopCat.Presheaf.germ R.obj W x hx a • largeGerm R M x W hx s) =
        TopCat.Presheaf.germ R.obj W x hx a • (largeStalk.{u, v} R x).map f (largeGerm R M x W hx s)
      rw [← largeGerm_smul, largeGerm_map, (f.val.app _).hom.map_smul, largeGerm_smul,
        largeGerm_map] }
  map_id M := by
    ext m
    exact congr($((largeStalk.{u, v} R x).map_id M) m)
  map_comp f g := by
    ext m
    exact congr($((largeStalk.{u, v} R x).map_comp f g) m)

instance linearStalkAdditive : (linearStalk.{u, v} R x).Additive where
  map_add {M N} f g := by
    ext m
    obtain ⟨W, hx, s, rfl⟩ := exists_largeGerm R x M m
    change (largeStalk.{u, v} R x).map (f + g) _ =
      (largeStalk.{u, v} R x).map f _ + (largeStalk.{u, v} R x).map g _
    simp only [largeGerm_map]
    exact (largeGerm R N x W hx).hom.map_add _ _

private instance stalkSectionsModule (N : ModuleCat.{max u v} (stalkRing R x))
    (W : (Opens X)ᵒᵖ) : Module (R.obj.obj W) (PLift (x ∈ W.unop) → N) :=
  letI (h : PLift (x ∈ W.unop)) : Module (R.obj.obj W) N :=
    Module.compHom N (TopCat.Presheaf.germ R.obj W.unop x h.down).hom
  inferInstanceAs (Module (R.obj.obj W) (PLift (x ∈ W.unop) → N))

/-- The skyscraper over the original ringed space with an enlarged module carrier. -/
private def largeSkyscraperPresheaf (N : ModuleCat.{max u v} (stalkRing R x)) :
    PresheafOfModules.{max u v} R.obj where
  obj W := ModuleCat.of _ (PLift (x ∈ W.unop) → N)
  map {W V} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.obj.map f).hom).obj
      (ModuleCat.of _ (PLift (x ∈ V.unop) → N))) {
    toFun s h := s ⟨f.unop.le h.down⟩
    map_add' _ _ := rfl
    map_smul' r s := by
      funext h
      change (TopCat.Presheaf.germ R.obj W.unop x (f.unop.le h.down) r) •
        (s ⟨f.unop.le h.down⟩ : N) =
        (TopCat.Presheaf.germ R.obj V.unop x h.down (R.obj.map f r)) • s ⟨f.unop.le h.down⟩
      rw [TopCat.Presheaf.germ_res_apply' R.obj f x h.down r] }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private def largeSkyscraper (N : ModuleCat.{max u v} (stalkRing R x)) :
    SheafOfModules.{max u v} R where
  val := largeSkyscraperPresheaf R x N
  isSheaf := by
    have : HasLimitsOfSize.{u, u} AddCommGrpCat.{max u v} := hasLimitsOfSizeShrink.{u, u, v, v} _
    have : PreservesLimitsOfSize.{u, u} (forget AddCommGrpCat.{max u v}) :=
      preservesLimitsOfSize_shrink.{u, v, u, v} _
    apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing ((largeSkyscraperPresheaf R x N).presheaf : X.Presheaf AddCommGrpCat.{max u v})).mpr
    intro J W sf hsf
    have compatible {i j : J} (hi : x ∈ W i) (hj : x ∈ W j) :
        sf i ⟨hi⟩ = sf j ⟨hj⟩ :=
      congrFun (hsf i j) ⟨hi, hj⟩
    classical
    let pick (h : PLift (x ∈ iSup W)) := Classical.choose (Opens.mem_iSup.mp h.down)
    have hpick (h : PLift (x ∈ iSup W)) : x ∈ W (pick h) :=
      Classical.choose_spec (Opens.mem_iSup.mp h.down)
    let s (h : PLift (x ∈ iSup W)) := sf (pick h) ⟨hpick h⟩
    refine ⟨s, ?_, ?_⟩
    · intro i
      funext hi
      change s ⟨le_iSup W i hi.down⟩ = sf i hi
      exact compatible _ hi.down
    · intro t ht
      funext hx
      change t hx = sf (pick hx) ⟨hpick hx⟩
      exact congrFun (ht (pick hx)) ⟨hpick hx⟩

private def toLargeSkyscraper {M : SheafOfModules.{max u v} R}
    {N : ModuleCat.{max u v} (stalkRing R x)} (f : (linearStalk R x).obj M ⟶ N) :
    M ⟶ largeSkyscraper R x N :=
  ⟨{ app W := ModuleCat.ofHom {
        toFun s h := f (largeGerm R M x W.unop h.down s)
        map_add' s t := by
          funext h
          change f (largeGerm R M x W.unop h.down (s + t)) = _ + _
          rw [(largeGerm R M x W.unop h.down).hom.map_add, f.hom.map_add]
        map_smul' r s := by
          funext h
          change f (largeGerm R M x W.unop h.down (r • s)) =
            (TopCat.Presheaf.germ R.obj W.unop x h.down r) • f (largeGerm R M x W.unop h.down s)
          rw [largeGerm_smul]
          exact f.hom.map_smul _ _ }
     naturality := by
       intro W V j
       ext s
       funext h
       change f (largeGerm R M x V.unop h.down (M.val.map j s)) =
         f (largeGerm R M x W.unop (j.unop.le h.down) s)
       exact congrArg _ (largeGerm_res R x M j.unop h.down s) }⟩

private def fromLargeSkyscraperAdd {M : SheafOfModules.{max u v} R}
    {N : ModuleCat.{max u v} (stalkRing R x)} (f : M ⟶ largeSkyscraper R x N) :
    (largeStalk R x).obj M ⟶ AddCommGrpCat.of N :=
  colimit.desc (neighbourhoodDiagram R x M) {
    pt := AddCommGrpCat.of N
    ι.app W := AddCommGrpCat.ofHom {
      toFun s := f.val.app (op W.unop.1) s ⟨W.unop.2⟩
      map_zero' := congrFun ((f.val.app _).hom.map_zero) _
      map_add' _ _ := congrFun ((f.val.app _).hom.map_add _ _) _ }
    ι.naturality W V j := by
      ext s
      have h := PresheafOfModules.naturality_apply f.val ((OpenNhds.inclusion x).op.map j) s
      exact congrFun h ⟨V.unop.2⟩ }

private lemma fromLargeSkyscraperAdd_germ {M : SheafOfModules.{max u v} R}
    {N : ModuleCat.{max u v} (stalkRing R x)} (f : M ⟶ largeSkyscraper R x N)
    (W : Opens X) (hx : x ∈ W) (s : M.val.obj (op W)) :
    fromLargeSkyscraperAdd R x f (largeGerm R M x W hx s) = f.val.app (op W) s ⟨hx⟩ := by
  change ((colimit.ι (neighbourhoodDiagram R x M) (op ⟨W, hx⟩)) ≫
    colimit.desc _ _) s = _
  rw [colimit.ι_desc]
  rfl

private def fromLargeSkyscraper {M : SheafOfModules.{max u v} R}
    {N : ModuleCat.{max u v} (stalkRing R x)} (f : M ⟶ largeSkyscraper R x N) :
    (linearStalk R x).obj M ⟶ N :=
  ModuleCat.ofHom {
    toFun := fromLargeSkyscraperAdd R x f
    map_add' := (fromLargeSkyscraperAdd R x f).hom.map_add
    map_smul' r m := by
      obtain ⟨W, hx, a, s, rfl, rfl⟩ := largeStalkGermsJoint R x M r m
      change fromLargeSkyscraperAdd R x f
        (TopCat.Presheaf.germ R.obj W x hx a • largeGerm R M x W hx s) =
          TopCat.Presheaf.germ R.obj W x hx a • fromLargeSkyscraperAdd R x f (largeGerm R M x W hx s)
      rw [← largeGerm_smul, fromLargeSkyscraperAdd_germ, fromLargeSkyscraperAdd_germ]
      exact congrFun ((f.val.app _).hom.map_smul a s) ⟨hx⟩ }

private lemma fromLargeSkyscraper_germ {M : SheafOfModules.{max u v} R}
    {N : ModuleCat.{max u v} (stalkRing R x)} (f : M ⟶ largeSkyscraper R x N)
    (W : Opens X) (hx : x ∈ W) (s : M.val.obj (op W)) :
    fromLargeSkyscraper R x f (largeGerm R M x W hx s) = f.val.app (op W) s ⟨hx⟩ :=
  fromLargeSkyscraperAdd_germ R x f W hx s

private def largeStalkHomEquiv (M : SheafOfModules.{max u v} R)
    (N : ModuleCat.{max u v} (stalkRing R x)) :
    ((linearStalk R x).obj M ⟶ N) ≃+ (M ⟶ largeSkyscraper R x N) where
  toFun := toLargeSkyscraper R x
  invFun := fromLargeSkyscraper R x
  left_inv f := by
    ext m
    obtain ⟨W, hx, s, rfl⟩ := exists_largeGerm R x M m
    exact fromLargeSkyscraper_germ R x (toLargeSkyscraper R x f) W hx s
  right_inv f := by
    ext W s
    funext hx
    exact fromLargeSkyscraper_germ R x f _ hx.down s
  map_add' _ _ := by
    ext W s
    rfl

private lemma largeStalkHomEquiv_comp {M N : SheafOfModules.{max u v} R}
    {T : ModuleCat.{max u v} (stalkRing R x)} (f : M ⟶ N)
    (g : (linearStalk R x).obj N ⟶ T) :
    largeStalkHomEquiv R x M T ((linearStalk R x).map f ≫ g) =
      f ≫ largeStalkHomEquiv R x N T g := by
  ext W s
  funext hx
  change g ((largeStalk.{u, v} R x).map f (largeGerm R M x W.unop hx.down s)) =
    g (largeGerm R N x W.unop hx.down (f.val.app W s))
  rw [largeGerm_map]


private def largeSkyscraperFunctor :
    ModuleCat.{max u v} (stalkRing R x) ⥤ SheafOfModules.{max u v} R where
  obj := largeSkyscraper R x
  map {N P} f := ⟨{
    app W := ModuleCat.ofHom {
      toFun s h := f (s h)
      map_add' _ _ := by funext h; exact f.hom.map_add _ _
      map_smul' r s := by
        funext h
        exact f.hom.map_smul (TopCat.Presheaf.germ R.obj W.unop x h.down r) (s h) }
    naturality := by
      intro W V j
      ext s
      rfl }⟩
  map_id N := by ext W s; rfl
  map_comp f g := by ext W s; rfl

private def largeStalkAdjunction : linearStalk.{u, v} R x ⊣ largeSkyscraperFunctor R x :=
  Adjunction.mkOfHomEquiv
    { homEquiv M N := (largeStalkHomEquiv R x M N).toEquiv
      homEquiv_naturality_left_symm := by
        intro M P N f g
        change (largeStalkHomEquiv R x M N).symm (f ≫ g) =
          (linearStalk R x).map f ≫ (largeStalkHomEquiv R x P N).symm g
        apply (largeStalkHomEquiv R x M N).injective
        rw [largeStalkHomEquiv_comp, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
      homEquiv_naturality_right := by
        intro M N P f g
        ext W s
        funext h
        rfl }

instance linearStalk_isLeftAdjoint : (linearStalk.{u, v} R x).IsLeftAdjoint :=
  (largeStalkAdjunction R x).isLeftAdjoint

end Stalk

section OpenUnitStalks

variable {X : TopCat.{u}} {R : RingSheaf X} (e : SectionPresentation.{u, v} R)
variable (V : Opens X) (x : X) (hx : x ∈ V)

private abbrev stalkFreeRankOne := ModuleCat.of (stalkRing R x) (ULift.{v} (stalkRing R x))

private def stalkFreeEvaluation (N : ModuleCat.{max u v} (stalkRing R x)) :
    (stalkFreeRankOne.{u, v} (R := R) x ⟶ N) ≃ N where
  toFun f := f ⟨1⟩
  invFun n := ModuleCat.ofHom
    ((LinearMap.toSpanSingleton (stalkRing R x) N n).comp ULift.moduleEquiv.toLinearMap)
  left_inv f := by
    ext r
    change r.down • f ⟨1⟩ = f r
    rw [← f.hom.map_smul]
    congr
    exact ULift.ext (mul_one _)
  right_inv n := one_smul _ _

private def stalkUnitEvaluation (N : ModuleCat.{max u v} (stalkRing R x)) :
    ((linearStalk.{u, v} R x).obj (largeOpenUnit.{u, v} R V) ⟶ N) ≃ N :=
  (largeStalkHomEquiv R x _ N).toEquiv.trans
    ((e.equiv V (largeSkyscraper R x N)).toEquiv.trans
      { toFun := fun s ↦ s ⟨hx⟩
        invFun := fun n _ ↦ n
        left_inv := by intro s; rfl
        right_inv := by intro n; rfl })

private lemma stalkUnitEvaluation_apply (N : ModuleCat.{max u v} (stalkRing R x))
    (f : (linearStalk.{u, v} R x).obj (largeOpenUnit.{u, v} R V) ⟶ N) :
    stalkUnitEvaluation e V x hx N f =
      f (largeGerm R (largeOpenUnit.{u, v} R V) x V hx
        (largeOpenUnitGenerator.{u, v} R V)) := by
  change e.equiv V (largeSkyscraper R x N) (toLargeSkyscraper R x f) ⟨hx⟩ = _
  rw [e.evaluation]
  rfl

private def stalkUnitGeneratorMap :
    stalkFreeRankOne.{u, v} (R := R) x ⟶ (linearStalk.{u, v} R x).obj (largeOpenUnit.{u, v} R V) :=
  (stalkFreeEvaluation x _).symm
    (largeGerm R (largeOpenUnit.{u, v} R V) x V hx (largeOpenUnitGenerator.{u, v} R V))

private lemma stalkUnitGeneratorMap_apply_one :
    stalkUnitGeneratorMap.{u, v} (R := R) V x hx ⟨1⟩ =
      largeGerm R (largeOpenUnit.{u, v} R V) x V hx (largeOpenUnitGenerator.{u, v} R V) := by
  change (1 : stalkRing R x) • (largeGerm R (largeOpenUnit.{u, v} R V) x V hx
    (largeOpenUnitGenerator.{u, v} R V)) = _
  exact one_smul _ _

include e in
private theorem stalkUnitGeneratorMap_isIso : IsIso (stalkUnitGeneratorMap.{u, v} (R := R) V x hx) := by
  apply isIso_of_coyoneda_map_bijective
  intro N
  have h : (fun f : (linearStalk.{u, v} R x).obj (largeOpenUnit.{u, v} R V) ⟶ N ↦
      stalkUnitGeneratorMap.{u, v} (R := R) V x hx ≫ f) =
      (stalkFreeEvaluation x N).symm ∘ stalkUnitEvaluation e V x hx N := by
    funext f
    apply (stalkFreeEvaluation x N).injective
    rw [Function.comp_apply, Equiv.apply_symm_apply, stalkUnitEvaluation_apply]
    change f (stalkUnitGeneratorMap.{u, v} (R := R) V x hx ⟨1⟩) = _
    rw [stalkUnitGeneratorMap_apply_one]
  rw [h]
  exact (stalkFreeEvaluation x N).symm.bijective.comp (stalkUnitEvaluation e V x hx N).bijective

/-- On its supporting open, the lifted unit has a free rank-one module stalk. -/
def openUnitStalkIso :
    stalkFreeRankOne.{u, v} (R := R) x ≅ (linearStalk.{u, v} R x).obj (largeOpenUnit.{u, v} R V) :=
  @asIso _ _ _ _ (stalkUnitGeneratorMap.{u, v} (R := R) V x hx) (stalkUnitGeneratorMap_isIso e V x hx)

lemma openUnitStalkIso_generator :
    (openUnitStalkIso e V x hx).hom ⟨1⟩ =
      largeGerm R (largeOpenUnit.{u, v} R V) x V hx (largeOpenUnitGenerator.{u, v} R V) :=
  stalkUnitGeneratorMap_apply_one V x hx

include e in
/-- Off its supporting open, the lifted unit has zero stalk. -/
lemma openUnitStalk_isZero (hx' : x ∉ V) :
    IsZero ((linearStalk.{u, v} R x).obj (largeOpenUnit.{u, v} R V)) := by
  rw [IsZero.iff_id_eq_zero]
  apply (largeStalkHomEquiv R x _ _).injective
  apply (e.equiv V _).injective
  funext hx
  exact (hx' hx.down).elim

end OpenUnitStalks

section TupleStalks

variable {X : TopCat.{u}} {R : RingSheaf X} {U : Opens X} {I : Type v}
  (c : Cover U I) (x : X) (p : ℕ)

/-- Taking the module stalk commutes with the coproduct indexed by all tuples. -/
def stalkCoproductIso :
    (linearStalk.{u, v} R x).obj (term R c p) ≅
      ∐ fun t : Fin (p + 1) → I ↦
        (linearStalk.{u, v} R x).obj (largeOpenUnit.{u, v} R (tupleOpen c t)) :=
  PreservesCoproduct.iso _ _

lemma stalkCoproductIso_inv_ι (t : Fin (p + 1) → I) :
    Sigma.ι (fun t : Fin (p + 1) → I ↦
      (linearStalk.{u, v} R x).obj (largeOpenUnit.{u, v} R (tupleOpen c t))) t ≫
        (stalkCoproductIso (R := R) c x p).inv =
      (linearStalk.{u, v} R x).map
        (Sigma.ι (fun t : Fin (p + 1) → I ↦ largeOpenUnit.{u, v} R (tupleOpen c t)) t) := by
  rw [stalkCoproductIso, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]

end TupleStalks

section SkyscraperCochains

universe w
variable {X : TopCat.{u}} {R : RingSheaf X}
variable {U : Opens X} {I : Type v} (c : Cover U I)

/-- A skyscraper differential is the ordinary alternating sum on those tuples
whose entire intersection contains the point. -/
private lemma largeSkyscraper_differential_apply (x : X) (N : ModuleCat.{max u w} (stalkRing R x))
    (p : ℕ) (s : Cochains R (largeSkyscraper R x N).val c p)
    (t : Fin (p + 2) → I) (ht : x ∈ tupleOpen c t) :
    differential R (largeSkyscraper R x N).val c p s t ⟨ht⟩ =
      ∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) •
        s (t ∘ a.succAbove) ⟨tupleOpen_reindex_le c a.succAbove t ht⟩ := by
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply,
    Finset.sum_apply, Pi.smul_apply]
  change (∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) •
    (fun hx : PLift (x ∈ tupleOpen c t) ↦
      s (t ∘ a.succAbove) ⟨tupleOpen_reindex_le c a.succAbove t hx.down⟩)) ⟨ht⟩ = _
  rw [Finset.sum_apply]
  rfl

private lemma prepend_mem (x : X) (i : I) (hi : x ∈ c.opens i)
    {p : ℕ} (t : Fin (p + 1) → I) (ht : x ∈ tupleOpen c t) :
    x ∈ tupleOpen c (Fin.cons i t) := by
  rw [tupleOpen, Fin.cons_zero, Fin.cons_comp_succ]
  exact And.intro hi ht

/-- Prepending an index containing x. No ordering or distinctness of indices
is imposed, and all other entries remain in their original order. -/
private def largeSkyscraperPrepend (x : X) (N : ModuleCat.{max u w} (stalkRing R x))
    (i : I) (hi : x ∈ c.opens i) (p : ℕ)
    (s : Cochains R (largeSkyscraper R x N).val c (p + 1)) :
    Cochains R (largeSkyscraper R x N).val c p :=
  fun t ht ↦ s (Fin.cons i t) ⟨prepend_mem c x i hi t ht.down⟩

private lemma largeSkyscraper_primitive (x : X) (N : ModuleCat.{max u w} (stalkRing R x))
    (i : I) (hi : x ∈ c.opens i) (p : ℕ)
    (s : Cochains R (largeSkyscraper R x N).val c (p + 1))
    (hs : differential R (largeSkyscraper R x N).val c (p + 1) s = 0) :
    differential R (largeSkyscraper R x N).val c p (largeSkyscraperPrepend c x N i hi p s) = s := by
  change ((t : Fin (p + 2) → I) → PLift (x ∈ tupleOpen c t) → N) at s
  funext t ht
  have h := congrArg (fun z ↦ z (Fin.cons i t) ⟨prepend_mem c x i hi t ht.down⟩) hs
  rw [largeSkyscraper_differential_apply, Fin.sum_univ_succ] at h
  rw [largeSkyscraper_differential_apply]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ,
    pow_succ, mul_zsmul, neg_zsmul, one_zsmul] at h
  have htup : Fin.cons i t ∘ (0 : Fin (p + 3)).succAbove = t := by
    funext a
    simp
  change (∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) •
      s (Fin.cons i (t ∘ a.succAbove)) ⟨prepend_mem c x i hi _ (tupleOpen_reindex_le c a.succAbove t ht.down)⟩) = s t ht
  have hev {t t' : Fin (p + 2) → I} (h : t = t')
      (ht : x ∈ tupleOpen c t) (ht' : x ∈ tupleOpen c t') :
      s t ⟨ht⟩ = s t' ⟨ht'⟩ := by
    subst t'
    rfl
  have h0 (h0 : x ∈ tupleOpen c (Fin.cons i t ∘ (0 : Fin (p + 3)).succAbove)) :
      s (Fin.cons i t ∘ (0 : Fin (p + 3)).succAbove) ⟨h0⟩ = s t ht :=
    hev htup h0 ht.down
  have hstep (a : Fin (p + 2))
      (ha : x ∈ tupleOpen c (Fin.cons i t ∘ a.succ.succAbove)) :
      s (Fin.cons i t ∘ a.succ.succAbove) ⟨ha⟩ =
        s (Fin.cons i (t ∘ a.succAbove))
          ⟨prepend_mem c x i hi _ (tupleOpen_reindex_le c a.succAbove t ht.down)⟩ :=
    hev (Fin.cons_comp_succ_succAbove i t a) ha _
  simp only [h0, hstep] at h
  simp only [smul_neg, Finset.sum_neg_distrib, Pi.zero_apply] at h
  have hsum : (∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) •
      s (Fin.cons i (t ∘ a.succAbove)) ⟨prepend_mem c x i hi _ (tupleOpen_reindex_le c a.succAbove t ht.down)⟩) = s t ht := by
    exact (sub_eq_zero.mp (show s t ht - (∑ a : Fin (p + 2), (-1 : ℤ) ^ (a : ℕ) •
      s (Fin.cons i (t ∘ a.succAbove)) ⟨prepend_mem c x i hi _
        (tupleOpen_reindex_le c a.succAbove t ht.down)⟩) = 0 from by
          rw [sub_eq_add_neg]
          exact h)).symm
  exact hsum


/-- The beginning of the augmented complex is exact for every sheaf. -/
theorem augmentation_exact (M : SheafOfModules.{w} R) :
    Function.Injective (Cech.augmentation R M.val c) ∧
    ∀ z, differential R M.val c 0 z = 0 →
      ∃ s, Cech.augmentation R M.val c s = z := by
  constructor
  · intro s t h
    apply (CechCochains.augmentationToKernel_bijective R c M).injective
    exact Subtype.ext h
  · intro z hz
    refine ⟨(CechCochains.sectionsKernelEquiv R c M).symm ⟨z, hz⟩, ?_⟩
    exact congrArg Subtype.val
      ((CechCochains.sectionsKernelEquiv R c M).apply_symm_apply ⟨z, hz⟩)

/-- Outside the covered open, every cochain of a skyscraper is zero. -/
private lemma largeSkyscraper_cochain_zero (x : X) (hx : x ∉ U)
    (N : ModuleCat.{max u w} (stalkRing R x)) (p : ℕ)
    (s : Cochains R (largeSkyscraper R x N).val c p) : s = 0 := by
  funext t ht
  exact (hx (tupleOpen_le c t ht.down)).elim

/-- All positive cocycles of a skyscraper have primitives, by prepending any
cover index through the point; the outside-U case has zero cochain groups. -/
private theorem largeSkyscraper_exact (x : X) (N : ModuleCat.{max u w} (stalkRing R x))
    (p : ℕ) (s : Cochains R (largeSkyscraper R x N).val c (p + 1))
    (hs : differential R (largeSkyscraper R x N).val c (p + 1) s = 0) :
    ∃ z, differential R (largeSkyscraper R x N).val c p z = s := by
  classical
  by_cases hx : x ∈ U
  · have hx' : x ∈ iSup c.opens := by rwa [c.covers]
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
    exact ⟨largeSkyscraperPrepend c x N i hi p s, largeSkyscraper_primitive c x N i hi p s hs⟩
  · exact ⟨0, by rw [map_zero, largeSkyscraper_cochain_zero c x hx N (p + 1) s]⟩

end SkyscraperCochains

section StalkExactness

variable {X : TopCat.{u}} {R : RingSheaf X} {U : Opens X} {I : Type v} (c : Cover U I)
variable (e : SectionPresentation.{u, v} R)

/-- Embedding the cokernel in an injective lets one test exactness by Hom. -/
private lemma exact_of_hom_lifting {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
    (S : ShortComplex C)
    (h : ∀ (N : C), Injective N → ∀ (f : S.X₂ ⟶ N), S.f ≫ f = 0 →
      ∃ g : S.X₃ ⟶ N, S.g ≫ g = f) : S.Exact := by
  rw [S.exact_iff_kernel_ι_comp_cokernel_π_zero]
  let j := Injective.ι (cokernel S.f)
  obtain ⟨g, hg⟩ := h (Injective.under (cokernel S.f)) inferInstance
    (cokernel.π S.f ≫ j) (by simp)
  apply (cancel_mono j).mp
  rw [zero_comp, Category.assoc, ← hg, ← Category.assoc, kernel.condition, zero_comp]

private lemma stalk_exact_of_skyscraper_hom (S : ShortComplex (SheafOfModules.{max u v} R))
    (h : ∀ (x : X) (N : ModuleCat.{max u v} (stalkRing R x))
      (f : S.X₂ ⟶ largeSkyscraper R x N), S.f ≫ f = 0 →
        ∃ g : S.X₃ ⟶ largeSkyscraper R x N, S.g ≫ g = f) (x : X) :
    (S.map (linearStalk.{u, v} R x)).Exact := by
  apply exact_of_hom_lifting
  intro N _ f hf
  change (linearStalk.{u, v} R x).map S.f ≫ f = 0 at hf
  have hf' : S.f ≫ largeStalkHomEquiv R x _ N f = 0 := by
    rw [← largeStalkHomEquiv_comp, hf, map_zero]
  obtain ⟨g, hg⟩ := h x N (largeStalkHomEquiv R x _ N f) hf'
  refine ⟨(largeStalkHomEquiv R x _ N).symm g, ?_⟩
  change (linearStalk.{u, v} R x).map S.g ≫ (largeStalkHomEquiv R x _ N).symm g = f
  apply (largeStalkHomEquiv R x _ N).injective
  rw [largeStalkHomEquiv_comp, AddEquiv.apply_symm_apply, hg]

/-- In positive degrees the skyscraper cochain contraction tests exactness
on the actual stalks of the coproduct chain. -/
theorem positive_stalk_exact (p : ℕ) (x : X) :
    ((ShortComplex.mk (e.boundary c (p + 1)) (e.boundary c p)
      (boundary_squared e c p)).map (linearStalk.{u, v} R x)).Exact := by
  apply stalk_exact_of_skyscraper_hom
  intro x N f hf
  have hz : differential R (largeSkyscraper R x N).val c (p + 1)
      (e.homCochains c _ (p + 1) f) = 0 := by
    rw [← hom_boundary, hf, map_zero]
  obtain ⟨z, hz⟩ := largeSkyscraper_exact c x N p _ hz
  refine ⟨(e.homCochains c _ p).symm z, ?_⟩
  apply (e.homCochains c _ (p + 1)).injective
  rw [hom_boundary, AddEquiv.apply_symm_apply, hz]

theorem augmented_stalk_exact (x : X) :
    ((ShortComplex.mk (e.boundary c 0) (e.augmentation c)
      (boundary_augmentation e c)).map (linearStalk.{u, v} R x)).Exact := by
  apply stalk_exact_of_skyscraper_hom
  intro x N f hf
  have hz : differential R (largeSkyscraper R x N).val c 0
      (e.homCochains c _ 0 f) = 0 := by
    rw [← hom_boundary, hf, map_zero]
  obtain ⟨z, hz⟩ := (augmentation_exact c (largeSkyscraper R x N)).2 _ hz
  refine ⟨(e.equiv U _).symm z, ?_⟩
  apply (e.homCochains c _ 0).injective
  rw [hom_augmentation, AddEquiv.apply_symm_apply, hz]

private lemma linearStalk_augmentation_epi (x : X) :
    Epi ((linearStalk.{u, v} R x).map (e.augmentation c)) where
  left_cancellation {N} f g h := by
    apply (largeStalkHomEquiv R x _ N).injective
    apply (e.equiv U _).injective
    apply (augmentation_exact c (largeSkyscraper R x N)).1
    rw [← hom_augmentation, ← hom_augmentation, ← largeStalkHomEquiv_comp,
      ← largeStalkHomEquiv_comp, h]

theorem stalk_exactness :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.stalkExactness R c e := by
  intro x
  refine ⟨?_, ?_, ?_⟩
  · exact (ModuleCat.epi_iff_surjective _).mp (linearStalk_augmentation_epi c e x)
  · exact (ShortComplex.moduleCat_exact_iff _).mp (augmented_stalk_exact c e x)
  · intro p
    exact (ShortComplex.moduleCat_exact_iff _).mp (positive_stalk_exact c e p x)

end StalkExactness

section ExactnessOnStalks

variable {X : TopCat.{u}} {R : RingSheaf X}

local instance (x : X) : PreservesColimitsOfShape (OpenNhds x)ᵒᵖ
    (forget AddCommGrpCat.{max u v}) := by
  have : PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{max u v}) :=
    preservesFilteredColimitsOfSize_shrink.{u, v, u, v} _
  infer_instance

private lemma largeGerm_eq (M : SheafOfModules.{max u v} R)
    (x : X) {V W : Opens X} (hxV : x ∈ V) (hxW : x ∈ W)
    (s : M.val.obj (op V)) (t : M.val.obj (op W))
    (h : largeGerm R M x V hxV s = largeGerm R M x W hxW t) :
    ∃ (Z : Opens X) (_ : x ∈ Z) (i : Z ⟶ V) (j : Z ⟶ W),
      M.val.map i.op s = M.val.map j.op t := by
  let F := (OpenNhds.inclusion x).op ⋙ M.val.presheaf
  obtain ⟨Z, i, j, hz⟩ := (colimit.isColimit F).eq_iff.mp h
  exact ⟨Z.unop.1, Z.unop.2, i.unop, j.unop, hz⟩

private lemma epi_of_local_section_lifts {M N : SheafOfModules.{max u v} R} (f : M ⟶ N)
    (h : ∀ (W : Opens X) (s : N.val.obj (op W)) (x : X) (_ : x ∈ W),
      ∃ (V : Opens X) (i : V ⟶ W), (∃ t : M.val.obj (op V),
        f.val.app (op V) t = N.val.map i.op s) ∧ x ∈ V) : Epi f := by
  apply (SheafOfModules.toSheaf.{max u v} R).epi_of_epi_map (f := f)
  have : CategoryTheory.Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf.{max u v} R).map f) := by
    constructor
    intro W s
    apply (Opens.mem_grothendieckTopology X).mpr
    exact h W s
  infer_instance

lemma epi_of_largeStalk_surjective {M N : SheafOfModules.{max u v} R} (f : M ⟶ N)
    (h : ∀ x : X, Function.Surjective ((largeStalk.{u, v} R x).map f)) : Epi f := by
  apply epi_of_local_section_lifts f
  intro W s x hx
  obtain ⟨z, hz⟩ := h x (largeGerm R N x W hx s)
  obtain ⟨V, hxV, t, rfl⟩ := exists_largeGerm R x M z
  rw [largeGerm_map] at hz
  obtain ⟨U, hxU, i, j, hrestr⟩ := largeGerm_eq N x hxV hx _ _ hz
  refine ⟨U, j, ⟨M.val.map i.op t, ?_⟩, hxU⟩
  exact (PresheafOfModules.naturality_apply f.val i.op t).trans hrestr

/-- An exactness test for the enlarged coefficient category. A cycle is a
boundary locally because its germ is a boundary at each point. -/
lemma exact_of_largeStalk_exact (S : ShortComplex (SheafOfModules.{max u v} R))
    (h : ∀ (x : X) (z : (largeStalk.{u, v} R x).obj S.X₂),
      (largeStalk.{u, v} R x).map S.g z = 0 →
      ∃ w, (largeStalk.{u, v} R x).map S.f w = z) : S.Exact := by
  rw [S.exact_iff_epi_kernel_lift]
  let κ := kernel.ι S.g
  let a := kernel.lift S.g S.f S.zero
  have hk : a ≫ κ = S.f := kernel.lift_ι _ _ _
  have hz : κ ≫ S.g = 0 := kernel.condition _
  have hmono : ∀ W : (Opens X)ᵒᵖ, Mono (κ.val.app W) := by
    intro W
    change Mono ((SheafOfModules.evaluation R W).map κ)
    infer_instance
  apply epi_of_local_section_lifts a
  intro W s x hx
  let z := largeGerm R S.X₂ x W hx (κ.val.app (op W) s)
  have hz' : (largeStalk.{u, v} R x).map S.g z = 0 := by
    dsimp only [z]
    rw [largeGerm_map]
    change largeGerm R S.X₃ x W hx ((κ ≫ S.g).val.app (op W) s) = 0
    rw [hz]
    change largeGerm R S.X₃ x W hx 0 = 0
    exact map_zero _
  obtain ⟨w, hw⟩ := h x z hz'
  obtain ⟨V, hxV, t, rfl⟩ := exists_largeGerm R x S.X₁ w
  rw [largeGerm_map] at hw
  obtain ⟨U, hxU, i, j, ht⟩ := largeGerm_eq S.X₂ x hxV hx _ _ hw
  refine ⟨U, j, ⟨S.X₁.val.map i.op t, ?_⟩, hxU⟩
  apply (ModuleCat.mono_iff_injective _).mp (hmono (op U))
  change (a ≫ κ).val.app (op U) (S.X₁.val.map i.op t) =
    κ.val.app (op U) ((kernel S.g).val.map j.op s)
  rw [hk]
  exact (PresheafOfModules.naturality_apply S.f.val i.op t).trans
    (ht.trans (PresheafOfModules.naturality_apply κ.val j.op s).symm)

end ExactnessOnStalks

section SheafChain

variable {X : TopCat.{u}} {R : RingSheaf X} {U : Opens X} {I : Type v}
  (e : SectionPresentation.{u, v} R) (c : Cover U I)

theorem augmentation_epi : Epi (e.augmentation c) :=
  epi_of_largeStalk_surjective _ (fun x ↦ (stalk_exactness c e x).1)

theorem augmented_chain_exact :
    (ShortComplex.mk (e.boundary c 0) (e.augmentation c)
      (boundary_augmentation e c)).Exact :=
  exact_of_largeStalk_exact _ (fun x ↦ (stalk_exactness c e x).2.1)

theorem positive_chain_exact (p : ℕ) :
    (ShortComplex.mk (e.boundary c (p + 1)) (e.boundary c p)
      (boundary_squared e c p)).Exact :=
  exact_of_largeStalk_exact _ (fun x ↦ (stalk_exactness c e x).2.2 p)

/-- In the enlarged sheaf category, the positive Čech primitives are obtained
by applying contravariant Hom into the injective coefficient to the chain. -/
theorem injective_exact_in_chain_category (M : SheafOfModules.{max u v} R)
    [Injective M] :
    Function.Injective (Cech.augmentation R M.val c) ∧
    (∀ z, differential R M.val c 0 z = 0 → ∃ s, Cech.augmentation R M.val c s = z) ∧
    ∀ p z, differential R M.val c (p + 1) z = 0 → ∃ y, differential R M.val c p y = z := by
  refine ⟨(augmentation_exact c M).1, (augmentation_exact c M).2, ?_⟩
  intro p z hz
  let e := presentation.{u, v} R
  let f := (e.homCochains c M (p + 1)).symm z
  have hf : e.boundary c (p + 1) ≫ f = 0 := by
    apply (e.homCochains c M (p + 2)).injective
    rw [hom_boundary, map_zero]
    simpa only [f, AddEquiv.apply_symm_apply] using hz
  let g := (positive_chain_exact e c p).descToInjective f hf
  refine ⟨e.homCochains c M p g, ?_⟩
  rw [← hom_boundary]
  change e.homCochains c M (p + 1)
    ((ShortComplex.mk (e.boundary c (p + 1)) (e.boundary c p)
      (boundary_squared e c p)).g ≫ g) = z
  rw [ShortComplex.Exact.comp_descToInjective]
  exact (e.homCochains c M (p + 1)).apply_symm_apply z

theorem sheaf_chain_properties :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.sheafChainProperties R c e :=
  ⟨complex_construction e c, chain_identities e c, hom_identification e c,
    hom_linear_identification e c, stalk_exactness c e⟩

theorem sheaf_chain_construction :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.sheafChainConstructionType.{u, v} := by
  intro X R U I c
  exact ⟨presentation R, sheaf_chain_properties _ c⟩

theorem unit_augmentation_exactness (d : Cover (⊤ : Opens X) I)
    (iso : largeOpenUnit.{u, v} R ⊤ ≅ liftSheaf.{u, v} R (SheafOfModules.unit R)) :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.unitAugmentationExactness R d e iso := by
  intro x
  let F := largeStalk.{u, v} R x
  have hi := ConcreteCategory.bijective_of_isIso (F.map iso.hom)
  constructor
  · rw [Functor.map_comp]
    exact hi.surjective.comp (stalk_exactness d e x).1
  · intro z hz
    apply (stalk_exactness d e x).2.1 z
    apply hi.injective
    rw [map_zero]
    rw [Functor.map_comp] at hz
    exact hz

theorem top_cover_construction (d : Cover (⊤ : Opens X) I) :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.topCoverConstruction R d :=
  ⟨presentation R, sheaf_chain_properties _ d, topUnitIso.{u, v} R,
    topUnitIso_generator.{u, v} R, unit_augmentation_exactness _ d _⟩

/-- Applying the construction to the restricted ring sheaf gives the augmented
chain on the actual open subspace. -/
theorem on_open_construction :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.onOpenConstructionType.{u, v} := by
  intro X R U I c
  exact top_cover_construction (R := U.sheafRestrict.obj R) (internalCover c)

end SheafChain

section OriginalInjective
open AdvancedHomologicalAlgebra.SheafInjectivesAndRestriction
variable {X : TopCat.{u}} {R : RingSheaf X}
variable {U : Opens X} {I : Type v} (c : Cover U I)

private theorem skyscraper_exact (x : X) (N : ModuleCat.{u} (stalkRing R x))
    (p : ℕ) (s : Cochains R (skyscraper R x N).val c (p + 1))
    (hs : differential R (skyscraper R x N).val c (p + 1) s = 0) :
    ∃ z, differential R (skyscraper R x N).val c p z = s :=
  largeSkyscraper_exact.{u, v, 0} c x N p s hs

/-- A morphism of coefficient sheaves acts at each tuple intersection. -/
private def cochainMap {M N : Modules R} (g : M ⟶ N) (p : ℕ) :
    Cochains R M.val c p →+ Cochains R N.val c p where
  toFun s t := g.val.app (op (tupleOpen c t)) (s t)
  map_zero' := funext fun _ ↦ map_zero _
  map_add' _s _t := funext fun _ ↦ map_add _ _ _

private lemma cochainMap_differential {M N : Modules R} (g : M ⟶ N) (p : ℕ)
    (s : Cochains R M.val c p) :
    cochainMap c g (p + 1) (differential R M.val c p s) =
      differential R N.val c p (cochainMap c g p s) := by
  funext t
  change g.val.app (op (tupleOpen c t)) (differential R M.val c p s t) = _
  simp only [differential, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
    Pi.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  exact PresheafOfModules.naturality_apply g.val (homOfLE (tupleOpen_reindex_le c a.succAbove t)).op
    (s (t ∘ a.succAbove))

/-- Form a section of the sheaf product from its sections in each factor. -/
private def productSection {J : Type u} (A : J → Modules R) (V : Opens X)
    (s : ∀ j, sections R (A j) V) : sections R (∏ᶜ A) V :=
  homOpenUnit R V _ (Pi.lift fun j ↦ (homOpenUnit R V (A j)).symm (s j))

private lemma productSection_projection {J : Type u} (A : J → Modules R) (V : Opens X)
    (s : ∀ j, sections R (A j) V) (j : J) :
    (Pi.π A j).val.app (op V) (productSection A V s) = s j := by
  rw [productSection, ← homOpenUnit_naturality, Pi.lift_comp_π, Equiv.apply_symm_apply]

private lemma productSection_ext {J : Type u} (A : J → Modules R) (V : Opens X)
    (s t : sections R (∏ᶜ A) V)
    (h : ∀ j, (Pi.π A j).val.app (op V) s = (Pi.π A j).val.app (op V) t) :
    s = t := by
  apply (homOpenUnit R V (∏ᶜ A)).symm.injective
  apply Pi.hom_ext
  intro j
  apply (homOpenUnit R V (A j)).injective
  rw [homOpenUnit_naturality, homOpenUnit_naturality, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  exact h j

/-- Each original injective is a retract of the product of its injective
skyscrapers. Assemble primitives in the product coordinatewise. -/
private theorem injective_exact_aux :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.injectiveExactness R c := by
  classical
  intro M hM
  let _ : Injective M := hM
  obtain ⟨hAug, hZero⟩ := augmentation_exact c M
  refine ⟨hAug, hZero, ?_⟩
  intro p s hs
  let A := injectiveSkyscrapers R M
  let f : M ⟶ ∏ᶜ A := stalkInjectiveEmbedding R M
  let g : (∏ᶜ A) ⟶ M := Injective.factorThru (𝟙 M) f
  have hfg : f ≫ g = 𝟙 M := Injective.comp_factorThru _ _
  let s' : Cochains R (∏ᶜ A).val c (p + 1) := cochainMap c f (p + 1) s
  have hs' : differential R (∏ᶜ A).val c (p + 1) s' = 0 := by
    rw [← cochainMap_differential, hs, map_zero]
  have hx (x : X) :
      ∃ z : Cochains R (A x).val c p,
        differential R (A x).val c p z = cochainMap c (Pi.π A x) (p + 1) s' := by
    apply skyscraper_exact c x (Injective.under ((stalkFunctor R x).obj M))
    change differential R (A x).val c (p + 1) (cochainMap c (Pi.π A x) (p + 1) s') = 0
    rw [← cochainMap_differential, hs', map_zero]
  choose z hz using hx
  let y : Cochains R (∏ᶜ A).val c p := fun t ↦
    productSection A (tupleOpen c t) (fun x ↦ z x t)
  have hyx (x : X) : cochainMap c (Pi.π A x) p y = z x := by
    funext t
    exact productSection_projection A (tupleOpen c t) (fun x ↦ z x t) x
  have hy : differential R (∏ᶜ A).val c p y = s' := by
    funext t
    apply productSection_ext A (tupleOpen c t)
    intro x
    calc
      _ = cochainMap c (Pi.π A x) (p + 1) (differential R (∏ᶜ A).val c p y) t := rfl
      _ = differential R (A x).val c p (cochainMap c (Pi.π A x) p y) t :=
        congrFun (cochainMap_differential c (Pi.π A x) p y) t
      _ = _ := by rw [hyx, hz]; rfl
  refine ⟨cochainMap c g p y, ?_⟩
  rw [← cochainMap_differential, hy]
  funext t
  change (f ≫ g).val.app (op (tupleOpen c t)) (s t) = _
  rw [hfg]
  rfl

end OriginalInjective

theorem injective_exact :
    Specs.AdvancedHomologicalAlgebra.InjectiveCechExactness.injectiveExactnessType.{u, v} := by
  intro X R U I c
  exact injective_exact_aux (R := R) c

end AdvancedHomologicalAlgebra.InjectiveCechExactness
