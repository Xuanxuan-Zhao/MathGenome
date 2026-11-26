import Specs.LinearAlgebraicGroups.Cohomology.OrderedCechComparison
import LinearAlgebraicGroups.Cohomology.OrderedCechInjectiveRows
import LinearAlgebraicGroups.Cohomology.CechFirstQuadrantTotalization
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.Grp.Zero

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u
noncomputable section

namespace LinearAlgebraicGroups.OrderedCechComparison

open Specs.OrderedCechComparison

section CechDegreeZero

open scoped Simplicial

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [CommRing A] (X : SchemeOverRing A)
  {I : Type u} [LinearOrder I] (U : I → X.left.Opens)

private def singletonTuple (i : I) : Fin 1 ↪o I :=
  OrderEmbedding.ofStrictMono (fun _ => i) (fun a b h => (not_lt_of_ge (Subsingleton.elim a b).ge h).elim)

private theorem singletonTuple_apply (i : I) (j : Fin 1) : singletonTuple i j = i := rfl

private theorem singletonTuple_eq (e : Fin 1 ↪o I) : singletonTuple (e 0) = e :=
  DFunLike.ext _ _ (fun j => by have : j = 0 := Subsingleton.elim _ _; subst j; rfl)

private theorem tupleOpen_singleton (i : I) : tupleOpen U (singletonTuple i) = U i := by
  simp [tupleOpen, singletonTuple_apply]

private theorem tupleOpen_pair (e : Fin 2 ↪o I) :
    tupleOpen U e = U (e 0) ⊓ U (e 1) := by
  apply le_antisymm
  · exact le_inf (iInf_le _ 0) (iInf_le _ 1)
  · refine le_iInf fun j => ?_
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right

private def cochainFamily (F : X.left.Modules) (x : (SheafCech U F).X 0) (i : I) :
    Γ(F, U i) :=
  F.presheaf.map (eqToHom (tupleOpen_singleton X U i).symm).op (x (singletonTuple i))

private theorem tupleRestriction_congr (F : X.left.Modules) (x : (SheafCech U F).X 0)
    {V : X.left.Opens} {e e' : Fin 1 ↪o I} (h : e = e')
    (j : V ⟶ tupleOpen U e) (j' : V ⟶ tupleOpen U e') :
    F.presheaf.map j.op (x e) = F.presheaf.map j'.op (x e') := by
  subst e'
  rw [Subsingleton.elim j j']

private theorem cochainFamily_diff (F : X.left.Modules) (x : (SheafCech U F).X 0)
    (e : Fin 2 ↪o I) :
    (SheafCech U F).d 0 1 x e =
      F.presheaf.map (homOfLE (le_trans (le_of_eq (tupleOpen_pair X U e)) inf_le_right)).op
          (cochainFamily X U F x (e 1)) -
        F.presheaf.map (homOfLE (le_trans (le_of_eq (tupleOpen_pair X U e)) inf_le_left)).op
          (cochainFamily X U F x (e 0)) := by
  have h₀ : (SemiSimplexCategory.homEquiv (coface (n := 0) 0)).trans e = singletonTuple (e 1) := by
    apply DFunLike.ext
    intro j
    have : (j : Fin 1) = 0 := @Subsingleton.elim (Fin 1) inferInstance j 0
    subst j
    rfl
  have h₁ : (SemiSimplexCategory.homEquiv (coface (n := 0) 1)).trans e = singletonTuple (e 0) := by
    apply DFunLike.ext
    intro j
    have : (j : Fin 1) = 0 := @Subsingleton.elim (Fin 1) inferInstance j 0
    subst j
    rfl
  have hd : (SheafCech U F).d 0 1 = differential U (coefficientPresheaf (X := X) F) 0 :=
    CochainComplex.of_d (fun n => (orderedCochains U (coefficientPresheaf (X := X) F)).obj ⦋n⦌ₛ)
      (differential U (coefficientPresheaf (X := X) F)) 0
  rw [hd]
  change ((differential U (coefficientPresheaf (X := X) F) 0).hom x) e = _
  unfold differential
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul, neg_one_zsmul,
    ModuleCat.hom_add, ModuleCat.hom_neg, LinearMap.add_apply, LinearMap.neg_apply,
    sub_eq_add_neg]
  change (orderedCochains U (coefficientPresheaf (X := X) F)).map (coface 0) x e +
    -(orderedCochains U (coefficientPresheaf (X := X) F)).map (coface 1) x e = _
  apply congrArg₂ (· + -·)
  · unfold cochainFamily
    rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp, ← op_comp]
    change F.presheaf.map (homOfLE _).op (x _) = _
    exact tupleRestriction_congr X U F x h₀ _ _
  · unfold cochainFamily
    rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp, ← op_comp]
    change F.presheaf.map (homOfLE _).op (x _) = _
    exact tupleRestriction_congr X U F x h₁ _ _

private theorem cochainFamily_compatible (F : X.left.Modules)
    (x : (SheafCech U F).X 0) (hx : (SheafCech U F).d 0 1 x = 0) :
    TopCat.Presheaf.IsCompatible F.presheaf U (cochainFamily X U F x) := by
  have h {i j : I} (hij : i < j) :
      F.presheaf.map (Opens.infLELeft (U i) (U j)).op (cochainFamily X U F x i) =
        F.presheaf.map (Opens.infLERight (U i) (U j)).op (cochainFamily X U F x j) := by
    let e : Fin 2 ↪o I := OrderEmbedding.ofStrictMono ![i,j] (by
      apply Fin.strictMono_iff_lt_succ.mpr
      intro l
      have : l = 0 := Subsingleton.elim _ _
      subst l
      exact hij)
    have hw := congrFun hx e
    rw [cochainFamily_diff, Pi.zero_apply, sub_eq_zero] at hw
    let V := U i ⊓ U j
    have he : tupleOpen U e = V := tupleOpen_pair X U e
    let φ : V ⟶ tupleOpen U e := eqToHom he.symm
    have hh := congrArg (F.presheaf.map φ.op) hw.symm
    simp only [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp] at hh
    exact hh
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact h hij
  · have h : Opens.infLELeft (U i) (U i) = Opens.infLERight (U i) (U i) := Subsingleton.elim _ _
    rw [h]
  · let φ : U i ⊓ U j ⟶ U j ⊓ U i := eqToHom (inf_comm _ _)
    have hh := congrArg (F.presheaf.map φ.op) (h hji).symm
    simp only [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp] at hh
    exact hh

private theorem cochainFamily_augmentation (F : X.left.Modules)
    (x : (sectionsFunctor X).obj F) (i : I) :
    cochainFamily X U F (sectionAugmentation U F x) i = F.presheaf.map (U i).leTop.op x := by
  rw [cochainFamily, sectionAugmentation_apply, ← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
  rfl

theorem cechZeroAugmentation_closed (F : X.left.Modules) :
    sectionAugmentation U F ≫ (SheafCech U F).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  ext x : 1
  funext e
  change (SheafCech U F).d 0 1 (sectionAugmentation U F x) e =
    (0 : (SheafCech U F).X 1) e
  rw [cochainFamily_diff, Pi.zero_apply, sub_eq_zero, cochainFamily_augmentation,
    cochainFamily_augmentation, ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← F.presheaf.map_comp, ← F.presheaf.map_comp]
  rfl

private theorem cochainFamily_eq_iff (F : X.left.Modules)
    (x y : (SheafCech U F).X 0) :
    (∀ i, cochainFamily X U F x i = cochainFamily X U F y i) ↔ x = y := by
  constructor
  · intro h
    funext e
    rw [← singletonTuple_eq e]
    let H := F.presheaf.map (eqToHom (tupleOpen_singleton X U (e 0)).symm).op
    exact (ConcreteCategory.bijective_of_isIso H).injective (h (e 0))
  · intro h i
    rw [h]

private def cechZeroCycleAugmentation (F : X.left.Modules) :
    (sectionsFunctor X).obj F ⟶ (SheafCech U F).cycles 0 :=
  (SheafCech U F).liftCycles' (sectionAugmentation U F) 1 (by decide)
    (cechZeroAugmentation_closed X U F)

theorem cechZeroCycleAugmentation_isIso (hU : (⨆ i, U i) = ⊤) (F : X.left.Modules) :
    IsIso (cechZeroCycleAugmentation X U F) := by
  let K := SheafCech U F
  let aug := cechZeroCycleAugmentation X U F
  let i := K.iCycles 0
  let S : TopCat.Sheaf AddCommGrpCat _ := ⟨F.presheaf, F.isSheaf⟩
  have haug : aug ≫ i = sectionAugmentation U F := K.liftCycles_i _ 1
    ((ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 0 1 by decide))
    (cechZeroAugmentation_closed X U F)
  have happ (x : (sectionsFunctor X).obj F) :
      i (aug x) = sectionAugmentation U F x :=
    congrArg (fun f => f x) haug
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro x y h
    let s := cochainFamily X U F (i (aug x))
    have hc : K.d 0 1 (i (aug x)) = 0 :=
      congrArg (fun f => f (aug x)) (K.iCycles_d 0 1)
    obtain ⟨z, _hz, hu⟩ := S.existsUnique_gluing' U ⊤ (fun j => (U j).leTop) hU.ge s
      (cochainFamily_compatible X U F _ hc)
    have h₁ : ∀ j, F.presheaf.map (U j).leTop.op x = s j := by
      intro j
      rw [show s j = cochainFamily X U F (i (aug x)) j from rfl, happ, cochainFamily_augmentation]
    have h₂ : ∀ j, F.presheaf.map (U j).leTop.op y = s j := by
      intro j
      rw [show s j = cochainFamily X U F (i (aug x)) j from rfl, h, happ, cochainFamily_augmentation]
    exact (hu x h₁).trans (hu y h₂).symm
  · intro x
    have hc : K.d 0 1 (i x) = 0 := congrArg (fun f => f x) (K.iCycles_d 0 1)
    obtain ⟨z, hz, _⟩ := S.existsUnique_gluing' U ⊤ (fun j => (U j).leTop) hU.ge
      (cochainFamily X U F (i x)) (cochainFamily_compatible X U F _ hc)
    refine ⟨z, ((ModuleCat.mono_iff_injective i).mp inferInstance) ?_⟩
    rw [happ]
    apply (cochainFamily_eq_iff X U F _ _).mp
    intro j
    rw [cochainFamily_augmentation]
    exact hz j

/-- The degree-zero comparison for any ordered open cover is the gluing
isomorphism, with the canonical augmentation to the Čech complex. -/
def cechDegreeZeroIso (hU : (⨆ i, U i) = ⊤) (F : X.left.Modules) :
    (cohomology X 0).obj F ≅ (SheafCech U F).homology 0 := by
  let K := SheafCech U F
  letI := cechZeroCycleAugmentation_isIso X U hU F
  have h : (K.sc 0).f = 0 := K.shape _ _ (by simp)
  exact (cohomologyZero X).app F ≪≫ asIso (cechZeroCycleAugmentation X U F) ≪≫
    (K.sc 0).asIsoHomologyπ h

private theorem cechZeroCycleAugmentation_natural {F F' : X.left.Modules} (f : F ⟶ F') :
    (sectionsFunctor X).map f ≫ cechZeroCycleAugmentation X U F' =
      cechZeroCycleAugmentation X U F ≫
        HomologicalComplex.cyclesMap (cechMap U (coefficientPresheafMap (X := X) f)) 0 := by
  let K := SheafCech U F
  let K' := SheafCech U F'
  let m := cechMap U (coefficientPresheafMap (X := X) f)
  let h : (ComplexShape.up ℕ).next 0 = 1 :=
    (ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel 0 1 by decide)
  have h₁ : cechZeroCycleAugmentation X U F ≫ K.iCycles 0 = sectionAugmentation U F :=
    K.liftCycles_i _ 1 h (cechZeroAugmentation_closed X U F)
  have h₂ : cechZeroCycleAugmentation X U F' ≫ K'.iCycles 0 = sectionAugmentation U F' :=
    K'.liftCycles_i _ 1 h (cechZeroAugmentation_closed X U F')
  apply (cancel_mono (K'.iCycles 0)).mp
  change ((sectionsFunctor X).map f ≫ cechZeroCycleAugmentation X U F') ≫ K'.iCycles 0 =
    (cechZeroCycleAugmentation X U F ≫ HomologicalComplex.cyclesMap m 0) ≫ K'.iCycles 0
  rw [Category.assoc, h₂, Category.assoc, HomologicalComplex.cyclesMap_i,
    ← Category.assoc, h₁]
  apply ModuleCat.hom_ext
  ext x : 1
  funext e
  change sectionAugmentation U F' ((sectionsFunctor X).map f x) e =
    f.app (tupleOpen U e) (sectionAugmentation U F x e)
  rw [sectionAugmentation_apply, sectionAugmentation_apply]
  exact (PresheafOfModules.naturality_apply f.val (tupleOpen U e).leTop.op x).symm

/-- The degree-zero Čech comparison is natural in the sheaf of modules. -/
theorem cechDegreeZeroIso_natural (hU : (⨆ i, U i) = ⊤)
    {F F' : X.left.Modules} (f : F ⟶ F') :
    (cohomology X 0).map f ≫ (cechDegreeZeroIso X U hU F').hom =
      (cechDegreeZeroIso X U hU F).hom ≫
        HomologicalComplex.homologyMap (cechMap U (coefficientPresheafMap (X := X) f)) 0 := by
  let m := cechMap U (coefficientPresheafMap (X := X) f)
  change (cohomology X 0).map f ≫ (cohomologyZero X).hom.app F' ≫
        cechZeroCycleAugmentation X U F' ≫ (SheafCech U F').homologyπ 0 =
    ((cohomologyZero X).hom.app F ≫ cechZeroCycleAugmentation X U F ≫
      (SheafCech U F).homologyπ 0) ≫ HomologicalComplex.homologyMap m 0
  rw [NatTrans.naturality_assoc, reassoc_of% cechZeroCycleAugmentation_natural X U f,
    Category.assoc, Category.assoc, HomologicalComplex.homologyπ_naturality]

end CechDegreeZero

/-- Degree zero agrees with gluing for all covers, including the empty cover. -/
theorem degreeZeroComparison : DegreeZeroComparison.{u} := by
  intro A _ X Idx _ U hU
  exact ⟨cechDegreeZeroIso X U hU, fun α => cechDegreeZeroIso_natural X U hU α⟩

section Columns

open HomologicalComplex

variable {A : Type u} [CommRing A] {X : SchemeOverRing A}
  {Idx : Type u} [Preorder Idx] {U : Idx → X.left.Opens} {F : X.left.Modules}

private theorem evaluation_exact_succ (hF : IntersectionAcyclic U F)
    (I : InjectiveResolution F) (p : ℕ) (e : Fin (p + 1) ↪o Idx) (q : ℕ) :
    let L := ((openEvaluation (tupleOpen U e)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
    (ShortComplex.mk (L.d q (q + 1)) (L.d (q + 1) (q + 1 + 1)) (L.d_comp_d _ _ _)).Exact := by
  let L := ((openEvaluation (tupleOpen U e)).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  have h := (hF p e (q + 1) (Nat.succ_pos _)).of_iso
    (I.isoRightDerivedObj (openEvaluation (tupleOpen U e)) (q + 1)).symm
  have he : L.ExactAt (q + 1) := (exactAt_iff_isZero_homology L _).2 h
  exact (exactAt_iff' L q (q + 1) (q + 1 + 1) (by simp) (by simp)).1 he

/-- Positive cohomology in a resolution column vanishes, by solving a
coboundary equation independently over every tuple intersection. -/
theorem resolutionColumn_exact_succ (hF : IntersectionAcyclic U F)
    (I : InjectiveResolution F) (p q : ℕ) :
    ((resolutionDouble U I.cocomplex).X p).ExactAt (q + 1) := by
  classical
  let K := (resolutionDouble U I.cocomplex).X p
  apply (exactAt_iff' K q (q + 1) (q + 1 + 1) (by simp) (by simp)).2
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro x hx
  have hl (e : Fin (p + 1) ↪o Idx) :
      ∃ y : I.cocomplex.X q |>.val.obj (op (tupleOpen U e)),
        (I.cocomplex.d q (q + 1)).app (tupleOpen U e) y = x e := by
    apply (ShortComplex.moduleCat_exact_iff _).1 (evaluation_exact_succ hF I p e q)
    exact congrFun hx e
  choose z hz using hl
  exact ⟨z, funext hz⟩

/-- Degree zero of each column is the actual coefficient term. -/
theorem resolutionColumn_augmentation_isIso (I : InjectiveResolution F) (p : ℕ) :
    let K := (resolutionDouble U I.cocomplex).X p
    ∃ a : (SheafCech U F).X p ⟶ K.cycles 0,
      IsIso a ∧ a ≫ K.iCycles 0 = ((sheafCechFunctor U).map (I.ι.f 0)).f p := by
  classical
  let K := (resolutionDouble U I.cocomplex).X p
  let f := ((sheafCechFunctor U).map (I.ι.f 0)).f p
  have hz : f ≫ K.d 0 1 = 0 := by
    change (((sheafCechFunctor U).map (I.ι.f 0)).f p) ≫
      ((sheafCechFunctor U).map (I.cocomplex.d 0 1)).f p = 0
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, I.ι_f_zero_comp_complex_d,
      Functor.map_zero, HomologicalComplex.zero_f]
  let a := K.liftCycles' f 1 (by decide) hz
  have ha : a ≫ K.iCycles 0 = f := K.liftCycles_i f 1 (by simp) hz
  refine ⟨a, ?_, ha⟩
  have hf (e : Fin (p + 1) ↪o Idx) :
      Function.Injective ((I.ι.f 0).app (tupleOpen U e)) := by
    let m := (openEvaluation (tupleOpen U e)).map (I.ι.f 0)
    have hm : Mono ((openEvaluation (tupleOpen U e)).map (I.ι.f 0)) := inferInstance
    exact (ModuleCat.mono_iff_injective m).1 hm
  apply (ConcreteCategory.isIso_iff_bijective _).2
  constructor
  · intro x y h
    apply funext
    intro e
    apply hf e
    exact congrFun ((DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ha) x).symm.trans
      ((congrArg (K.iCycles 0) h).trans (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ha) y))) e
  · intro x
    have hx : K.d 0 1 (K.iCycles 0 x) = 0 :=
      DFunLike.congr_fun (congrArg ModuleCat.Hom.hom (K.iCycles_d 0 1)) x
    have hl (e : Fin (p + 1) ↪o Idx) :
        ∃ y : F.val.obj (op (tupleOpen U e)),
          (I.ι.f 0).app (tupleOpen U e) y = (K.iCycles 0 x) e := by
      let S := ShortComplex.mk _ _ I.ι_f_zero_comp_complex_d
      have he : (S.map (openEvaluation (tupleOpen U e))).Exact :=
        ShortComplex.exact_of_f_is_kernel _ (KernelFork.mapIsLimit _ I.isLimitKernelFork
          (openEvaluation (tupleOpen U e)))
      exact (ShortComplex.moduleCat_exact_iff _).1 he ((K.iCycles 0 x) e) (congrFun hx e)
    choose z hz using hl
    refine ⟨z, (ModuleCat.mono_iff_injective (K.iCycles 0)).1 inferInstance ?_⟩
    exact (DFunLike.congr_fun (congrArg ModuleCat.Hom.hom ha) z).trans (funext hz)

/-- Evaluation at the empty open has zero derived values in every degree. -/
theorem isZero_rightDerived_openEvaluation_bot (F : X.left.Modules) (n : ℕ) :
    IsZero (((openEvaluation (⊥ : X.left.Opens)).rightDerived n).obj F) := by
  let I := injectiveResolution F
  let E := openEvaluation (⊥ : X.left.Opens)
  let K := (E.mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  apply IsZero.of_iso _ (I.isoRightDerivedObj (openEvaluation (⊥ : X.left.Opens)) n)
  have h : IsZero (K.X n) := by
    let M := I.cocomplex.X n
    let S : TopCat.Sheaf AddCommGrpCat X.left := ⟨M.presheaf, M.isSheaf⟩
    let i := S.isTerminalOfEmpty.uniqueUpToIso (HasZeroObject.zeroIsTerminal (C := AddCommGrpCat))
    have hz : IsZero (S.obj.obj (op ⊥)) := (isZero_zero AddCommGrpCat).of_iso i
    apply ModuleCat.isZero_iff_subsingleton.2
    exact AddCommGrpCat.isZero_iff_subsingleton.1 hz
  exact (ExactAt.of_isZero h).isZero_homology

/-- Empty intersections impose no extra acyclicity condition. -/
theorem intersectionAcyclic_of_ne_bot (F : X.left.Modules)
    (h : ∀ (p : ℕ) (e : Fin (p + 1) ↪o Idx) (q : ℕ), 0 < q →
      tupleOpen U e ≠ ⊥ → IsZero (((openEvaluation (tupleOpen U e)).rightDerived q).obj F)) :
    IntersectionAcyclic U F := by
  intro p e q hq
  by_cases he : tupleOpen U e = ⊥
  · exact (congrArg
      (fun W : X.left.Opens => IsZero (((openEvaluation W).rightDerived q).obj F)) he).mpr
        (isZero_rightDerived_openEvaluation_bot F q)
  · exact h p e q hq he

end Columns

section ResolutionAxes

open HomologicalComplex

variable {A : Type u} [CommRing A] {X : SchemeOverRing A}
  {Idx : Type u} [Preorder Idx] (U : Idx → X.left.Opens)

/-- Global sections of the resolution restrict into the zeroth Čech column. -/
def sectionComplexAugmentation (K : CochainComplex X.left.Modules ℕ) :
    ((sectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj K ⟶
      (resolutionDouble U K).X 0 :=
  HomologicalComplex.Hom.mk (fun q => sectionAugmentation U (K.X q))
    (fun q q' _ => (sectionAugmentation_naturality U (K.d q q')).symm)

/-- The resolution map takes the coefficient Čech complex into the zeroth row. -/
def coefficientComplexAugmentation {F : X.left.Modules} (I : InjectiveResolution F) :
    SheafCech U F ⟶ (resolutionDouble U I.cocomplex).flip.X 0 :=
  (sheafCechFunctor U).map (I.ι.f 0)

theorem coefficientComplexAugmentation_closed {F : X.left.Modules} (I : InjectiveResolution F) (p : ℕ) :
    (coefficientComplexAugmentation U I).f p ≫ ((resolutionDouble U I.cocomplex).X p).d 0 1 = 0 := by
  change (((sheafCechFunctor U).map (I.ι.f 0)).f p) ≫
    ((sheafCechFunctor U).map (I.cocomplex.d 0 1)).f p = 0
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp, I.ι_f_zero_comp_complex_d,
    Functor.map_zero, HomologicalComplex.zero_f]

end ResolutionAxes

section Pullback

variable {A B : Type u} [CommRing A] [CommRing B] {X : SchemeOverRing A}
  {Y : SchemeOverRing B} (φ : A →+* B) (f : Y.left ⟶ X.left)
  (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
  {Idx : Type u} [Preorder Idx] (U : Idx → X.left.Opens)
  {F : X.left.Modules} {G : Y.left.Modules}

/-- Restricting a pulled-back global section commutes with the ordered
Čech augmentation. -/
theorem sectionAugmentation_pullback (α : F ⟶ (Scheme.Modules.pushforward f).obj G) :
    sectionAugmentation U F ≫ (cechPullback φ f hf U α).f 0 =
      sectionsPullback φ f hf α ≫
        (ModuleCat.restrictScalars φ).map (sectionAugmentation (pullbackCover f U) G) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext e
  change G.presheaf.map (pullbackToIntersection f U e).op
      (α.app (tupleOpen U e) (F.presheaf.map (tupleOpen U e).leTop.op x)) =
    G.presheaf.map (tupleOpen (pullbackCover f U) e).leTop.op (α.app ⊤ x)
  let j := (tupleOpen U e).leTop.op
  have hn := (PresheafOfModules.naturality_apply α.val j x).symm
  change G.presheaf.map (((Opens.map f.base).map (tupleOpen U e).leTop).op)
      (α.app ⊤ x) =
    α.app (tupleOpen U e) (F.presheaf.map j x) at hn
  refine (congrArg (G.presheaf.map (pullbackToIntersection f U e).op) hn.symm).trans ?_
  let y : Γ(G, ⊤) := α.app ⊤ x
  let i := ((Opens.map f.base).map (tupleOpen U e).leTop).op
  let k := (pullbackToIntersection f U e).op
  let j' := (tupleOpen (pullbackCover f U) e).leTop.op
  change G.presheaf.map k (G.presheaf.map i y) = G.presheaf.map j' y
  have h : G.presheaf.map i ≫ G.presheaf.map k = G.presheaf.map j' := by
    exact (G.presheaf.map_comp i k).symm.trans
      (congrArg G.presheaf.map (Subsingleton.elim (i ≫ k) j'))
  exact congrArg (fun g => g y) h

/-- Pullback on ordered cochains is compatible with a square of coefficient
maps whose right-hand side is pushed forward. -/
theorem cechPullback_comm {F' : X.left.Modules} {G' : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G)
    (β : F' ⟶ (Scheme.Modules.pushforward f).obj G')
    (a : F ⟶ F') (b : G ⟶ G')
    (h : a ≫ β = α ≫ (Scheme.Modules.pushforward f).map b) :
    (sheafCechFunctor U).map a ≫ cechPullback φ f hf U β =
      cechPullback φ f hf U α ≫
        ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℕ)).map
          ((sheafCechFunctor (pullbackCover f U)).map b) := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  funext e
  change G'.presheaf.map (pullbackToIntersection f U e).op
      (β.app (tupleOpen U e) (a.app (tupleOpen U e) (x e))) =
    b.app (tupleOpen (pullbackCover f U) e)
      (G.presheaf.map (pullbackToIntersection f U e).op (α.app (tupleOpen U e) (x e)))
  have h' := congrArg (fun g : F ⟶ (Scheme.Modules.pushforward f).obj G' =>
    g.app (tupleOpen U e) (x e)) h
  change β.app (tupleOpen U e) (a.app (tupleOpen U e) (x e)) =
    b.app (f ⁻¹ᵁ tupleOpen U e) (α.app (tupleOpen U e) (x e)) at h'
  exact (congrArg (G'.presheaf.map (pullbackToIntersection f U e).op) h').trans
    (PresheafOfModules.naturality_apply b.val (pullbackToIntersection f U e).op
      (α.app (tupleOpen U e) (x e))).symm

/-- Apply a lift of coefficients on each ordered intersection of a resolution. -/
def resolutionDoublePullback (K : CochainComplex X.left.Modules ℕ)
    (L : CochainComplex Y.left.Modules ℕ)
    (l : K ⟶ ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).obj L) :
    resolutionDouble U K ⟶
      (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℕ)).mapHomologicalComplex
        (.up ℕ)).obj (resolutionDouble (pullbackCover f U) L) := by
  let CK := ((sheafCechFunctor U).mapHomologicalComplex (.up ℕ)).obj K
  let CL := (((sheafCechFunctor (pullbackCover f U)) ⋙
    (ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)).obj L
  let h : CK ⟶ CL := HomologicalComplex.Hom.mk
    (fun n => cechPullback φ f hf U (l.f n))
    (fun n m _ => (cechPullback_comm φ f hf U (l.f n) (l.f m) (K.d n m) (L.d n m)
      (l.comm n m).symm).symm)
  exact (HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)).map h

@[simp]
theorem resolutionDoublePullback_comm_column {F : X.left.Modules} {G : Y.left.Modules}
    (α : F ⟶ (Scheme.Modules.pushforward f).obj G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (l : I.cocomplex ⟶ ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).obj J.cocomplex)
    (hl : I.ι.f 0 ≫ l.f 0 = α ≫ (Scheme.Modules.pushforward f).map (J.ι.f 0)) (p : ℕ) :
    (coefficientComplexAugmentation U I).f p ≫
      ((resolutionDoublePullback φ f hf U I.cocomplex J.cocomplex l).f p).f 0 =
    (cechPullback φ f hf U α).f p ≫
      (ModuleCat.restrictScalars φ).map ((coefficientComplexAugmentation (pullbackCover f U) J).f p) :=
  HomologicalComplex.congr_hom
    (cechPullback_comm φ f hf U α (l.f 0) (I.ι.f 0) (J.ι.f 0) hl) p

theorem resolutionDoublePullback_comm_row
    (K : CochainComplex X.left.Modules ℕ) (L : CochainComplex Y.left.Modules ℕ)
    (l : K ⟶ ((Scheme.Modules.pushforward f).mapHomologicalComplex (.up ℕ)).obj L) (q : ℕ) :
    (sectionComplexAugmentation U K).f q ≫
      ((resolutionDoublePullback φ f hf U K L l).f 0).f q =
    sectionsPullback φ f hf (l.f q) ≫
      (ModuleCat.restrictScalars φ).map ((sectionComplexAugmentation (pullbackCover f U) L).f q) :=
  sectionAugmentation_pullback φ f hf U (l.f q)

end Pullback

section CompareAugmentations

open HomologicalComplex

variable {A : Type u} [CommRing A] {X : SchemeOverRing A}
  {Idx : Type u} [Preorder Idx] (U : Idx → X.left.Opens)
  {F : X.left.Modules} (I : InjectiveResolution F)

private abbrev globalComplex := ((sectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj I.cocomplex

private abbrev totalComplex := (extendDouble (resolutionDouble U I.cocomplex)).total (.up ℤ)

variable (a : (globalComplex I).extend intEmbedding ⟶ totalComplex U I)
  (b : (SheafCech U F).extend intEmbedding ⟶ totalComplex U I)
  [QuasiIso a] [QuasiIso b]

/-- Once the two canonical augmentations are quasi-isomorphisms, the comparison
is obtained by following the section augmentation and inverting the coefficient
augmentation in cohomology. -/
def comparisonOfAugmentations (n : ℕ) :
    (cohomology X n).obj F ≅ (SheafCech U F).homology n :=
  I.isoRightDerivedObj (sectionsFunctor X) n ≪≫
    ((globalComplex I).extendHomologyIso intEmbedding (by simp [intEmbedding])).symm ≪≫
    asIso (homologyMap a (n : ℤ)) ≪≫ (asIso (homologyMap b (n : ℤ))).symm ≪≫
    (SheafCech U F).extendHomologyIso intEmbedding (by simp [intEmbedding])

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
theorem comparisonOfAugmentations_hom_comp (n : ℕ) :
    (comparisonOfAugmentations U I a b n).hom ≫
      ((SheafCech U F).extendHomologyIso intEmbedding
        (by simp [intEmbedding] : intEmbedding.f n = (n : ℤ))).inv ≫ homologyMap b (n : ℤ) =
      (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫
        ((globalComplex I).extendHomologyIso intEmbedding
          (by simp [intEmbedding] : intEmbedding.f n = (n : ℤ))).inv ≫ homologyMap a (n : ℤ) := by
  let G := (globalComplex I).extendHomologyIso intEmbedding (j := n) (j' := (n : ℤ))
    (by simp [intEmbedding])
  let C := (SheafCech U F).extendHomologyIso intEmbedding (j := n) (j' := (n : ℤ))
    (by simp [intEmbedding])
  let i := (I.isoRightDerivedObj (sectionsFunctor X) n).hom
  let a' := homologyMap a (n : ℤ)
  let b' := asIso (homologyMap b (n : ℤ))
  change (i ≫ G.inv ≫ a' ≫ b'.inv ≫ C.hom) ≫ C.inv ≫ b'.hom = i ≫ G.inv ≫ a'
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]


end CompareAugmentations

section Bound

variable {A : Type u} [CommRing A] {X : SchemeOverRing A} {Idx : Type u}
  [Preorder Idx] [Fintype Idx] (U : Idx → X.left.Opens)

theorem isZero_sheafCech_X_of_card_le (F : X.left.Modules) (n : ℕ)
    (h : Fintype.card Idx ≤ n) : IsZero ((SheafCech U F).X n) := by
  have noTuple (e : Fin (n + 1) ↪o Idx) : False := by
    have h' := Fintype.card_le_of_injective e e.injective
    simp only [Fintype.card_fin] at h'
    omega
  apply ModuleCat.isZero_iff_subsingleton.2
  exact ⟨fun a b => funext fun e => (noTuple e).elim⟩

theorem isZero_sheafCech_homology_of_card_le (F : X.left.Modules) (n : ℕ)
    (h : Fintype.card Idx ≤ n) : IsZero ((SheafCech U F).homology n) :=
  (HomologicalComplex.ExactAt.of_isZero (isZero_sheafCech_X_of_card_le U F n h)).isZero_homology

end Bound

section AxisExactness

open HomologicalComplex

private theorem singleQuasiIso {A : Type u} [CommRing A]
    {V : ModuleCat.{u} A} {K : CochainComplex (ModuleCat.{u} A) ℕ}
    (m : V ⟶ K.X 0) (hm : ∀ j, (ComplexShape.up ℕ).Rel 0 j → m ≫ K.d 0 j = 0)
    (a : V ⟶ K.cycles 0) [IsIso a] (ha : a ≫ K.iCycles 0 = m)
    (hK : ∀ j : ℕ, K.ExactAt (j + 1)) :
    QuasiIso (mkHomFromSingle m hm) := by
  apply (quasiIso_iff _).2
  intro j
  cases j with
  | zero =>
    let S := (single (ModuleCat.{u} A) (.up ℕ) 0).obj V
    let f : S ⟶ K := mkHomFromSingle m hm
    have h : cyclesMap f 0 = (singleObjCyclesSelfIso (.up ℕ) 0 V).hom ≫ a := by
      apply (cancel_mono (K.iCycles 0)).1
      rw [cyclesMap_i, Category.assoc, ha, singleObjCyclesSelfIso_hom, Category.assoc]
      rw [mkHomFromSingle_f]
    let : IsIso (cyclesMap f 0) := h ▸ (inferInstance : IsIso
      ((singleObjCyclesSelfIso (.up ℕ) 0 V).hom ≫ a))
    have : IsIso (S.homologyπ 0) := S.isIso_homologyπ 0 0 (by simp) (by rfl)
    have : IsIso (K.homologyπ 0) := K.isIso_homologyπ 0 0 (by simp) (K.shape _ _ (by simp))
    apply (quasiIsoAt_iff_isIso_homologyMap f 0).2
    have : IsIso (S.homologyπ 0 ≫ homologyMap f 0) := by
      rw [homologyπ_naturality]
      infer_instance
    exact IsIso.of_isIso_comp_left (S.homologyπ 0) _
  | succ j =>
    apply (quasiIsoAt_iff_exactAt _ _ (CochainComplex.exactAt_succ_single_obj V j)).2
    exact hK j

variable {A : Type u} [CommRing A] {X : SchemeOverRing A}
  {Idx : Type u} [LinearOrder Idx] (U : Idx → X.left.Opens)

private theorem sheafCech_d_apply (M : X.left.Modules) (p : ℕ)
    (x : (SheafCech U M).X p) :
    (SheafCech U M).d p (p + 1) x =
      Specs.OrderedCechInjectiveRows.differential M U p x := by
  funext e
  change (((SheafCech U M).d p (p + 1)).hom x) e = _
  rw [show (SheafCech U M).d p (p + 1) = differential U (coefficientPresheaf M) p from
    CochainComplex.of_d (fun n => (orderedCochains U (coefficientPresheaf M)).obj
      (SemiSimplexCategory.mk n)) (differential U (coefficientPresheaf M)) p]
  unfold differential Specs.OrderedCechInjectiveRows.differential
  erw [ModuleCat.hom_sum, LinearMap.sum_apply, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  erw [ModuleCat.hom_zsmul, LinearMap.smul_apply, Pi.smul_apply]
  rfl

private theorem resolutionRow_exact_succ [Finite Idx] (hU : (⨆ i, U i) = ⊤)
    (M : X.left.Modules) (hM : Injective M) (p : ℕ) :
    (SheafCech U M).ExactAt (p + 1) := by
  let K := SheafCech U M
  apply (exactAt_iff' K p (p + 1) (p + 1 + 1) (by simp) (by simp)).2
  apply (ShortComplex.moduleCat_exact_iff _).2
  intro x hx
  change K.d (p + 1) (p + 1 + 1) x = 0 at hx
  rw [sheafCech_d_apply] at hx
  obtain ⟨y, hy⟩ := LinearAlgebraicGroups.OrderedCechInjectiveRows.injective_row_exactness
    X.left.carrier X.left.ringCatSheaf Idx U hU M hM p x hx
  refine ⟨y, ?_⟩
  exact (sheafCech_d_apply U M p y).trans hy

end AxisExactness

section Extension

open HomologicalComplex

private theorem intEmbedding_at (p : ℕ) : intEmbedding.f p = (p : ℤ) := by
  simp [intEmbedding]

private theorem intEmbedding_not_negative (p : ℤ) (hp : p < 0) (i : ℕ) :
    intEmbedding.f i ≠ p := by
  rw [intEmbedding_at]
  omega

private abbrev extendInner {D : Type*} [Category* D] [Preadditive D] [HasZeroObject D] :=
  (intEmbedding.extendFunctor D).mapHomologicalComplex (.up ℕ)

private def mapExtendComponent {D E : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [Category* E] [Preadditive E] [HasZeroObject E]
    (R : D ⥤ E) [R.Additive] (K : CochainComplex D ℕ) (i : Option ℕ) :
    R.obj (HomologicalComplex.extend.X K i) ≅
      HomologicalComplex.extend.X ((R.mapHomologicalComplex (.up ℕ)).obj K) i :=
  match i with
  | none => R.mapZeroObject
  | some _ => Iso.refl _

set_option backward.isDefEq.respectTransparency false in
private def mapExtendIso {D E : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [Category* E] [Preadditive E] [HasZeroObject E]
    (R : D ⥤ E) [R.Additive] (K : CochainComplex D ℕ) :
    (R.mapHomologicalComplex (.up ℤ)).obj (K.extend intEmbedding) ≅
      ((R.mapHomologicalComplex (.up ℕ)).obj K).extend intEmbedding :=
  Hom.isoOfComponents (fun i => mapExtendComponent R K (intEmbedding.r i)) (by
    intro i j _
    change (mapExtendComponent R K (intEmbedding.r i)).hom ≫
      HomologicalComplex.extend.d _ (intEmbedding.r i) (intEmbedding.r j) =
      R.map (HomologicalComplex.extend.d _ (intEmbedding.r i) (intEmbedding.r j)) ≫
        (mapExtendComponent R K (intEmbedding.r j)).hom
    cases hi : intEmbedding.r i <;> cases hj : intEmbedding.r j <;>
      simp [mapExtendComponent, HomologicalComplex.extend.d])

private theorem mapExtendComponent_hom {D E : Type*} [Category* D] [Preadditive D]
    [HasZeroObject D] [Category* E] [Preadditive E] [HasZeroObject E]
    (R : D ⥤ E) [R.Additive] (K : CochainComplex D ℕ) {j : Option ℕ} {i : ℕ}
    (h : j = some i) :
    (mapExtendComponent R K j).hom ≫ (HomologicalComplex.extend.XIso _ h).hom =
      R.map (HomologicalComplex.extend.XIso K h).hom := by
  subst j
  change 𝟙 _ ≫ 𝟙 _ = R.map (𝟙 _)
  rw [Category.id_comp, R.map_id]

private theorem mapExtendIso_hom_f {D E : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [Category* E] [Preadditive E] [HasZeroObject E]
    (R : D ⥤ E) [R.Additive] (K : CochainComplex D ℕ) (i : ℕ) :
    (mapExtendIso R K).hom.f (i : ℤ) ≫
      (((R.mapHomologicalComplex (.up ℕ)).obj K).extendXIso intEmbedding (intEmbedding_at i)).hom =
    R.map (K.extendXIso intEmbedding (intEmbedding_at i)).hom := by
  exact mapExtendComponent_hom R K (intEmbedding.r_eq_some (intEmbedding_at i))

@[reassoc (attr := simp)]
private theorem iso_inv_hom_f {D : Type*} [Category* D] [HasZeroMorphisms D]
    {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex D c}
    (e : K ≅ L) (i : ι) :
    e.inv.f i ≫ e.hom.f i = 𝟙 _ := congr_hom e.inv_hom_id i

private def extendMapTo {D E : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [Category* E] [Preadditive E] [HasZeroObject E]
    (R : D ⥤ E) [R.Additive] {K : CochainComplex E ℕ} {L : CochainComplex D ℕ}
    (g : K ⟶ (R.mapHomologicalComplex (.up ℕ)).obj L) :
    K.extend intEmbedding ⟶ (R.mapHomologicalComplex (.up ℤ)).obj (L.extend intEmbedding) :=
  extendMap g intEmbedding ≫ (mapExtendIso R L).inv

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem extendMapTo_f {D E : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [Category* E] [Preadditive E] [HasZeroObject E]
    (R : D ⥤ E) [R.Additive] {K : CochainComplex E ℕ} {L : CochainComplex D ℕ}
    (g : K ⟶ (R.mapHomologicalComplex (.up ℕ)).obj L) (i : ℕ) :
    (extendMapTo R g).f (i : ℤ) ≫ R.map (L.extendXIso intEmbedding (intEmbedding_at i)).hom =
      (K.extendXIso intEmbedding (intEmbedding_at i)).hom ≫ g.f i := by
  rw [← mapExtendIso_hom_f, extendMapTo, comp_f, Category.assoc, iso_inv_hom_f_assoc,
    extendMap_f _ _ (intEmbedding_at i)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable {A : Type u} [CommRing A]

private def columnIso (K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℕ) (.up ℕ)) (p : ℕ) :
    (extendDouble K).X (p : ℤ) ≅ (K.X p).extend intEmbedding :=
  ((extendInner (D := ModuleCat.{u} A)).obj K).extendXIso intEmbedding (intEmbedding_at p)

private def rowIso (K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℕ) (.up ℕ)) (q : ℕ) :
    (extendDouble K).flip.X (q : ℤ) ≅ (K.flip.X q).extend intEmbedding :=
  mapExtendIso (HomologicalComplex.eval _ _ (q : ℤ)) (extendInner.obj K) ≪≫
    (intEmbedding.extendFunctor _).mapIso
      ((NatIso.mapHomologicalComplex
        (intEmbedding.extendFunctorCompEvalIso _ (intEmbedding_at q)) (.up ℕ)).app K)

@[reassoc]
private theorem columnIso_hom_f
    (K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℕ) (.up ℕ)) (p q : ℕ) :
    (columnIso K p).hom.f (q : ℤ) ≫ ((K.X p).extendXIso intEmbedding (intEmbedding_at q)).hom =
      (doubleComponentIso K p q).hom := rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rowIso_hom_f
    (K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℕ) (.up ℕ)) (p q : ℕ) :
    (rowIso K q).hom.f (p : ℤ) ≫
       ((K.flip.X q).extendXIso intEmbedding (intEmbedding_at p)).hom =
      (doubleComponentIso K p q).hom := by
  simp only [rowIso, Iso.trans_hom, Functor.mapIso_hom, comp_f,
    ComplexShape.Embedding.extendFunctor_map]
  rw [extendMap_f _ _ (intEmbedding_at p)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, mapExtendIso_hom_f]
  rfl

private theorem extendDouble_firstQuadrant
    (K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℕ) (.up ℕ)) :
    CechFirstQuadrantTotalization.Specs.FirstQuadrant (extendDouble K) := by
  intro p q h
  by_cases hp : p < 0
  · exact (HomologicalComplex.eval _ _ q).map_isZero
      ((extendInner.obj K).isZero_extend_X intEmbedding p (intEmbedding_not_negative p hp))
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ p)
    exact ((K.X i).isZero_extend_X intEmbedding q (intEmbedding_not_negative q
      (h.resolve_left hp))).of_iso ((HomologicalComplex.eval _ _ q).mapIso (columnIso K i))

end Extension

section IntegerAxes

open HomologicalComplex

private def IsSingleResolution {A : Type u} [CommRing A]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) {V : ModuleCat.{u} A} (m : V ⟶ K.X 0) : Prop :=
  ∃ f : (single _ (.up ℤ) 0).obj V ⟶ K, QuasiIso f ∧
    f.f 0 = (singleObjXSelf (.up ℤ) 0 V).hom ≫ m

private theorem IsSingleResolution.closed {A : Type u} [CommRing A]
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {V : ModuleCat.{u} A} {m : V ⟶ K.X 0}
    (h : IsSingleResolution K m) (i : ℤ) (_ : (ComplexShape.up ℤ).Rel 0 i) :
    m ≫ K.d 0 i = 0 := by
  obtain ⟨f, _, hf⟩ := h
  apply (cancel_epi (singleObjXSelf (.up ℤ) 0 V).hom).mp
  rw [← Category.assoc, ← hf, f.comm, single_obj_d, zero_comp, comp_zero]

private theorem IsSingleResolution.quasiIso {A : Type u} [CommRing A]
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {V : ModuleCat.{u} A} {m : V ⟶ K.X 0}
    (h : IsSingleResolution K m) :
    QuasiIso (mkHomFromSingle m h.closed) := by
  have hc := h.closed
  obtain ⟨f, hq, hf⟩ := h
  have he : mkHomFromSingle m hc = f :=
    from_single_hom_ext ((mkHomFromSingle_f _ _).trans hf.symm)
  exact he.symm ▸ hq

private theorem singleResolution_of_isZero {A : Type u} [CommRing A]
    {K : CochainComplex (ModuleCat.{u} A) ℤ} {V : ModuleCat.{u} A} (m : V ⟶ K.X 0)
    (hV : IsZero V) (hK : ∀ i, IsZero (K.X i)) :
    IsSingleResolution K m := by
  refine ⟨0, (quasiIso_iff _).2 ?_, (hK 0).eq_of_tgt _ _⟩
  intro i
  apply (quasiIsoAt_iff_exactAt _ _ (ShortComplex.exact_of_isZero_X₂ _ ?_)).2
  · exact ShortComplex.exact_of_isZero_X₂ _ (hK i)
  · exact ((single (ModuleCat.{u} A) (.up ℤ) 0) ⋙ (eval _ _ i)).map_isZero hV

set_option backward.isDefEq.respectTransparency false in
private theorem singleResolution_extend {A : Type u} [CommRing A]
    {K : CochainComplex (ModuleCat.{u} A) ℕ} {L : CochainComplex (ModuleCat.{u} A) ℤ}
    {V W : ModuleCat.{u} A} {m : V ⟶ K.X 0} {b : W ⟶ L.X 0}
    (h : ∀ j, (ComplexShape.up ℕ).Rel 0 j → m ≫ K.d 0 j = 0)
    (hq : QuasiIso (mkHomFromSingle m h))
    (e : L ≅ K.extend intEmbedding) (w : W ≅ V)
    (hb : b ≫ e.hom.f 0 ≫ (K.extendXIso intEmbedding (intEmbedding_at 0)).hom =
      w.hom ≫ m) : IsSingleResolution L b := by
  let s := extendSingleIso intEmbedding V 0 0 (intEmbedding_at 0)
  let f := (single _ (.up ℤ) 0).map w.hom ≫ s.inv ≫
    extendMap (mkHomFromSingle m h) intEmbedding ≫ e.inv
  refine ⟨f, by dsimp [f]; infer_instance, ?_⟩
  apply (cancel_mono (e.hom.f 0 ≫ (K.extendXIso intEmbedding (intEmbedding_at 0)).hom)).mp
  have hz : intEmbedding.f (0 : ℕ) = (0 : ℤ) := intEmbedding_at 0
  simp only [f, comp_f, Category.assoc, iso_inv_hom_f_assoc, hb, single_map_f_self,
    s, extendSingleIso_inv_f, extendMap_f _ _ hz, mkHomFromSingle_f, Iso.inv_hom_id_assoc,
    Iso.inv_hom_id, Category.comp_id]

end IntegerAxes

section Assembly

open HomologicalComplex
open CechFirstQuadrantTotalization.Specs (FirstQuadrant RowClosed ColumnClosed
  RowComponents ColumnComponents)

variable {A : Type u} [CommRing A] {X : SchemeOverRing A}
  {Idx : Type u} [LinearOrder Idx] (U : Idx → X.left.Opens)
  {F : X.left.Modules} (I : InjectiveResolution F)

private abbrev doubleComplex := extendDouble (resolutionDouble U I.cocomplex)

private def rowAxis :
    (globalComplex I).extend intEmbedding ⟶ (doubleComplex U I).X 0 :=
  extendMap (sectionComplexAugmentation U I.cocomplex) intEmbedding ≫
    (columnIso (resolutionDouble U I.cocomplex) 0).inv

private def columnAxis :
    (SheafCech U F).extend intEmbedding ⟶ (doubleComplex U I).flip.X 0 :=
  extendMap (coefficientComplexAugmentation U I) intEmbedding ≫
    (rowIso (resolutionDouble U I.cocomplex) 0).inv

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem rowAxis_f (q : ℕ) :
    (rowAxis U I).f (q : ℤ) ≫ (doubleComponentIso (resolutionDouble U I.cocomplex) 0 q).hom =
      ((globalComplex I).extendXIso intEmbedding (intEmbedding_at q)).hom ≫
        sectionAugmentation U (I.cocomplex.X q) := by
  rw [← columnIso_hom_f, rowAxis, comp_f, Category.assoc, iso_inv_hom_f_assoc,
    extendMap_f _ _ (intEmbedding_at q)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem columnAxis_f (p : ℕ) :
    (columnAxis U I).f (p : ℤ) ≫ (doubleComponentIso (resolutionDouble U I.cocomplex) p 0).hom =
      ((SheafCech U F).extendXIso intEmbedding (intEmbedding_at p)).hom ≫
        (coefficientComplexAugmentation U I).f p := by
  rw [← rowIso_hom_f, columnAxis, comp_f, Category.assoc, iso_inv_hom_f_assoc,
    extendMap_f _ _ (intEmbedding_at p)]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
private theorem rowAxis_resolves [Finite Idx] (hU : (⨆ i, U i) = ⊤) (q : ℤ) :
    IsSingleResolution ((doubleComplex U I).flip.X q) ((rowAxis U I).f q) := by
  by_cases hq : q < 0
  · exact singleResolution_of_isZero _
      ((globalComplex I).isZero_extend_X intEmbedding q (intEmbedding_not_negative q hq))
      (fun p => extendDouble_firstQuadrant _ p q (Or.inr hq))
  · obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ q)
    let M := I.cocomplex.X j
    have h : ∀ i, (ComplexShape.up ℕ).Rel 0 i →
        sectionAugmentation U M ≫ (SheafCech U M).d 0 i = 0 := by
      intro i hi
      change 0 + 1 = i at hi
      subst i
      exact cechZeroAugmentation_closed X U M
    have := cechZeroCycleAugmentation_isIso X U hU M
    have hq := singleQuasiIso _ h (cechZeroCycleAugmentation X U M)
      ((SheafCech U M).liftCycles_i _ 1 (by simp) (cechZeroAugmentation_closed X U M))
      (resolutionRow_exact_succ U hU M (I.injective j))
    apply singleResolution_extend h hq (rowIso (resolutionDouble U I.cocomplex) j)
      ((globalComplex I).extendXIso intEmbedding (intEmbedding_at j))
    exact (congrArg ((rowAxis U I).f (j : ℤ) ≫ ·) (rowIso_hom_f _ 0 j)).trans
      (rowAxis_f U I j)

set_option backward.isDefEq.respectTransparency false in
private theorem columnAxis_resolves (hF : IntersectionAcyclic U F) (p : ℤ) :
    IsSingleResolution ((doubleComplex U I).X p) ((columnAxis U I).f p) := by
  by_cases hp : p < 0
  · exact singleResolution_of_isZero _
      ((SheafCech U F).isZero_extend_X intEmbedding p (intEmbedding_not_negative p hp))
      (fun q => extendDouble_firstQuadrant _ p q (Or.inl hp))
  · obtain ⟨i, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ p)
    let K := (resolutionDouble U I.cocomplex).X i
    have h : ∀ j, (ComplexShape.up ℕ).Rel 0 j →
        (coefficientComplexAugmentation U I).f i ≫ K.d 0 j = 0 := by
      intro j hj
      change 0 + 1 = j at hj
      subst j
      exact coefficientComplexAugmentation_closed U I i
    obtain ⟨a, _, ha⟩ := resolutionColumn_augmentation_isIso I i (U := U)
    have hq := singleQuasiIso _ h a ha (resolutionColumn_exact_succ hF I i)
    apply singleResolution_extend h hq (columnIso (resolutionDouble U I.cocomplex) i)
      ((SheafCech U F).extendXIso intEmbedding (intEmbedding_at i))
    exact (congrArg ((columnAxis U I).f (i : ℤ) ≫ ·) (columnIso_hom_f _ i 0)).trans
      (columnAxis_f U I i)

private structure ResolutionAugmentations where
  a : (globalComplex I).extend intEmbedding ⟶ totalComplex U I
  b : (SheafCech U F).extend intEmbedding ⟶ totalComplex U I
  quasiIso_a : QuasiIso a
  quasiIso_b : QuasiIso b
  row_components : RowComponents (doubleComplex U I) (rowAxis U I) a
  column_components : ColumnComponents (doubleComplex U I) (columnAxis U I) b

private def resolutionAugmentations [Finite Idx] (hU : (⨆ i, U i) = ⊤)
    (hF : IntersectionAcyclic U F) : ResolutionAugmentations U I := by
  let K := doubleComplex U I
  have hr q := rowAxis_resolves U I hU q
  have hc p := columnAxis_resolves U I hF p
  have hK : FirstQuadrant K := extendDouble_firstQuadrant _
  have ha := CechFirstQuadrantTotalization.rowAssembly K hK _ (rowAxis U I)
    (fun q => (hr q).closed) (fun q => (hr q).quasiIso)
  have hb := CechFirstQuadrantTotalization.columnAssembly K hK _ (columnAxis U I)
    (fun p => (hc p).closed) (fun p => (hc p).quasiIso)
  exact ⟨ha.choose, hb.choose, ha.choose_spec.1, hb.choose_spec.1,
    ha.choose_spec.2, hb.choose_spec.2⟩

private def resolutionComparison (M : ResolutionAugmentations U I) (n : ℕ) :
    (cohomology X n).obj F ≅ (SheafCech U F).homology n :=
  letI := M.quasiIso_a
  letI := M.quasiIso_b
  comparisonOfAugmentations U I M.a M.b n

private theorem resolutionComparison_hom_comp (M : ResolutionAugmentations U I) (n : ℕ) :
    (resolutionComparison U I M n).hom ≫
      ((SheafCech U F).extendHomologyIso intEmbedding (intEmbedding_at n)).inv ≫
      homologyMap M.b (n : ℤ) =
    (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫
      ((globalComplex I).extendHomologyIso intEmbedding (intEmbedding_at n)).inv ≫
      homologyMap M.a (n : ℤ) := by
  let := M.quasiIso_a
  let := M.quasiIso_b
  exact comparisonOfAugmentations_hom_comp U I M.a M.b n

set_option backward.isDefEq.respectTransparency false in
private theorem resolutionComparison_spec (M : ResolutionAugmentations U I) (n : ℕ) :
    IsComparisonFromResolution U I n (resolutionComparison U I M n) := by
  refine ⟨M.a, M.b, M.quasiIso_a, M.quasiIso_b, ?_, ?_, ?_⟩
  · intro q
    rw [M.row_components (q : ℤ), ← rowAxis_f_assoc U I q]
    simp only [Iso.hom_inv_id_assoc]
  · intro p
    refine (M.column_components (p : ℤ)).trans ?_
    have h := columnAxis_f_assoc U I p
      ((doubleComponentIso (resolutionDouble U I.cocomplex) p 0).inv ≫
        (doubleComplex U I).ιTotal (.up ℤ) (p : ℤ) 0 (p : ℤ) (add_zero _))
    simpa only [Iso.hom_inv_id_assoc, coefficientComplexAugmentation] using h
  · exact resolutionComparison_hom_comp U I M n

end Assembly

section ExtendMaps

open HomologicalComplex
open CechFirstQuadrantTotalization.Specs (mapBicomplex)

set_option backward.isDefEq.respectTransparency false in
private theorem extendMapTo_comm {D E : Type*} [Category* D] [Preadditive D] [HasZeroObject D]
    [Category* E] [Preadditive E] [HasZeroObject E]
    (R : D ⥤ E) [R.Additive] {K K' : CochainComplex E ℕ} {L L' : CochainComplex D ℕ}
    (g : K ⟶ (R.mapHomologicalComplex (.up ℕ)).obj L)
    (g' : K' ⟶ (R.mapHomologicalComplex (.up ℕ)).obj L')
    (a : K ⟶ K') (b : L ⟶ L')
    (h : a ≫ g' = g ≫ (R.mapHomologicalComplex (.up ℕ)).map b) :
    extendMap a intEmbedding ≫ extendMapTo R g' =
      extendMapTo R g ≫ (R.mapHomologicalComplex (.up ℤ)).map (extendMap b intEmbedding) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : i < 0
  · exact (K.isZero_extend_X intEmbedding i (intEmbedding_not_negative i hi)).eq_of_src _ _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
    apply (cancel_mono (R.map (L'.extendXIso intEmbedding (intEmbedding_at n)).hom)).1
    have hn : a.f n ≫ g'.f n = g.f n ≫ R.map (b.f n) := congr_hom h n
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc,
      extendMapTo_f, extendMap_f a _ (intEmbedding_at n), extendMap_f b _ (intEmbedding_at n),
      Iso.inv_hom_id_assoc, hn, ← Functor.map_comp, Iso.inv_hom_id, Category.comp_id]
    rw [Functor.map_comp, extendMapTo_f_assoc]

variable {A B : Type u} [CommRing A] [CommRing B]
  (R : ModuleCat.{u} B ⥤ ModuleCat.{u} A) [R.Additive]
  {K : HomologicalComplex₂ (ModuleCat.{u} A) (.up ℕ) (.up ℕ)}
  {L : HomologicalComplex₂ (ModuleCat.{u} B) (.up ℕ) (.up ℕ)}

private abbrev mapNatDouble :=
  (R.mapHomologicalComplex (.up ℕ)).mapHomologicalComplex (.up ℕ)

private def extendInnerMap (φ : K ⟶ (mapNatDouble R).obj L) :
    extendInner.obj K ⟶ ((R.mapHomologicalComplex (.up ℤ)).mapHomologicalComplex (.up ℕ)).obj
      (extendInner.obj L) :=
  Hom.mk (fun p => extendMapTo R (φ.f p)) (fun p q _ =>
    (extendMapTo_comm R (φ.f p) (φ.f q) (K.d p q) (L.d p q) (φ.comm p q).symm).symm)

private def extendDoubleMap (φ : K ⟶ (mapNatDouble R).obj L) :
    extendDouble K ⟶ (mapBicomplex R).obj (extendDouble L) :=
  extendMapTo (R.mapHomologicalComplex (.up ℤ)) (extendInnerMap R φ)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem extendDoubleMap_f (φ : K ⟶ (mapNatDouble R).obj L) (p q : ℕ) :
    ((extendDoubleMap R φ).f (p : ℤ)).f (q : ℤ) ≫ R.map (doubleComponentIso L p q).hom =
      (doubleComponentIso K p q).hom ≫ (φ.f p).f q := by
  have h := congr_hom (extendMapTo_f (R.mapHomologicalComplex (.up ℤ))
    (extendInnerMap R φ) p) (q : ℤ)
  change ((extendDoubleMap R φ).f (p : ℤ)).f (q : ℤ) ≫
      R.map ((columnIso L p).hom.f (q : ℤ)) =
    (columnIso K p).hom.f (q : ℤ) ≫ (extendMapTo R (φ.f p)).f (q : ℤ) at h
  rw [← columnIso_hom_f, ← columnIso_hom_f, Functor.map_comp, ← Category.assoc, h,
    Category.assoc, extendMapTo_f, Category.assoc]

end ExtendMaps

section HomologyMaps

open HomologicalComplex

variable {A B : Type u} [CommRing A] [CommRing B]
  (R : ModuleCat.{u} B ⥤ ModuleCat.{u} A) [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]

private def homologyTo {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{u} A) c} {L : HomologicalComplex (ModuleCat.{u} B) c}
    (g : K ⟶ (R.mapHomologicalComplex c).obj L) (n : ι) :
    K.homology n ⟶ R.obj (L.homology n) :=
  homologyMap g n ≫ ((L.sc n).mapHomologyIso R).hom

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem homologyTo_comm {ι : Type*} {c : ComplexShape ι}
    {K K' : HomologicalComplex (ModuleCat.{u} A) c}
    {L L' : HomologicalComplex (ModuleCat.{u} B) c}
    (g : K ⟶ (R.mapHomologicalComplex c).obj L)
    (g' : K' ⟶ (R.mapHomologicalComplex c).obj L')
    (a : K ⟶ K') (b : L ⟶ L')
    (h : a ≫ g' = g ≫ (R.mapHomologicalComplex c).map b) (n : ι) :
    homologyMap a n ≫ homologyTo R g' n = homologyTo R g n ≫ R.map (homologyMap b n) := by
  have hb := ShortComplex.mapHomologyIso_hom_naturality
    ((shortComplexFunctor (ModuleCat.{u} B) c n).map b) R
  change homologyMap ((R.mapHomologicalComplex c).map b) n ≫
      ((L'.sc n).mapHomologyIso R).hom =
    ((L.sc n).mapHomologyIso R).hom ≫ R.map (homologyMap b n) at hb
  rw [homologyTo, homologyTo, ← homologyMap_comp_assoc, h, homologyMap_comp,
    Category.assoc, hb, Category.assoc]

private def cyclesTo {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{u} A) c} {L : HomologicalComplex (ModuleCat.{u} B) c}
    (g : K ⟶ (R.mapHomologicalComplex c).obj L) (n : ι) :
    K.cycles n ⟶ R.obj (L.cycles n) :=
  cyclesMap g n ≫ ((L.sc n).mapCyclesIso R).hom

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem cyclesTo_iCycles {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{u} A) c} {L : HomologicalComplex (ModuleCat.{u} B) c}
    (g : K ⟶ (R.mapHomologicalComplex c).obj L) (n : ι) :
    cyclesTo R g n ≫ R.map (L.iCycles n) = K.iCycles n ≫ g.f n := by
  have h := ShortComplex.mapCyclesIso_hom_iCycles (L.sc n) R
  change ((L.sc n).mapCyclesIso R).hom ≫ R.map (L.iCycles n) =
    ((R.mapHomologicalComplex c).obj L).iCycles n at h
  rw [cyclesTo, Category.assoc, h, cyclesMap_i]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem homologyπ_homologyTo {ι : Type*} {c : ComplexShape ι}
    {K : HomologicalComplex (ModuleCat.{u} A) c} {L : HomologicalComplex (ModuleCat.{u} B) c}
    (g : K ⟶ (R.mapHomologicalComplex c).obj L) (n : ι) :
    K.homologyπ n ≫ homologyTo R g n = cyclesTo R g n ≫ R.map (L.homologyπ n) := by
  let S := L.sc n
  have h : (S.map R).homologyπ ≫ (S.mapHomologyIso R).hom =
      (S.mapCyclesIso R).hom ≫ R.map S.homologyπ := by
    rw [S.homologyData.left.mapHomologyIso_eq R,
      S.homologyData.left.mapCyclesIso_eq R, Iso.trans_hom, Iso.trans_hom]
    rw [ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom_assoc]
    simp only [Category.assoc, ShortComplex.LeftHomologyData.map_π, Functor.mapIso_hom,
      Iso.symm_hom, ← Functor.map_comp, ShortComplex.LeftHomologyData.π_comp_homologyIso_inv]
  simp only [homologyTo, cyclesTo, homologyπ_naturality_assoc, Category.assoc]
  exact congrArg (cyclesMap g n ≫ ·) h

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem homologyTo_extend {K : CochainComplex (ModuleCat.{u} A) ℕ}
    {L : CochainComplex (ModuleCat.{u} B) ℕ}
    (g : K ⟶ (R.mapHomologicalComplex (.up ℕ)).obj L) (n : ℕ) :
    homologyTo R (extendMapTo R g) (n : ℤ) ≫
      R.map (L.extendHomologyIso intEmbedding (intEmbedding_at n)).hom =
      (K.extendHomologyIso intEmbedding (intEmbedding_at n)).hom ≫ homologyTo R g n := by
  have hc : cyclesTo R (extendMapTo R g) (n : ℤ) ≫
      R.map (L.extendCyclesIso intEmbedding (intEmbedding_at n)).hom =
      (K.extendCyclesIso intEmbedding (intEmbedding_at n)).hom ≫ cyclesTo R g n := by
    apply (cancel_mono (R.map (L.iCycles n))).1
    rw [Category.assoc, ← Functor.map_comp, extendCyclesIso_hom_iCycles, Functor.map_comp,
      cyclesTo_iCycles_assoc, Category.assoc, extendMapTo_f, cyclesTo_iCycles,
      extendCyclesIso_hom_iCycles_assoc]
  apply (cancel_epi ((K.extend intEmbedding).homologyπ (n : ℤ))).1
  rw [homologyπ_homologyTo_assoc, ← Functor.map_comp, homologyπ_extendHomologyIso_hom,
    Functor.map_comp, ← Category.assoc, hc, Category.assoc,
    homologyπ_extendHomologyIso_hom_assoc, homologyπ_homologyTo]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
private theorem homologyTo_extend_inv {K : CochainComplex (ModuleCat.{u} A) ℕ}
    {L : CochainComplex (ModuleCat.{u} B) ℕ}
    (g : K ⟶ (R.mapHomologicalComplex (.up ℕ)).obj L) (n : ℕ) :
    homologyTo R g n ≫ R.map (L.extendHomologyIso intEmbedding (intEmbedding_at n)).inv =
      (K.extendHomologyIso intEmbedding (intEmbedding_at n)).inv ≫
        homologyTo R (extendMapTo R g) (n : ℤ) := by
  apply (cancel_mono (R.map (L.extendHomologyIso intEmbedding (intEmbedding_at n)).hom)).1
  rw [Category.assoc, ← R.map_comp, Iso.inv_hom_id, R.map_id, Category.comp_id,
    Category.assoc, homologyTo_extend, Iso.inv_hom_id_assoc]

private theorem homologyTo_id {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex (ModuleCat.{u} A) c} (g : K ⟶ L) (n : ι) :
    homologyTo (𝟭 (ModuleCat.{u} A)) (L := L) g n = homologyMap g n := by
  have h : cyclesTo (𝟭 (ModuleCat.{u} A)) (L := L) g n = cyclesMap g n := by
    apply (cancel_mono (L.iCycles n)).1
    exact (cyclesTo_iCycles (𝟭 (ModuleCat.{u} A)) (L := L) g n).trans (cyclesMap_i g n).symm
  apply (cancel_epi (K.homologyπ n)).1
  rw [homologyπ_homologyTo, homologyπ_naturality, h]
  rfl

end HomologyMaps

section Naturality

open HomologicalComplex
open CechFirstQuadrantTotalization.Specs (mapBicomplex)

variable {A B : Type u} [CommRing A] [CommRing B]
  {X : SchemeOverRing A} {Y : SchemeOverRing B}
  {Idx : Type u} [LinearOrder Idx] (U : Idx → X.left.Opens) (V : Idx → Y.left.Opens)
  {F : X.left.Modules} {G : Y.left.Modules} (I : InjectiveResolution F) (J : InjectiveResolution G)
  (R : ModuleCat.{u} B ⥤ ModuleCat.{u} A) [R.Additive]
  (m : resolutionDouble U I.cocomplex ⟶ (mapNatDouble R).obj (resolutionDouble V J.cocomplex))

set_option backward.isDefEq.respectTransparency false in
private theorem rowAxis_naturality
    (g : globalComplex I ⟶ (R.mapHomologicalComplex (.up ℕ)).obj (globalComplex J))
    (h : ∀ q : ℕ, sectionAugmentation U (I.cocomplex.X q) ≫ (m.f 0).f q =
      g.f q ≫ R.map (sectionAugmentation V (J.cocomplex.X q))) :
    rowAxis U I ≫ (extendDoubleMap R m).f 0 =
      extendMapTo R g ≫ (R.mapHomologicalComplex (.up ℤ)).map (rowAxis V J) := by
  apply HomologicalComplex.hom_ext
  intro j
  by_cases hj : j < 0
  · exact ((globalComplex I).isZero_extend_X intEmbedding j
      (intEmbedding_not_negative j hj)).eq_of_src _ _
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ j)
    apply (cancel_mono (R.map (doubleComponentIso (resolutionDouble V J.cocomplex) 0 q).hom)).1
    simp only [comp_f, Functor.mapHomologicalComplex_map_f, Category.assoc]
    have hm : ((extendDoubleMap R m).f 0).f (q : ℤ) ≫
        R.map (doubleComponentIso (resolutionDouble V J.cocomplex) 0 q).hom =
      (doubleComponentIso (resolutionDouble U I.cocomplex) 0 q).hom ≫ (m.f 0).f q :=
      extendDoubleMap_f R m 0 q
    erw [hm]
    rw [rowAxis_f_assoc U I q, ← R.map_comp, rowAxis_f V J q,
      R.map_comp, extendMapTo_f_assoc, h q]

set_option backward.isDefEq.respectTransparency false in
private theorem columnAxis_naturality
    (c : SheafCech U F ⟶ (R.mapHomologicalComplex (.up ℕ)).obj (SheafCech V G))
    (h : ∀ p : ℕ, (coefficientComplexAugmentation U I).f p ≫ (m.f p).f 0 =
      c.f p ≫ R.map ((coefficientComplexAugmentation V J).f p)) :
    columnAxis U I ≫ ((HomologicalComplex₂.flipFunctor _ (.up ℤ) (.up ℤ)).map
        (extendDoubleMap R m)).f 0 =
      extendMapTo R c ≫ (R.mapHomologicalComplex (.up ℤ)).map (columnAxis V J) := by
  apply HomologicalComplex.hom_ext
  intro j
  by_cases hj : j < 0
  · exact ((SheafCech U F).isZero_extend_X intEmbedding j
      (intEmbedding_not_negative j hj)).eq_of_src _ _
  · obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ j)
    apply (cancel_mono (R.map (doubleComponentIso (resolutionDouble V J.cocomplex) p 0).hom)).1
    simp only [comp_f, HomologicalComplex₂.flipFunctor_map_f_f, Functor.mapHomologicalComplex_map_f,
      Category.assoc]
    have hm : ((extendDoubleMap R m).f (p : ℤ)).f 0 ≫
        R.map (doubleComponentIso (resolutionDouble V J.cocomplex) p 0).hom =
      (doubleComponentIso (resolutionDouble U I.cocomplex) p 0).hom ≫ (m.f p).f 0 :=
      extendDoubleMap_f R m p 0
    erw [hm]
    rw [columnAxis_f_assoc U I p, ← R.map_comp, columnAxis_f V J p,
      R.map_comp, extendMapTo_f_assoc, h p]

variable [PreservesFiniteLimits R] [PreservesFiniteColimits R]

set_option backward.isDefEq.respectTransparency false in
private theorem resolutionComparison_natural
    (M : ResolutionAugmentations U I) (N : ResolutionAugmentations V J)
    (g : globalComplex I ⟶ (R.mapHomologicalComplex (.up ℕ)).obj (globalComplex J))
    (c : SheafCech U F ⟶ (R.mapHomologicalComplex (.up ℕ)).obj (SheafCech V G))
    (hg : ∀ q : ℕ, sectionAugmentation U (I.cocomplex.X q) ≫ (m.f 0).f q =
      g.f q ≫ R.map (sectionAugmentation V (J.cocomplex.X q)))
    (hc : ∀ p : ℕ, (coefficientComplexAugmentation U I).f p ≫ (m.f p).f 0 =
      c.f p ≫ R.map ((coefficientComplexAugmentation V J).f p)) (n : ℕ) :
    (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫ homologyTo R g n ≫
      R.map (J.isoRightDerivedObj (sectionsFunctor Y) n).inv ≫
        R.map (resolutionComparison V J N n).hom =
    (resolutionComparison U I M n).hom ≫ homologyTo R c n := by
  let d := extendDoubleMap R m
  let gi := (globalComplex I).extendHomologyIso intEmbedding (intEmbedding_at n)
  let gj := (globalComplex J).extendHomologyIso intEmbedding (intEmbedding_at n)
  let ci := (SheafCech U F).extendHomologyIso intEmbedding (intEmbedding_at n)
  let cj := (SheafCech V G).extendHomologyIso intEmbedding (intEmbedding_at n)
  let i := I.isoRightDerivedObj (sectionsFunctor X) n
  let j := J.isoRightDerivedObj (sectionsFunctor Y) n
  let e := resolutionComparison U I M n
  let e' := resolutionComparison V J N n
  let a := homologyMap M.a (n : ℤ)
  let a' := homologyMap N.a (n : ℤ)
  let b := homologyMap M.b (n : ℤ)
  let b' := homologyMap N.b (n : ℤ)
  have he : e.hom ≫ ci.inv ≫ b = i.hom ≫ gi.inv ≫ a :=
    resolutionComparison_hom_comp U I M n
  have he' : e'.hom ≫ cj.inv ≫ b' = j.hom ≫ gj.inv ≫ a' :=
    resolutionComparison_hom_comp V J N n
  obtain ⟨t, ht, _⟩ := CechFirstQuadrantTotalization.totalMapExists R
    (doubleComplex U I) (doubleComplex V J) d
  have hs := CechFirstQuadrantTotalization.rowNaturality R
    (doubleComplex U I) (doubleComplex V J) d (extendMapTo R g)
    (rowAxis U I) (rowAxis V J) M.a N.a t M.row_components N.row_components ht
    (rowAxis_naturality U V I J R m g hg)
  have hr := CechFirstQuadrantTotalization.columnNaturality R
    (doubleComplex U I) (doubleComplex V J) d (extendMapTo R c)
    (columnAxis U I) (columnAxis V J) M.b N.b t M.column_components N.column_components ht
    (columnAxis_naturality U V I J R m c hc)
  have ha : a ≫ homologyTo R t (n : ℤ) =
      homologyTo R (extendMapTo R g) (n : ℤ) ≫ R.map a' :=
    homologyTo_comm R (extendMapTo R g) t M.a N.a hs _
  have hb : b ≫ homologyTo R t (n : ℤ) =
      homologyTo R (extendMapTo R c) (n : ℤ) ≫ R.map b' :=
    homologyTo_comm R (extendMapTo R c) t M.b N.b hr _
  let := N.quasiIso_b
  change i.hom ≫ homologyTo R g n ≫ R.map j.inv ≫ R.map e'.hom = e.hom ≫ homologyTo R c n
  apply (cancel_mono (R.map (cj.inv ≫ b'))).1
  calc
    _ = i.hom ≫ homologyTo R g n ≫ R.map (j.inv ≫ e'.hom ≫ cj.inv ≫ b') := by
      simp only [Functor.map_comp, Category.assoc]
    _ = i.hom ≫ homologyTo R g n ≫ R.map gj.inv ≫ R.map a' := by
      rw [he', Iso.inv_hom_id_assoc, Functor.map_comp]
    _ = i.hom ≫ gi.inv ≫ homologyTo R (extendMapTo R g) (n : ℤ) ≫ R.map a' := by
      rw [homologyTo_extend_inv_assoc]
    _ = (i.hom ≫ gi.inv ≫ a) ≫ homologyTo R t (n : ℤ) := by
      simp only [Category.assoc, ha]
    _ = (e.hom ≫ ci.inv ≫ b) ≫ homologyTo R t (n : ℤ) := by rw [he]
    _ = e.hom ≫ ci.inv ≫ homologyTo R (extendMapTo R c) (n : ℤ) ≫ R.map b' := by
      simp only [Category.assoc, hb]
    _ = _ := by
      rw [← homologyTo_extend_inv_assoc, Functor.map_comp, Category.assoc]

end Naturality

section Comparison

open HomologicalComplex

variable {A : Type u} [CommRing A] {X : SchemeOverRing A}
  {Idx : Type u} [LinearOrder Idx] (U : Idx → X.left.Opens)
  {F G : X.left.Modules} (I : InjectiveResolution F) (J : InjectiveResolution G)

set_option backward.isDefEq.respectTransparency false in
private theorem resolutionComparison_coefficients
    (M : ResolutionAugmentations U I) (N : ResolutionAugmentations U J)
    (α : F ⟶ G) (n : ℕ) :
    (cohomology X n).map α ≫ (resolutionComparison U J N n).hom =
      (resolutionComparison U I M n).hom ≫ homologyMap ((sheafCechFunctor U).map α) n := by
  let l := InjectiveResolution.desc α J I
  have hl : I.ι.f 0 ≫ l.f 0 = α ≫ J.ι.f 0 := InjectiveResolution.desc_commutes_zero α J I
  let g := ((sectionsFunctor X).mapHomologicalComplex (.up ℕ)).map l
  let c := (sheafCechFunctor U).map α
  let m : resolutionDouble U I.cocomplex ⟶ resolutionDouble U J.cocomplex :=
    (HomologicalComplex₂.flipFunctor _ (.up ℕ) (.up ℕ)).map
      (((sheafCechFunctor U).mapHomologicalComplex (.up ℕ)).map l)
  have hg (q : ℕ) : sectionAugmentation U (I.cocomplex.X q) ≫ (m.f 0).f q =
      g.f q ≫ sectionAugmentation U (J.cocomplex.X q) :=
    (sectionAugmentation_naturality U (l.f q)).symm
  have hc (p : ℕ) : (coefficientComplexAugmentation U I).f p ≫ (m.f p).f 0 =
      c.f p ≫ (coefficientComplexAugmentation U J).f p := by
    change ((sheafCechFunctor U).map (I.ι.f 0)).f p ≫ ((sheafCechFunctor U).map (l.f 0)).f p =
      ((sheafCechFunctor U).map α).f p ≫ ((sheafCechFunctor U).map (J.ι.f 0)).f p
    rw [← comp_f, ← comp_f, ← Functor.map_comp, ← Functor.map_comp, hl]
  have h := resolutionComparison_natural U U I J (𝟭 (ModuleCat.{u} A)) m M N g c hg hc n
  have hd := (sectionsFunctor X).rightDerived_map_eq n α l (InjectiveResolution.desc_commutes α J I)
  change (cohomology X n).map α =
    (I.isoRightDerivedObj (sectionsFunctor X) n).hom ≫ homologyMap g n ≫
      (J.isoRightDerivedObj (sectionsFunctor X) n).inv at hd
  simpa only [CategoryTheory.Functor.id_map, homologyTo_id, hd, Category.assoc] using h

private theorem resolutionComparison_independent (J : InjectiveResolution F)
    (M : ResolutionAugmentations U I) (N : ResolutionAugmentations U J) (n : ℕ) :
    resolutionComparison U I M n = resolutionComparison U J N n := by
  apply Iso.ext
  have h := resolutionComparison_coefficients U I J M N (𝟙 F) n
  simp only [CategoryTheory.Functor.map_id, homologyMap_id, Category.id_comp] at h
  change (resolutionComparison U J N n).hom =
    (resolutionComparison U I M n).hom ≫ 𝟙 ((SheafCech U F).homology n) at h
  rw [Category.comp_id] at h
  exact h.symm

end Comparison

section ComparisonPullback

open HomologicalComplex

variable {A B : Type u} [CommRing A] [CommRing B] {X : SchemeOverRing A} {Y : SchemeOverRing B}
  {Idx : Type u} [LinearOrder Idx] (U : Idx → X.left.Opens)
  (φ : A →+* B) (f : Y.left ⟶ X.left)
  (hf : f ≫ X.hom = Y.hom ≫ Spec.map (CommRingCat.ofHom φ))
  {F : X.left.Modules} {G : Y.left.Modules} (α : F ⟶ (Scheme.Modules.pushforward f).obj G)
  (I : InjectiveResolution F) (J : InjectiveResolution G)

private theorem resolutionComparison_pullback
    (M : ResolutionAugmentations U I) (N : ResolutionAugmentations (pullbackCover f U) J)
    (l : I.cocomplex ⟶ ((Scheme.Modules.pushforward f).mapHomologicalComplex _).obj J.cocomplex)
    (hl : I.ι.f 0 ≫ l.f 0 = α ≫ (Scheme.Modules.pushforward f).map (J.ι.f 0)) (n : ℕ) :
    let R := ModuleCat.restrictScalars.{u} φ
    let V := pullbackCover f U
    derivedMapOfLift φ f hf I J l n ≫ R.map (resolutionComparison V J N n).hom =
      (resolutionComparison U I M n).hom ≫ homologyMap (cechPullback φ f hf U α) n ≫
        (restrictCohomologyIso φ (SheafCech V G) n).inv := by
  let R := ModuleCat.restrictScalars.{u} φ
  let V := pullbackCover f U
  let m := resolutionDoublePullback φ f hf U I.cocomplex J.cocomplex l
  let g := sectionsComplexPullback φ f hf l
  let c := cechPullback φ f hf U α
  have h := resolutionComparison_natural U V I J R m M N g c
    (resolutionDoublePullback_comm_row φ f hf U I.cocomplex J.cocomplex l)
    (resolutionDoublePullback_comm_column φ f hf U α I J l hl) n
  simp only [derivedMapOfLift, homologyTo, restrictCohomologyIso] at h ⊢
  exact h

end ComparisonPullback

open HomologicalComplex

/-- The canonical comparison for a finite ordered acyclic cover. -/
def orderedCechComparisonIso
    {A : Type u} [CommRing A] (X : SchemeOverRing A)
    {Idx : Type u} [LinearOrder Idx] [Fintype Idx] (U : Idx → X.left.Opens)
    (hU : (⨆ i, U i) = ⊤) (F : X.left.Modules) (hF : IntersectionAcyclic U F) (n : ℕ) :
    (cohomology X n).obj F ≅ (SheafCech U F).homology n :=
  let I := injectiveResolution F
  resolutionComparison U I (resolutionAugmentations U I hU hF) n

private theorem orderedCechComparisonIso_eq
    {A : Type u} [CommRing A] (X : SchemeOverRing A)
    {Idx : Type u} [LinearOrder Idx] [Fintype Idx] (U : Idx → X.left.Opens)
    (hU : (⨆ i, U i) = ⊤) (F : X.left.Modules) (hF : IntersectionAcyclic U F)
    (I : InjectiveResolution F) (n : ℕ) :
    orderedCechComparisonIso X U hU F hF n =
      resolutionComparison U I (resolutionAugmentations U I hU hF) n :=
  resolutionComparison_independent U (injectiveResolution F) I
    (resolutionAugmentations U (injectiveResolution F) hU hF) (resolutionAugmentations U I hU hF) n

/-- The ordered Čech comparison is computed on every resolution and is
natural for both coefficient maps and pullback with a compatible cochain lift. -/
theorem orderedCechComparison : Comparison.{u} := by
  refine ⟨orderedCechComparisonIso, ?_, ?_, ?_⟩
  · intro A _ X Idx _ _ U hU F hF I n
    change IsComparisonFromResolution U I n (orderedCechComparisonIso X U hU F hF n)
    rw [orderedCechComparisonIso_eq X U hU F hF I n]
    exact resolutionComparison_spec U I (resolutionAugmentations U I hU hF) n
  · intro A _ X Idx _ _ U hU F G α hF hG n
    let I := injectiveResolution F
    let J := injectiveResolution G
    exact resolutionComparison_coefficients U I J
      (resolutionAugmentations U I hU hF) (resolutionAugmentations U J hU hG) α n
  · intro A B _ _ X Y Idx _ _ U hU φ f hf F G α hF hG I J l hl n
    dsimp only
    rw [orderedCechComparisonIso_eq X U hU F hF I n,
      orderedCechComparisonIso_eq Y (pullbackCover f U) (f.iSup_preimage_eq_top hU) G hG J n]
    exact resolutionComparison_pullback U φ f hf α I J (resolutionAugmentations U I hU hF)
      (resolutionAugmentations (pullbackCover f U) J (f.iSup_preimage_eq_top hU) hG) l hl n

/-- In degrees at least the size of the cover, every ordered cochain is zero. -/
theorem isZero_cohomology_of_card_le
    {A : Type u} [CommRing A] {X : SchemeOverRing A}
    {Idx : Type u} [LinearOrder Idx] [Fintype Idx] (U : Idx → X.left.Opens)
    (hU : (⨆ i, U i) = ⊤) (F : X.left.Modules) (hF : IntersectionAcyclic U F)
    (n : ℕ) (hn : Fintype.card Idx ≤ n) : IsZero ((cohomology X n).obj F) :=
  (isZero_sheafCech_homology_of_card_le U F n hn).of_iso (orderedCechComparisonIso X U hU F hF n)

end LinearAlgebraicGroups.OrderedCechComparison
