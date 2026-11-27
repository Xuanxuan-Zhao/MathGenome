import MathGenome.Internal.HomologicalAlgebraDeepening.DerivedFormalization.Cochains
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainCoefficientLift
import Mathlib.Algebra.Category.Grp.Ulift
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! Coefficient-universe lifts of ordinary complexes over the original ring. -/

namespace DerivedFormalization.CochainCoefficientLift

open CategoryTheory CategoryTheory.Limits

universe t v u s w j k

variable {R : Type u} [Ring R]

noncomputable section

attribute [local instance] HasDerivedCategory.standard

/-- Apply the module universe lift to each term, over the same ring. -/
abbrev lift (R : Type u) [Ring R] : Comp.{v} R ⥤ Comp.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapHomologicalComplex (.up ℤ)

/-- The original module and the lifted carrier are linearly equivalent by `ULift.up`. -/
def termEquiv (X : Comp.{v} R) (i : ℤ) : X.X i ≃ₗ[R] ((lift.{t} R).obj X).X i :=
  ULift.moduleEquiv.symm

theorem termEquiv_apply (X : Comp.{v} R) (i : ℤ) (x : X.X i) :
    termEquiv.{t} X i x = ULift.up x := rfl

theorem termEquiv_symm_apply (X : Comp.{v} R) (i : ℤ) (x : ((lift.{t} R).obj X).X i) :
    (termEquiv.{t} X i).symm x = x.down := rfl

theorem lift_smul (X : Comp.{v} R) (i : ℤ) (r : R) (x : X.X i) :
    r • termEquiv.{t} X i x = termEquiv.{t} X i (r • x) := rfl

theorem lift_d (X : Comp.{v} R) (i j : ℤ) (x : X.X i) :
    ((lift.{t} R).obj X).d i j (termEquiv.{t} X i x) =
      termEquiv.{t} X j (X.d i j x) := rfl

theorem lift_f {X Y : Comp.{v} R} (f : X ⟶ Y) (i : ℤ) (x : X.X i) :
    ((lift.{t} R).map f).f i (termEquiv.{t} X i x) =
      termEquiv.{t} Y i (f.f i x) := rfl

/-- Lift the components of a chain homotopy by the same up/down formulas. -/
def liftHomotopy {X Y : Comp.{v} R} {f g : X ⟶ Y} (h : Homotopy f g) :
    Homotopy ((lift.{t} R).map f) ((lift.{t} R).map g) :=
  (ModuleCat.uliftFunctor.{t, v} R).mapHomotopy h

theorem liftHomotopy_hom {X Y : Comp.{v} R} {f g : X ⟶ Y}
    (h : Homotopy f g) (i j : ℤ) (x : X.X i) :
    (liftHomotopy.{t} h).hom i j (termEquiv.{t} X i x) =
      termEquiv.{t} Y j (h.hom i j x) := rfl

/-- The term lift is fully faithful on cochain maps. -/
def fullyFaithful (R : Type u) [Ring R] : (lift.{t, v} R).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful (lift.{t, v} R)

/-- The functor on cochain homotopy categories induced by the term lift. -/
def liftK (R : Type u) [Ring R] : K.{v} R ⥤ K.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapHomotopyCategory (.up ℤ)

def liftKFactors (R : Type u) [Ring R] :
    homotopyQuotient.{v} R ⋙ liftK.{t, v} R ≅
      lift.{t, v} R ⋙ homotopyQuotient.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapHomotopyCategoryFactors (.up ℤ)

def fullyFaithfulK (R : Type u) [Ring R] : (liftK.{t, v} R).FullyFaithful :=
  Functor.FullyFaithful.ofFullyFaithful
    ((ModuleCat.uliftFunctor.{t, v} R).mapHomotopyCategory (.up ℤ))

/-- The degreewise lift commutes with the signed cochain shift. -/
def shiftIso (R : Type u) [Ring R] (n : ℤ) :
    cochainShift.{v} R n ⋙ lift.{t, v} R ≅ lift.{t, v} R ⋙ cochainShift.{max v t} R n :=
  (ModuleCat.uliftFunctor.{t, v} R).mapCochainComplexShiftIso n

/-- The canonical comparison with the cone of the lifted morphism. -/
def coneIso {X Y : Comp.{v} R} (f : X ⟶ Y) :
    (lift.{t} R).obj (CochainComplex.mappingCone f) ≅
      CochainComplex.mappingCone ((lift.{t} R).map f) :=
  CochainComplex.mappingCone.mapHomologicalComplexIso f (ModuleCat.uliftFunctor.{t, v} R)

private theorem forgetModulePreservesLimits (R : Type u) [Ring R]
    (J : Type j) [Category.{k} J] [Small.{v} J] :
    PreservesLimitsOfShape J (forget₂ (ModuleCat.{v} R) AddCommGrpCat) where
  preservesLimit := ModuleCat.forget₂AddCommGroup_preservesLimit _

private theorem moduleLiftPreservesLimits (R : Type u) [Ring R]
    (J : Type j) [Category.{k} J] [Small.{v} J] :
    PreservesLimitsOfShape J (ModuleCat.uliftFunctor.{t, v} R) := by
  let _ := forgetModulePreservesLimits.{v} R J
  let : PreservesLimitsOfShape J (ModuleCat.uliftFunctor.{t, v} R ⋙
      forget₂ _ AddCommGrpCat) := by
    change PreservesLimitsOfShape J
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{t, v})
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves
    (ModuleCat.uliftFunctor.{t, v} R) (forget₂ _ AddCommGrpCat)

/-- The lift preserves limits of module-small shapes, including countable towers. -/
theorem preservesLimits (R : Type u) [Ring R]
    (J : Type j) [Category.{k} J] [Small.{v} J] :
    PreservesLimitsOfShape J (lift.{t, v} R) := by
  let := ModuleCat.hasLimitsOfShape (R := R) (J := J)
  let := moduleLiftPreservesLimits.{t, v} R J
  infer_instance

private theorem moduleLiftPreservesColimits (R : Type u) [Ring R]
    (J : Type j) [Category.{k} J] [Small.{v} J] :
    PreservesColimitsOfShape J (ModuleCat.uliftFunctor.{t, v} R) := by
  let : Small.{max v t} J := small_lift.{j, t} J
  let : PreservesColimitsOfShape J (ModuleCat.uliftFunctor.{t, v} R ⋙
      forget₂ _ AddCommGrpCat) := by
    change PreservesColimitsOfShape J
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat ⋙ AddCommGrpCat.uliftFunctor.{t, v})
    infer_instance
  exact preservesColimitsOfShape_of_reflects_of_preserves
    (ModuleCat.uliftFunctor.{t, v} R) (forget₂ _ AddCommGrpCat)

/-- The lift preserves colimits of module-small shapes, including sums and sequential colimits. -/
theorem preservesColimits (R : Type u) [Ring R]
    (J : Type j) [Category.{k} J] [Small.{v} J] :
    PreservesColimitsOfShape J (lift.{t, v} R) := by
  let := moduleLiftPreservesColimits.{t, v} R J
  infer_instance

/-- The lift on the localization of the original cochain category. -/
def liftD (R : Type u) [Ring R] : D.{v} R ⥤ D.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapDerivedCategory

def liftDFactors (R : Type u) [Ring R] :
    Q.{v} R ⋙ liftD.{t, v} R ≅ lift.{t, v} R ⋙ Q.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapDerivedCategoryFactors

/-- The lift also factors against localization of the homotopy category. -/
def liftDFactorsh (R : Type u) [Ring R] :
    Qh.{v} R ⋙ liftD.{t, v} R ≅ liftK.{t, v} R ⋙ Qh.{max v t} R :=
  (ModuleCat.uliftFunctor.{t, v} R).mapDerivedCategoryFactorsh

/-- Comparison with the lift of the actual chosen cycle object. -/
def cyclesIso (R : Type u) [Ring R] (i : ℤ) :
    lift.{t, v} R ⋙ HomologicalComplex.cyclesFunctor (ModuleCat.{max v t} R) (.up ℤ) i ≅
      HomologicalComplex.cyclesFunctor (ModuleCat.{v} R) (.up ℤ) i ⋙
        ModuleCat.uliftFunctor.{t, v} R :=
  Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ _ i)
    (ShortComplex.cyclesFunctorIso (ModuleCat.uliftFunctor.{t, v} R))

/-- Comparison with the lift of the actual cohomology functor. -/
def cohomologyIso (R : Type u) [Ring R] (i : ℤ) :
    lift.{t, v} R ⋙ cohomologyFunctor.{max v t} R i ≅
      cohomologyFunctor.{v} R i ⋙ ModuleCat.uliftFunctor.{t, v} R :=
  Functor.isoWhiskerLeft (HomologicalComplex.shortComplexFunctor _ _ i)
    (ShortComplex.homologyFunctorIso (ModuleCat.uliftFunctor.{t, v} R))

def cyclesEquiv (X : Comp.{v} R) (i : ℤ) :
    X.cycles i ≃ₗ[R] ((lift.{t} R).obj X).cycles i :=
  ULift.moduleEquiv.symm.trans (((cyclesIso.{t} R i).app X).symm.toLinearEquiv)

def cohomologyEquiv (X : Comp.{v} R) (i : ℤ) :
    X.homology i ≃ₗ[R] ((lift.{t} R).obj X).homology i :=
  ULift.moduleEquiv.symm.trans (((cohomologyIso.{t} R i).app X).symm.toLinearEquiv)

theorem cyclesEquiv_iCycles (X : Comp.{v} R) (i : ℤ) (x : X.cycles i) :
    ((lift.{t} R).obj X).iCycles i (cyclesEquiv.{t} X i x) =
      termEquiv.{t} X i (X.iCycles i x) := by
  have h := (X.sc i).mapCyclesIso_hom_iCycles (ModuleCat.uliftFunctor.{t, v} R)
  have h' := congrArg (fun f => ((X.sc i).mapCyclesIso (ModuleCat.uliftFunctor.{t, v} R)).inv ≫ f) h
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at h'
  exact (congrArg (fun f => f (ULift.up x)) (ModuleCat.hom_ext_iff.mp h')).symm

theorem quasiIso_iff {X Y : Comp.{v} R} (f : X ⟶ Y) :
    QuasiIso ((lift.{t} R).map f) ↔ QuasiIso f :=
  HomologicalComplex.quasiIso_map_iff_of_preservesHomology f (ModuleCat.uliftFunctor.{t, v} R)

theorem acyclic_iff (X : Comp.{v} R) :
    ((lift.{t} R).obj X).Acyclic ↔ X.Acyclic := by
  simp only [HomologicalComplex.acyclic_iff]
  apply forall_congr'
  intro i
  simp only [HomologicalComplex.exactAt_iff_isZero_homology]
  change IsZero ((lift.{t, v} R ⋙ cohomologyFunctor.{max v t} R i).obj X) ↔ _
  rw [((cohomologyIso.{t} R i).app X).isZero_iff]
  let F := ModuleCat.uliftFunctor.{t, v} R
  change IsZero (F.obj (X.homology i)) ↔ IsZero (X.homology i)
  rw [IsZero.iff_id_eq_zero, IsZero.iff_id_eq_zero, ← F.map_id, ← F.map_zero]
  exact ⟨fun h => F.map_injective h, congrArg F.map⟩

theorem injective_iff {X Y : Comp.{v} R} (f : X ⟶ Y) (i : ℤ) :
    Function.Injective (((lift.{t} R).map f).f i) ↔ Function.Injective (f.f i) := by
  have eq : (((lift.{t} R).map f).f i) ∘ termEquiv.{t} X i =
      termEquiv.{t} Y i ∘ f.f i := rfl
  rw [← Function.Injective.of_comp_iff' _ (termEquiv.{t} X i).bijective, eq,
    (termEquiv.{t} Y i).injective.of_comp_iff]

theorem surjective_iff {X Y : Comp.{v} R} (f : X ⟶ Y) (i : ℤ) :
    Function.Surjective (((lift.{t} R).map f).f i) ↔ Function.Surjective (f.f i) := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := h (termEquiv.{t} Y i y)
    exact ⟨x.down, ULift.up_injective hx⟩
  · intro h y
    obtain ⟨x, hx⟩ := h y.down
    exact ⟨ULift.up x, congrArg ULift.up hx⟩

theorem mono_iff {X Y : Comp.{v} R} (f : X ⟶ Y) (i : ℤ) :
    Mono (((lift.{t} R).map f).f i) ↔ Mono (f.f i) := by
  simp only [ModuleCat.mono_iff_injective, injective_iff]

/-- Transport of the boundary submodule in the middle term by the term equivalence. -/
theorem map_boundary (X : Comp.{v} R) (i : ℤ) :
    (LinearMap.range (X.d ((ComplexShape.up ℤ).prev i) i).hom).map
        (termEquiv.{t} X i).toLinearMap =
      LinearMap.range (((lift.{t} R).obj X).d ((ComplexShape.up ℤ).prev i) i).hom := by
  ext z
  simp only [Submodule.mem_map, LinearMap.mem_range]
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨ULift.up x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨x.down, rfl⟩, rfl⟩

/-- The boundary equivalence is the restriction of `ULift.up` to the image of the differential. -/
def boundariesEquiv (X : Comp.{v} R) (i : ℤ) :
    LinearMap.range (X.d ((ComplexShape.up ℤ).prev i) i).hom ≃ₗ[R]
      LinearMap.range (((lift.{t} R).obj X).d ((ComplexShape.up ℤ).prev i) i).hom :=
  (termEquiv.{t} X i).ofSubmodules _ _ (map_boundary.{t} X i)

theorem boundariesEquiv_apply (X : Comp.{v} R) (i : ℤ)
    (x : LinearMap.range (X.d ((ComplexShape.up ℤ).prev i) i).hom) :
    (boundariesEquiv.{t} X i x).val = termEquiv.{t} X i x.val := rfl

set_option backward.isDefEq.respectTransparency false in
private theorem cohomologyComparison_homologyπ (X : Comp.{v} R) (i : ℤ) :
    let F := ModuleCat.uliftFunctor.{t, v} R
    let S := X.sc i
    F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
      (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ := by
  dsimp only
  let F := ModuleCat.uliftFunctor.{t, v} R
  let S := X.sc i
  let h := S.homologyData.left
  change F.map S.homologyπ ≫ (S.mapHomologyIso F).inv =
    (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ
  rw [h.mapHomologyIso_eq F, h.mapCyclesIso_eq F]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv, Category.assoc,
    ← Functor.map_comp_assoc]
  rw [h.homologyπ_comp_homologyIso_hom, Functor.map_comp, Category.assoc]
  exact congrArg (F.map h.cyclesIso.hom ≫ ·) (h.map F).π_comp_homologyIso_inv

theorem cohomologyEquiv_homologyπ (X : Comp.{v} R) (i : ℤ) (x : X.cycles i) :
    cohomologyEquiv.{t} X i (X.homologyπ i x) =
      ((lift.{t} R).obj X).homologyπ i (cyclesEquiv.{t} X i x) := by
  exact congrArg (fun f => f (ULift.up x))
    (ModuleCat.hom_ext_iff.mp (cohomologyComparison_homologyπ.{t} X i))

/-- A chain map written with linear maps between terms in possibly different universes. -/
abbrev MixedHom (X : Comp.{v} R) (Y : Comp.{w} R) :=
  Specs.DerivedFormalization.CochainCoefficientLift.MixedHom X Y

/-- Read a map out of the lift as a mixed map, by precomposing with `up`. -/
def fromOriginal {X : Comp.{v} R} {Y : Comp.{max v t} R}
    (f : (lift.{t} R).obj X ⟶ Y) : MixedHom X Y where
  f i := (f.f i).hom.comp (termEquiv.{t} X i).toLinearMap
  comm i j x :=
    congrArg (fun g => g (termEquiv.{t} X i x)) (ModuleCat.hom_ext_iff.mp (f.comm i j))

/-- Read a map into the lift as a mixed map, by postcomposing with `down`. -/
def toOriginal {X : Comp.{max v t} R} {Y : Comp.{v} R}
    (f : X ⟶ (lift.{t} R).obj Y) : MixedHom X Y where
  f i := (termEquiv.{t} Y i).symm.toLinearMap.comp (f.f i).hom
  comm i j x :=
    congrArg ULift.down (congrArg (fun g => g x) (ModuleCat.hom_ext_iff.mp (f.comm i j)))

/-- Write a mixed map out of the original complex as a map out of its lift. -/
def fromOriginalEquiv {X : Comp.{v} R} {Y : Comp.{max v t} R} :
    ((lift.{t} R).obj X ⟶ Y) ≃ MixedHom X Y where
  toFun := fromOriginal
  invFun f :=
    { f := fun i => ModuleCat.ofHom ((f.f i).comp (termEquiv.{t} X i).symm.toLinearMap)
      comm' := fun i j _ => by
        apply ModuleCat.hom_ext
        ext x
        exact f.comm i j x.down }
  left_inv f := by ext i x; rfl
  right_inv := by rintro ⟨f, h⟩; rfl

/-- Write a mixed map into the original complex as a map into its lift. -/
def toOriginalEquiv {X : Comp.{max v t} R} {Y : Comp.{v} R} :
    (X ⟶ (lift.{t} R).obj Y) ≃ MixedHom X Y where
  toFun := toOriginal
  invFun f :=
    { f := fun i => ModuleCat.ofHom ((termEquiv.{t} Y i).toLinearMap.comp (f.f i))
      comm' := fun i j _ => by
        apply ModuleCat.hom_ext
        ext x
        exact congrArg ULift.up (f.comm i j x) }
  left_inv f := by ext i x; rfl
  right_inv := by rintro ⟨f, h⟩; rfl

theorem fromOriginal_injective {X : Comp.{v} R} {Y : Comp.{max v t} R}
    (f : (lift.{t} R).obj X ⟶ Y) (i : ℤ) :
    Function.Injective ((fromOriginal.{t} f).f i) ↔ Mono (f.f i) := by
  rw [ModuleCat.mono_iff_injective]
  exact Function.Injective.of_comp_iff' _ (termEquiv.{t} X i).bijective

theorem fromOriginal_surjective {X : Comp.{v} R} {Y : Comp.{max v t} R}
    (f : (lift.{t} R).obj X ⟶ Y) (i : ℤ) :
    Function.Surjective ((fromOriginal.{t} f).f i) ↔ Function.Surjective (f.f i) :=
  Function.Surjective.of_comp_iff _ (termEquiv.{t} X i).surjective

theorem toOriginal_injective {X : Comp.{max v t} R} {Y : Comp.{v} R}
    (f : X ⟶ (lift.{t} R).obj Y) (i : ℤ) :
    Function.Injective ((toOriginal.{t} f).f i) ↔ Mono (f.f i) := by
  rw [ModuleCat.mono_iff_injective]
  exact (termEquiv.{t} Y i).symm.injective.of_comp_iff _

theorem toOriginal_surjective {X : Comp.{max v t} R} {Y : Comp.{v} R}
    (f : X ⟶ (lift.{t} R).obj Y) (i : ℤ) :
    Function.Surjective ((toOriginal.{t} f).f i) ↔ Function.Surjective (f.f i) :=
  Function.Surjective.of_comp_iff' (termEquiv.{t} Y i).symm.bijective _

/-- The map on cycles of a map from an original complex to a larger one. -/
def fromOriginalCycles {X : Comp.{v} R} {Y : Comp.{max v t} R}
    (f : (lift.{t} R).obj X ⟶ Y) (i : ℤ) : X.cycles i →ₗ[R] Y.cycles i :=
  (HomologicalComplex.cyclesMap f i).hom.comp (cyclesEquiv.{t} X i).toLinearMap

/-- The map on cycles of a map from a larger complex to an original one. -/
def toOriginalCycles {X : Comp.{max v t} R} {Y : Comp.{v} R}
    (f : X ⟶ (lift.{t} R).obj Y) (i : ℤ) : X.cycles i →ₗ[R] Y.cycles i :=
  (cyclesEquiv.{t} Y i).symm.toLinearMap.comp (HomologicalComplex.cyclesMap f i).hom

/-- The map on actual cohomology of a map from an original complex to a larger one. -/
def fromOriginalCohomology {X : Comp.{v} R} {Y : Comp.{max v t} R}
    (f : (lift.{t} R).obj X ⟶ Y) (i : ℤ) : X.homology i →ₗ[R] Y.homology i :=
  (HomologicalComplex.homologyMap f i).hom.comp (cohomologyEquiv.{t} X i).toLinearMap

/-- The map on actual cohomology of a map from a larger complex to an original one. -/
def toOriginalCohomology {X : Comp.{max v t} R} {Y : Comp.{v} R}
    (f : X ⟶ (lift.{t} R).obj Y) (i : ℤ) : X.homology i →ₗ[R] Y.homology i :=
  (cohomologyEquiv.{t} Y i).symm.toLinearMap.comp (HomologicalComplex.homologyMap f i).hom

theorem fromOriginalCycles_iCycles {X : Comp.{v} R} {Y : Comp.{max v t} R}
    (f : (lift.{t} R).obj X ⟶ Y) (i : ℤ) (x : X.cycles i) :
    Y.iCycles i (fromOriginalCycles.{t} f i x) =
      (fromOriginal.{t} f).f i (X.iCycles i x) := by
  have h := HomologicalComplex.cyclesMap_i f i
  change Y.iCycles i (HomologicalComplex.cyclesMap f i (cyclesEquiv.{t} X i x)) =
    f.f i (termEquiv.{t} X i (X.iCycles i x))
  rw [← cyclesEquiv_iCycles]
  exact congrArg (fun g => g (cyclesEquiv.{t} X i x)) h

theorem toOriginalCycles_iCycles {X : Comp.{max v t} R} {Y : Comp.{v} R}
    (f : X ⟶ (lift.{t} R).obj Y) (i : ℤ) (x : X.cycles i) :
    Y.iCycles i (toOriginalCycles.{t} f i x) =
      (toOriginal.{t} f).f i (X.iCycles i x) := by
  apply (termEquiv.{t} Y i).injective
  rw [← cyclesEquiv_iCycles]
  change ((lift.{t} R).obj Y).iCycles i
      (cyclesEquiv.{t} Y i ((cyclesEquiv.{t} Y i).symm (HomologicalComplex.cyclesMap f i x))) =
    termEquiv.{t} Y i ((termEquiv.{t} Y i).symm (f.f i (X.iCycles i x)))
  simp only [LinearEquiv.apply_symm_apply]
  exact congrArg (fun g => g x) (HomologicalComplex.cyclesMap_i f i)

theorem fromOriginalCohomology_homologyπ {X : Comp.{v} R} {Y : Comp.{max v t} R}
    (f : (lift.{t} R).obj X ⟶ Y) (i : ℤ) (x : X.cycles i) :
    fromOriginalCohomology.{t} f i (X.homologyπ i x) =
      Y.homologyπ i (fromOriginalCycles.{t} f i x) := by
  change HomologicalComplex.homologyMap f i (cohomologyEquiv.{t} X i (X.homologyπ i x)) =
    Y.homologyπ i (HomologicalComplex.cyclesMap f i (cyclesEquiv.{t} X i x))
  rw [cohomologyEquiv_homologyπ]
  exact congrArg (fun g => g (cyclesEquiv.{t} X i x))
    (HomologicalComplex.homologyπ_naturality f i)

theorem toOriginalCohomology_homologyπ {X : Comp.{max v t} R} {Y : Comp.{v} R}
    (f : X ⟶ (lift.{t} R).obj Y) (i : ℤ) (x : X.cycles i) :
    toOriginalCohomology.{t} f i (X.homologyπ i x) =
      Y.homologyπ i (toOriginalCycles.{t} f i x) := by
  apply (cohomologyEquiv.{t} Y i).injective
  rw [cohomologyEquiv_homologyπ]
  change cohomologyEquiv.{t} Y i
      ((cohomologyEquiv.{t} Y i).symm (HomologicalComplex.homologyMap f i (X.homologyπ i x))) =
    ((lift.{t} R).obj Y).homologyπ i
      (cyclesEquiv.{t} Y i ((cyclesEquiv.{t} Y i).symm (HomologicalComplex.cyclesMap f i x)))
  simp only [LinearEquiv.apply_symm_apply]
  exact congrArg (fun g => g x) (HomologicalComplex.homologyπ_naturality f i)

/-- The module map on cohomology of a quasi-isomorphism is bijective on original coefficients. -/
theorem fromOriginal_quasiIso_iff {X : Comp.{v} R} {Y : Comp.{max v t} R}
    (f : (lift.{t} R).obj X ⟶ Y) :
    QuasiIso f ↔ ∀ i, Function.Bijective (fromOriginalCohomology.{t} f i) := by
  rw [_root_.quasiIso_iff]
  apply forall_congr'
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact (Function.Bijective.of_comp_iff _ (cohomologyEquiv.{t} X i).bijective).symm

theorem toOriginal_quasiIso_iff {X : Comp.{max v t} R} {Y : Comp.{v} R}
    (f : X ⟶ (lift.{t} R).obj Y) :
    QuasiIso f ↔ ∀ i, Function.Bijective (toOriginalCohomology.{t} f i) := by
  rw [_root_.quasiIso_iff]
  apply forall_congr'
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact (Function.Bijective.of_comp_iff' (cohomologyEquiv.{t} Y i).symm.bijective _).symm

/-- The repeated lift is identified with the single lift by collapsing the two wrappers. -/
def compIso (R : Type u) [Ring R] :
    lift.{t, v} R ⋙ lift.{s, max v t} R ≅ lift.{max t s, v} R :=
  Functor.mapHomologicalComplexCompIso
    (NatIso.ofComponents
      (fun M : ModuleCat.{v} R =>
        let first : M ≃ₗ[R] ((ModuleCat.uliftFunctor.{t, v} R).obj M : Type _) :=
          ULift.moduleEquiv.symm
        let second : ((ModuleCat.uliftFunctor.{t, v} R).obj M : Type _) ≃ₗ[R]
            ((ModuleCat.uliftFunctor.{t, v} R ⋙
              ModuleCat.uliftFunctor.{s, max v t} R).obj M : Type _) := ULift.moduleEquiv.symm
        let single : M ≃ₗ[R] ((ModuleCat.uliftFunctor.{max t s, v} R).obj M : Type _) :=
          ULift.moduleEquiv.symm
        ((first.trans second).symm.trans single).toModuleIso)
      (fun _ => by ext; rfl)) (.up ℤ)

/-- Lifting within the same coefficient universe is naturally isomorphic to the identity. -/
def sameLevelIso (R : Type u) [Ring R] : lift.{v, v} R ≅ 𝟭 (Comp.{v} R) :=
  let e : ModuleCat.uliftFunctor.{v, v} R ≅ 𝟭 (ModuleCat.{v} R) :=
    NatIso.ofComponents
      (fun M : ModuleCat.{v} R =>
        (ULift.moduleEquiv : ((ModuleCat.uliftFunctor.{v, v} R).obj M : Type v) ≃ₗ[R]
          M).toModuleIso)
      (fun _ => by ext; rfl)
  NatIso.mapHomologicalComplex e (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso (ModuleCat.{v} R) (ComplexShape.up ℤ)

/-- Coefficient lift commutes with restriction along the given ring map. -/
def restrictScalarsIso {S : Type s} [Ring S] (a : R →+* S) :
    (ModuleCat.restrictScalars.{v} a).mapHomologicalComplex (.up ℤ) ⋙ lift.{t, v} R ≅
      lift.{t, v} S ⋙ (ModuleCat.restrictScalars.{max v t} a).mapHomologicalComplex (.up ℤ) :=
  Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso
      (Iso.refl (ModuleCat.restrictScalars.{v} a ⋙ ModuleCat.uliftFunctor.{t, v} R))
      (.up ℤ)).symm

/-- On terms the repeated lift comparison collapses the intermediate wrapper. -/
theorem compIso_apply (X : Comp.{v} R) (i : ℤ)
    (x : (((lift.{t, v} R) ⋙ lift.{s, max v t} R).obj X).X i) :
    ((compIso.{t, v, u, s} R).hom.app X).f i x = ULift.up x.down.down := rfl

/-- At the original level the comparison is down on each term. -/
theorem sameLevelIso_apply (X : Comp.{v} R) (i : ℤ)
    (x : ((lift.{v, v} R).obj X).X i) :
    ((sameLevelIso.{v} R).hom.app X).f i x = x.down := rfl

/-- Both orders of lift and restriction have the same elements and scalar action. -/
theorem restrictScalarsIso_apply {S : Type s} [Ring S] (a : R →+* S)
    (X : Comp.{v} S) (i : ℤ) (x : X.X i) :
    ((restrictScalarsIso.{t, v} a).hom.app X).f i (ULift.up x) = ULift.up x := rfl

/-- Restriction uses the original action through the given ring homomorphism on every lifted term. -/
theorem restrictScalars_smul {S : Type s} [Ring S] (a : R →+* S)
    (X : Comp.{v} S) (i : ℤ) (r : R) (x : X.X i) :
    let M := ((lift.{t, v} S ⋙
      (ModuleCat.restrictScalars.{max v t} a).mapHomologicalComplex (.up ℤ)).obj X).X i
    @SMul.smul R M (inferInstanceAs (SMul R M)) r (ULift.up x) = ULift.up (a r • x) := rfl

end

end DerivedFormalization.CochainCoefficientLift
