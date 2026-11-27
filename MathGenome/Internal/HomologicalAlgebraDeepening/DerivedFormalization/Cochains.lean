import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! The ordinary cochain and derived categories of left modules over a unital ring. -/

namespace DerivedFormalization

open CategoryTheory CategoryTheory.Limits

universe v u

variable (R : Type u) [Ring R]

/-- Unbounded cochain complexes of left modules. -/
abbrev Comp.{v', u'} (R : Type u') [Ring R] := CochainComplex (ModuleCat.{v'} R) ℤ

/-- The ordinary cochain homotopy category. -/
abbrev K.{v', u'} (R : Type u') [Ring R] := HomotopyCategory (ModuleCat.{v'} R) (.up ℤ)

attribute [local instance] HasDerivedCategory.standard

/-- The standard localization at quasi-isomorphisms. -/
abbrev D.{v', u'} (R : Type u') [Ring R] := DerivedCategory (ModuleCat.{v'} R)

noncomputable section

/-- The cochain localization functor. -/
abbrev Q : Comp.{v} R ⥤ D.{v} R := DerivedCategory.Q

/-- The localization functor out of the cochain homotopy category. -/
abbrev Qh : K.{v} R ⥤ D.{v} R := DerivedCategory.Qh

/-- Passage to cochain homotopy classes. -/
abbrev homotopyQuotient : Comp.{v} R ⥤ K.{v} R :=
  HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)

theorem Q_isLocalization :
    (Q.{v} R).IsLocalization (HomologicalComplex.quasiIso (ModuleCat.{v} R) (.up ℤ)) :=
  inferInstance

theorem Qh_isLocalization :
    (Qh.{v} R).IsLocalization (HomotopyCategory.quasiIso (ModuleCat.{v} R) (.up ℤ)) :=
  inferInstance

/-- The cochain localization factors through the homotopy quotient. -/
def homotopyQuotientCompQhIso : homotopyQuotient.{v} R ⋙ Qh.{v} R ≅ Q.{v} R :=
  DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)

theorem comp_hasLimits : HasLimits (Comp.{v} R) :=
  ⟨fun _ _ => inferInstance⟩

theorem comp_hasColimits : HasColimits (Comp.{v} R) :=
  ⟨fun _ _ => inferInstance⟩

theorem eval_preservesLimits (i : ℤ) :
    PreservesLimits (HomologicalComplex.eval (ModuleCat.{v} R) (.up ℤ) i) where
  preservesLimitsOfShape := by intros; infer_instance

theorem eval_preservesColimits (i : ℤ) :
    PreservesColimits (HomologicalComplex.eval (ModuleCat.{v} R) (.up ℤ) i) where
  preservesColimitsOfShape := by intros; infer_instance

/-- Cohomology in degree `i` of an ordinary cochain complex. -/
abbrev cohomologyFunctor (i : ℤ) : Comp.{v} R ⥤ ModuleCat.{v} R :=
  HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.up ℤ) i

/-- Cohomology in degree `i` on the derived category. -/
abbrev derivedCohomologyFunctor (i : ℤ) : D.{v} R ⥤ ModuleCat.{v} R :=
  DerivedCategory.homologyFunctor (ModuleCat.{v} R) i

def cohomologyFactors (i : ℤ) :
    Q.{v} R ⋙ derivedCohomologyFunctor.{v} R i ≅ cohomologyFunctor.{v} R i :=
  DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i

/-- The cochain complex supported in degree zero. -/
abbrev stalk : ModuleCat.{v} R ⥤ Comp.{v} R :=
  CochainComplex.singleFunctor (ModuleCat.{v} R) 0

/-- The degree-zero stalk viewed in the derived category. -/
abbrev derivedStalk : ModuleCat.{v} R ⥤ D.{v} R := stalk.{v} R ⋙ Q.{v} R

@[simp] theorem stalk_X_zero (M : ModuleCat.{v} R) :
    ((stalk R).obj M).X 0 = M :=
  HomologicalComplex.single_obj_X_self (.up ℤ) 0 M

theorem stalk_X_isZero (M : ModuleCat.{v} R) (i : ℤ) (hi : i ≠ 0) :
    IsZero (((stalk R).obj M).X i) :=
  HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M i hi

@[simp] theorem stalk_d (M : ModuleCat.{v} R) (i j : ℤ) :
    ((stalk R).obj M).d i j = 0 :=
  CochainComplex.singleFunctor_obj_d M 0 i j

/-- The cochain shift by `s`, taking degree `i` from degree `i + s`. -/
abbrev cochainShift (s : ℤ) : Comp.{v} R ⥤ Comp.{v} R :=
  CategoryTheory.shiftFunctor (Comp.{v} R) s

/-- Localization commutes with the cochain shift. -/
def QShiftIso (s : ℤ) :
    cochainShift.{v} R s ⋙ Q.{v} R ≅ Q.{v} R ⋙ CategoryTheory.shiftFunctor (D.{v} R) s :=
  (Q.{v} R).commShiftIso s

@[simp] theorem cochainShift_X (s : ℤ) (X : Comp.{v} R) (i : ℤ) :
    ((cochainShift R s).obj X).X i = X.X (i + s) :=
  CochainComplex.shiftFunctor_obj_X' X s i

@[simp] theorem cochainShift_d (s : ℤ) (X : Comp.{v} R) (i j : ℤ) :
    ((cochainShift R s).obj X).d i j = s.negOnePow • X.d (i + s) (j + s) :=
  CochainComplex.shiftFunctor_obj_d' X s i j

/-- The cohomology of a shifted complex in degree `i` is cohomology in degree `i + s`. -/
def cohomologyShiftIso (s i : ℤ) :
    cochainShift.{v} R s ⋙ cohomologyFunctor.{v} R i ≅ cohomologyFunctor.{v} R (i + s) :=
  CochainComplex.ShiftSequence.shiftIso (ModuleCat.{v} R) s i (i + s)
    (add_comm s i)

/-- The same shift formula for cohomology on the derived category. -/
def derivedCohomologyShiftIso (s i : ℤ) :
    CategoryTheory.shiftFunctor (D.{v} R) s ⋙ derivedCohomologyFunctor.{v} R i ≅
      derivedCohomologyFunctor.{v} R (i + s) :=
  (derivedCohomologyFunctor.{v} R 0).shiftIso s i (i + s) (add_comm s i)

end

end DerivedFormalization
