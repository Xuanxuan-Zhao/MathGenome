import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! Independent specifications for the ordinary cochain and derived category models. -/

namespace Specs.DerivedFormalization.Cochains

open CategoryTheory CategoryTheory.Limits

universe v u

variable (R : Type u) [Ring R]

attribute [local instance] HasDerivedCategory.standard

-- The type-valued specifications retain distinct ring and module universes.
set_option linter.checkUnivs false

noncomputable section

def compType := ∀ (R : Type u) [Ring R], Type (max u (v + 1))

abbrev compValue := CochainComplex (ModuleCat.{v} R) ℤ

def homotopyType := ∀ (R : Type u) [Ring R], Type (max u (v + 1))

abbrev homotopyValue := HomotopyCategory (ModuleCat.{v} R) (.up ℤ)

def derivedType := ∀ (R : Type u) [Ring R], Type (max u (v + 1))

abbrev derivedValue := DerivedCategory (ModuleCat.{v} R)

def qType := ∀ (R : Type u) [Ring R], compValue.{v} R ⥤ derivedValue.{v} R

abbrev qValue : compValue.{v} R ⥤ derivedValue.{v} R := DerivedCategory.Q

def qhType := ∀ (R : Type u) [Ring R], homotopyValue.{v} R ⥤ derivedValue.{v} R

def qhValue : homotopyValue.{v} R ⥤ derivedValue.{v} R := DerivedCategory.Qh

def quotientType := ∀ (R : Type u) [Ring R], compValue.{v} R ⥤ homotopyValue.{v} R

def quotientValue : compValue.{v} R ⥤ homotopyValue.{v} R :=
  HomotopyCategory.quotient (ModuleCat.{v} R) (.up ℤ)

def qIsLocalizationType : Prop :=
  ∀ (R : Type u) [Ring R],
    (qValue.{v} R).IsLocalization (HomologicalComplex.quasiIso (ModuleCat.{v} R) (.up ℤ))

def qhIsLocalizationType : Prop :=
  ∀ (R : Type u) [Ring R],
    (qhValue.{v} R).IsLocalization (HomotopyCategory.quasiIso (ModuleCat.{v} R) (.up ℤ))

def quotientCompQhIsoType :=
  ∀ (R : Type u) [Ring R], quotientValue.{v} R ⋙ qhValue.{v} R ≅ qValue.{v} R

def quotientCompQhIsoValue : quotientValue.{v} R ⋙ qhValue.{v} R ≅ qValue.{v} R :=
  DerivedCategory.quotientCompQhIso (ModuleCat.{v} R)

def compHasLimitsType : Prop :=
  ∀ (R : Type u) [Ring R], HasLimits (compValue.{v} R)

def compHasColimitsType : Prop :=
  ∀ (R : Type u) [Ring R], HasColimits (compValue.{v} R)

def evalPreservesLimitsType : Prop :=
  ∀ (R : Type u) [Ring R] (i : ℤ),
    PreservesLimits (HomologicalComplex.eval (ModuleCat.{v} R) (.up ℤ) i)

def evalPreservesColimitsType : Prop :=
  ∀ (R : Type u) [Ring R] (i : ℤ),
    PreservesColimits (HomologicalComplex.eval (ModuleCat.{v} R) (.up ℤ) i)

def cohomologyType := ∀ (R : Type u) [Ring R], ℤ → compValue.{v} R ⥤ ModuleCat.{v} R

def cohomologyValue (i : ℤ) : compValue.{v} R ⥤ ModuleCat.{v} R :=
  HomologicalComplex.homologyFunctor (ModuleCat.{v} R) (.up ℤ) i

def derivedCohomologyType :=
  ∀ (R : Type u) [Ring R], ℤ → derivedValue.{v} R ⥤ ModuleCat.{v} R

abbrev derivedCohomologyValue (i : ℤ) : derivedValue.{v} R ⥤ ModuleCat.{v} R :=
  DerivedCategory.homologyFunctor (ModuleCat.{v} R) i

def cohomologyFactorsType :=
  ∀ (R : Type u) [Ring R] (i : ℤ),
    qValue.{v} R ⋙ derivedCohomologyValue.{v} R i ≅ cohomologyValue.{v} R i

def cohomologyFactorsValue (i : ℤ) :
    qValue.{v} R ⋙ derivedCohomologyValue.{v} R i ≅ cohomologyValue.{v} R i :=
  DerivedCategory.homologyFunctorFactors (ModuleCat.{v} R) i

def stalkType := ∀ (R : Type u) [Ring R], ModuleCat.{v} R ⥤ compValue.{v} R

def stalkValue : ModuleCat.{v} R ⥤ compValue.{v} R :=
  HomologicalComplex.single (ModuleCat.{v} R) (.up ℤ) 0

def derivedStalkType := ∀ (R : Type u) [Ring R], ModuleCat.{v} R ⥤ derivedValue.{v} R

def derivedStalkValue : ModuleCat.{v} R ⥤ derivedValue.{v} R :=
  DerivedCategory.singleFunctor (ModuleCat.{v} R) 0

def stalkXZeroType : Prop :=
  ∀ (R : Type u) [Ring R] (M : ModuleCat.{v} R), ((stalkValue R).obj M).X 0 = M

def stalkXIsZeroType : Prop :=
  ∀ (R : Type u) [Ring R] (M : ModuleCat.{v} R) (i : ℤ), i ≠ 0 →
    IsZero (((stalkValue R).obj M).X i)

def stalkDType : Prop :=
  ∀ (R : Type u) [Ring R] (M : ModuleCat.{v} R) (i j : ℤ),
    ((stalkValue R).obj M).d i j = 0

def shiftType := ∀ (R : Type u) [Ring R], ℤ → compValue.{v} R ⥤ compValue.{v} R

def shiftValue (s : ℤ) : compValue.{v} R ⥤ compValue.{v} R :=
  CochainComplex.shiftFunctor (ModuleCat.{v} R) s

def qShiftIsoType :=
  ∀ (R : Type u) [Ring R] (s : ℤ),
    shiftValue.{v} R s ⋙ qValue.{v} R ≅
      qValue.{v} R ⋙ CategoryTheory.shiftFunctor (derivedValue.{v} R) s

def qShiftIsoValue (s : ℤ) :
    shiftValue.{v} R s ⋙ qValue.{v} R ≅
      qValue.{v} R ⋙ CategoryTheory.shiftFunctor (derivedValue.{v} R) s :=
  (qValue.{v} R).commShiftIso s

def shiftXType : Prop :=
  ∀ (R : Type u) [Ring R] (s : ℤ) (X : compValue.{v} R) (i : ℤ),
    ((shiftValue R s).obj X).X i = X.X (i + s)

def shiftDType : Prop :=
  ∀ (R : Type u) [Ring R] (s : ℤ) (X : compValue.{v} R) (i j : ℤ),
    ((shiftValue R s).obj X).d i j = s.negOnePow • X.d (i + s) (j + s)

def cohomologyShiftIsoType :=
  ∀ (R : Type u) [Ring R] (s i : ℤ),
    shiftValue.{v} R s ⋙ cohomologyValue.{v} R i ≅ cohomologyValue.{v} R (i + s)

def cohomologyShiftIsoValue (s i : ℤ) :
    shiftValue.{v} R s ⋙ cohomologyValue.{v} R i ≅ cohomologyValue.{v} R (i + s) :=
  CochainComplex.ShiftSequence.shiftIso (ModuleCat.{v} R) s i (i + s) (add_comm s i)

def derivedCohomologyShiftIsoType :=
  ∀ (R : Type u) [Ring R] (s i : ℤ),
    CategoryTheory.shiftFunctor (derivedValue.{v} R) s ⋙ derivedCohomologyValue.{v} R i ≅
      derivedCohomologyValue.{v} R (i + s)

def derivedCohomologyShiftIsoValue (s i : ℤ) :
    CategoryTheory.shiftFunctor (derivedValue.{v} R) s ⋙ derivedCohomologyValue.{v} R i ≅
      derivedCohomologyValue.{v} R (i + s) :=
  (derivedCohomologyValue.{v} R 0).shiftIso s i (i + s) (add_comm s i)

end

end Specs.DerivedFormalization.Cochains
