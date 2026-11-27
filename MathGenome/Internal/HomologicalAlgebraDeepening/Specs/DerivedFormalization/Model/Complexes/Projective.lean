import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Complexes.CellFactorization
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Model.Localization
import Mathlib.Algebra.Homology.DerivedCategory.Basic

open CategoryTheory CategoryTheory.MorphismProperty HomologicalComplex HomotopicalAlgebra

universe u

namespace DerivedFormalization.Specs.ComplexProjective

open Model.Complexes ComplexGenerators

/-- The projective cofibrations lift against the degreewise surjective quasi-isomorphisms. -/
def cofibrationsValue : generatorClassType.{u} :=
  fun A _ ↦ (degreewiseSurjectiveValue A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ)).llp

def iCellCofibrationsType : Prop :=
  ∀ (A : Type u) [Ring A], ComplexCellFactorization.iCellValue A ≤ cofibrationsValue A

def jCellTrivialCofibrationsType : Prop :=
  ∀ (A : Type u) [Ring A], ComplexCellFactorization.jCellValue A ≤
    cofibrationsValue A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ)

def trivialCofibrationsLiftingType : Prop :=
  ∀ (A : Type u) [Ring A], (degreewiseSurjectiveValue A).llp =
    cofibrationsValue A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ)

def cofibrationsRetractsType : Prop :=
  ∀ (A : Type u) [Ring A], (ComplexCellFactorization.iCellValue A).retracts =
    cofibrationsValue A

def trivialCofibrationsRetractsType : Prop :=
  ∀ (A : Type u) [Ring A], (ComplexCellFactorization.jCellValue A).retracts =
    cofibrationsValue A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ)

def cofibrationFactorizationType : Prop :=
  ∀ (A : Type u) [Ring A], HasFunctorialFactorization (cofibrationsValue A)
    (degreewiseSurjectiveValue A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ))

def fibrationFactorizationType : Prop :=
  ∀ (A : Type u) [Ring A], HasFunctorialFactorization
    (cofibrationsValue A ⊓ quasiIso (ModuleCat A) (ComplexShape.up ℤ))
    (degreewiseSurjectiveValue A)

end DerivedFormalization.Specs.ComplexProjective

namespace DerivedFormalization.Model.Complexes

open Specs.ComplexGenerators Specs.ComplexProjective

/-- A full functorial model category structure on unbounded cochain complexes, with the
three projective morphism classes. The equalities refer to the same model structure. -/
structure ProjectiveModel (A : Type u) [Ring A] where
  model : FunctorialModelCategory (Cochains A)
  weakEquivalences_eq :
    letI := model
    weakEquivalences (Cochains A) = quasiIso (ModuleCat A) (ComplexShape.up ℤ)
  fibrations_eq :
    letI := model
    fibrations (Cochains A) = degreewiseSurjectiveValue A
  cofibrations_eq :
    letI := model
    cofibrations (Cochains A) = cofibrationsValue A

end DerivedFormalization.Model.Complexes

namespace DerivedFormalization.Specs.ComplexProjective

open Model Model.Complexes ModelLocalization

def projectiveModelExistsType : Prop :=
  ∀ (A : Type u) [Ring A], Nonempty (ProjectiveModel A)

def allFibrantType : Prop :=
  ∀ (A : Type u) [Ring A] (M : ProjectiveModel A),
    letI := M.model
    ∀ X : Cochains A, IsFibrant X

/-- The equivalence compares the model homotopy category localization with the
standard derived category localization on the same category of unbounded complexes. -/
def derivedComparisonType : Prop :=
  ∀ (A : Type u) [Ring A] (M : ProjectiveModel A),
    letI := M.model
    letI : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard (ModuleCat A)
    ∃ r : Replacement (Cochains A),
      ∃ e : homotopyCategoryValue (Cochains A) ≌ DerivedCategory (ModuleCat.{u} A),
        Nonempty (localizationFunctorValue r ⋙ e.functor ≅ DerivedCategory.Q)

end DerivedFormalization.Specs.ComplexProjective
