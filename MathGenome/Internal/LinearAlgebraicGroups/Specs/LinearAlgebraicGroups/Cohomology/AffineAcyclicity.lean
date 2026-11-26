import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

noncomputable section

open AlgebraicGeometry CategoryTheory Limits Opposite

universe u

namespace Specs.LinearAlgebraicGroups.Cohomology

/-- Zariski evaluation at an open, in the abelian category of all module sheaves. -/
abbrev evaluation (X : Scheme.{u}) (U : X.Opens) : X.Modules ⥤ ModuleCat.{u} Γ(X, U) :=
  SheafOfModules.evaluation X.ringCatSheaf (op U)

instance (X : Scheme.{u}) (U : X.Opens) : (evaluation X U).Additive where
  map_add := by intros; rfl

/-- Positive right-derived evaluations at the top open of any prime spectrum vanish. -/
def SpectrumAcyclicity : Prop :=
  ∀ (R : CommRingCat.{u}) (M : (Spec R).Modules) [M.IsQuasicoherent] (n : ℕ),
    0 < n → IsZero (((evaluation (Spec R) ⊤).rightDerived n).obj M)

/-- Positive right-derived global sections of a quasi-coherent module on an affine scheme vanish. -/
def AffineAcyclicity : Prop :=
  ∀ (X : Scheme.{u}) [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] (n : ℕ),
    0 < n → IsZero (((evaluation X ⊤).rightDerived n).obj M)

/-- Positive right-derived evaluation at an affine open, both on the ambient scheme
and on the open with the coefficient sheaf restricted along its inclusion. -/
def AffineOpenAcyclicity : Prop :=
  ∀ (X : Scheme.{u}) (U : X.Opens), IsAffineOpen U →
    ∀ (M : X.Modules) [M.IsQuasicoherent] (n : ℕ), 0 < n →
      IsZero (((evaluation X U).rightDerived n).obj M) ∧
      IsZero (((evaluation U.toScheme ⊤).rightDerived n).obj (M.restrict U.ι))

end Specs.LinearAlgebraicGroups.Cohomology
