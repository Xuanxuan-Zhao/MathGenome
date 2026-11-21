import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! Left modules over the quotient by a two-sided ideal. -/

open CategoryTheory

namespace RM03.Quivers.QuotientModules

universe u v

variable {A : Type u} [Ring A]

/-- The full subcategory defined by this property has all the original module maps. -/
def annihilated (I : Ideal A) : ObjectProperty (ModuleCat.{v} A) :=
  fun M => Module.IsTorsionBySet A M (I : Set A)

variable (I : Ideal A) [I.IsTwoSided]

/-- The same additive group with the quotient action obtained by descending the original action. -/
def descendObj (M : (annihilated.{u, v} I).FullSubcategory) : ModuleCat.{v} (A ⧸ I) :=
  let h : Module.IsTorsionBySet A M.obj (I : Set A) := M.property
  letI := h.module
  ModuleCat.of (A ⧸ I) M.obj

namespace Specs

/-- The quotient action computes on every representative via the original action. -/
def DescentAction : Prop :=
  ∀ {A : Type u} [Ring A] (I : Ideal A) [I.IsTwoSided]
    (M : (annihilated.{u, v} I).FullSubcategory) (a : A) (m : M.obj),
    Ideal.Quotient.mk I a • (show descendObj I M from m) = (a • m : M.obj)

/-- An additive map is linear over the quotient exactly when it is linear after restriction. -/
def LinearityAfterRestriction : Prop :=
  ∀ {A : Type u} [Ring A] (I : Ideal A) [I.IsTwoSided]
    (M N : ModuleCat.{v} (A ⧸ I)) (f : M →+ N),
    let F := ModuleCat.restrictScalars (Ideal.Quotient.mk I)
    (∀ (q : A ⧸ I) (m : M), f (q • m) = q • f m) ↔
    (∀ (a : A) (m : M),
      f (a • (show F.obj M from m)) = (a • (show F.obj N from f m) : F.obj N))

/-- Restriction is an equivalence onto the full subcategory. Its inverse is the descended
action, with the same underlying additive groups and additive maps. -/
def QuotientEquivalence : Prop :=
  ∀ {A : Type u} [Ring A] (I : Ideal A) [I.IsTwoSided],
  ∃ e : ModuleCat.{v} (A ⧸ I) ≌ (annihilated.{u, v} I).FullSubcategory,
    e.functor ⋙ (annihilated I).ι = ModuleCat.restrictScalars (Ideal.Quotient.mk I) ∧
    e.functor ⋙ (annihilated I).ι ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat =
      forget₂ (ModuleCat.{v} (A ⧸ I)) AddCommGrpCat ∧
    (∀ M, e.inverse.obj M = descendObj I M) ∧
    e.inverse ⋙ forget₂ (ModuleCat.{v} (A ⧸ I)) AddCommGrpCat =
      (annihilated I).ι ⋙ forget₂ (ModuleCat.{v} A) AddCommGrpCat

end Specs
end RM03.Quivers.QuotientModules
