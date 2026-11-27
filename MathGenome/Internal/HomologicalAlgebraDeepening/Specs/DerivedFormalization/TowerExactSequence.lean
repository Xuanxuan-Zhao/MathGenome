import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Cochains
import Mathlib.CategoryTheory.Functor.OfSequence

/-! The ordinary inverse limit and product of a sequence of cochain complexes. -/

namespace Specs.DerivedFormalization.TowerExactSequence

open CategoryTheory CategoryTheory.Limits Opposite
open Specs.DerivedFormalization.Cochains (compValue cohomologyValue)

universe u v w

noncomputable section

variable {R : Type u} [Ring R]

/-- The map from stage (n+1) to stage (n). -/
abbrev transition (A : ℕᵒᵖ ⥤ compValue.{v} R) (n : ℕ) :
    A.obj (op (n + 1)) ⟶ A.obj (op n) :=
  A.map (homOfLE (Nat.le_add_right n 1)).op

abbrev towerProduct (A : ℕᵒᵖ ⥤ compValue.{v} R) :=
  ∏ᶜ (fun n : ℕ ↦ A.obj (op n))

/-- The canonical map from the inverse limit to the product of the stages. -/
def inclusionValue (A : ℕᵒᵖ ⥤ compValue.{v} R) : limit A ⟶ towerProduct A :=
  Pi.lift (fun n : ℕ ↦ limit.π A (op n))

/-- The product endomorphism with (n)-th coordinate given by the successor projection
followed by the transition from stage (n+1) to stage (n). -/
def shiftValue (A : ℕᵒᵖ ⥤ compValue.{v} R) : towerProduct A ⟶ towerProduct A :=
  Pi.map' (fun n : ℕ ↦ n + 1) (transition A)

/-- The endomorphism (1-s) of the product. -/
def differenceValue (A : ℕᵒᵖ ⥤ compValue.{v} R) : towerProduct A ⟶ towerProduct A :=
  𝟙 _ - shiftValue A

/-- The inverse limit, product, and difference map form a short complex for every tower. -/
def shortComplexValue (A : ℕᵒᵖ ⥤ compValue.{v} R) : ShortComplex (compValue.{v} R) :=
  ShortComplex.mk (inclusionValue A) (differenceValue A) (by
    apply Pi.hom_ext
    intro n
    simp only [differenceValue, Preadditive.comp_sub, Category.comp_id,
      Preadditive.sub_comp, zero_comp, inclusionValue, Pi.lift_comp_π, Category.assoc,
      Pi.lift_comp_π_assoc, shiftValue, Pi.map'_comp_π, transition, limit.w, sub_self])

set_option linter.checkUnivs false in
def inclusionType :=
  ∀ {R : Type u} [Ring R] (A : ℕᵒᵖ ⥤ compValue.{v} R), limit A ⟶ towerProduct A

set_option linter.checkUnivs false in
def shiftType :=
  ∀ {R : Type u} [Ring R] (A : ℕᵒᵖ ⥤ compValue.{v} R), towerProduct A ⟶ towerProduct A

set_option linter.checkUnivs false in
def differenceType :=
  ∀ {R : Type u} [Ring R] (A : ℕᵒᵖ ⥤ compValue.{v} R), towerProduct A ⟶ towerProduct A

set_option linter.checkUnivs false in
def shortComplexType :=
  ∀ {R : Type u} [Ring R] (_ : ℕᵒᵖ ⥤ compValue.{v} R), ShortComplex (compValue.{v} R)

/-- The canonical sequence is short exact when every transition is surjective in each degree. -/
def shortExactType : Prop :=
  ∀ (R : Type u) [Ring R] (A : ℕᵒᵖ ⥤ compValue.{v} R),
    (∀ (n : ℕ) (i : ℤ), Function.Surjective ((transition A n).f i)) →
    (shortComplexValue A).ShortExact

/-- Both maps of the sequence are natural for strict maps of towers. -/
def naturalityType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : ℕᵒᵖ ⥤ compValue.{v} R) (f : A ⟶ B),
    let p : towerProduct A ⟶ towerProduct B :=
      CategoryTheory.Limits.Pi.map (fun n : ℕ ↦ f.app (op n))
    limMap f ≫ inclusionValue B = inclusionValue A ≫ p ∧
    p ≫ differenceValue B = differenceValue A ≫ p

/-- The comparison induced by the product projections is invertible in every cochain degree.
Here `Small` allows any index type that fits in the universe of the modules. -/
def cohomologyProductType : Prop :=
  ∀ (R : Type u) [Ring R] (I : Type w) [Small.{v} I] (A : I → compValue.{v} R) (i : ℤ),
    IsIso (piComparison (cohomologyValue R i) A)

end
end Specs.DerivedFormalization.TowerExactSequence
