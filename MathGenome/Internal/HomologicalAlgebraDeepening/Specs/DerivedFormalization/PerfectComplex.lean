import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Cochains
import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Defs

/-! Specifications for bounded finite projective models and perfect derived objects. -/

namespace Specs.DerivedFormalization.PerfectComplex

open CategoryTheory
open Specs.DerivedFormalization.Cochains (compValue derivedValue qValue)

universe v u

-- The ring and the modules retain the distinct universes of the cochain models.
set_option linter.checkUnivs false

variable {R : Type u} [CommRing R]

def isBoundedFiniteProjectiveType :=
  ∀ {R : Type u} [CommRing R], compValue.{v} R → Prop

def isBoundedFiniteProjectiveValue (C : compValue.{v} R) : Prop :=
  (∀ i : ℤ, Module.Finite R (C.X i) ∧ Module.Projective R (C.X i)) ∧
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i → Limits.IsZero (C.X i)

def isPerfectType :=
  ∀ {R : Type u} [CommRing R], derivedValue.{v} R → Prop

def isPerfectValue (P : derivedValue.{v} R) : Prop :=
  ∃ C : compValue.{v} R,
    isBoundedFiniteProjectiveValue C ∧ Nonempty (P ≅ (qValue R).obj C)

end Specs.DerivedFormalization.PerfectComplex
