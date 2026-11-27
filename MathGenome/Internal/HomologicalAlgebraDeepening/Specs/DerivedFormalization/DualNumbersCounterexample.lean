import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainModels
import Mathlib.Algebra.DualNumber
import Mathlib.LinearAlgebra.FreeModule.Basic

/-! The periodic free complex over the dual numbers and its failure of K-flatness. -/

namespace Specs.DerivedFormalization.DualNumbersCounterexample

open CategoryTheory
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.CochainModels
  (isKFlatValue isKProjectiveValue tensorComplexValue)

universe u

variable (k : Type u) [Field k]

local notation "R" => DualNumber k

def complexType := ∀ (k : Type u) [Field k], compValue.{u} (DualNumber k)

/-- The regular module in every degree, with each successive differential
given by multiplication by the canonical square-zero element. -/
abbrev complexValue : compValue.{u} R where
  X _ := ModuleCat.of R R
  d i j := if i + 1 = j then ModuleCat.ofHom (LinearMap.mulLeft R DualNumber.eps) else 0
  shape i j h := ite_eq_right h
  d_comp_d' i j l hij hjl := by
    change i + 1 = j at hij
    change j + 1 = l at hjl
    rw [ite_eq_left hij, ite_eq_left hjl]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (DualNumber.eps : R) * (DualNumber.eps * x) = 0
    rw [← mul_assoc, DualNumber.eps_mul_eps, zero_mul]

def acyclicType : Prop :=
  ∀ (k : Type u) [Field k], (complexValue k).Acyclic

def termwiseFreeType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℤ), Module.Free (DualNumber k) ((complexValue k).X n)

def notKProjectiveType : Prop :=
  ∀ (k : Type u) [Field k], ¬ isKProjectiveValue (complexValue k)

def tensorNotExactAtType : Prop :=
  ∀ (k : Type u) [Field k] (n : ℤ),
    ¬ (tensorComplexValue (complexValue k) (complexValue k)).ExactAt n

def notKFlatType : Prop :=
  ∀ (k : Type u) [Field k], ¬ isKFlatValue (complexValue k)

end Specs.DerivedFormalization.DualNumbersCounterexample
