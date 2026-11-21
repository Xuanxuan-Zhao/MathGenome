import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.Definitions

/-! The square-zero lifting definitions of formal smoothness, unramifiedness,
and étaleness (FL-01), and their equivalence to Mathlib's cotangent predicates.
The reduction lemmas allow arbitrary test universes, including zero test rings.
-/
namespace AdvCommAlg.FormalLifting

universe u v w

open Specs.AdvCommAlg.FormalLifting

/-- Every A-algebra map B → C/N lifts when N² = 0. -/
def FormallySmooth : propertyType.{u,v} := formallySmoothValue

/-- Any two A-algebra maps B → C with the same reduction modulo N agree
when N² = 0. -/
def FormallyUnramified : propertyType.{u,v} := formallyUnramifiedValue

/-- Every A-algebra map B → C/N has exactly one lift when N² = 0. -/
def FormallyEtale : propertyType.{u,v} := formallyEtaleValue

theorem formallySmooth_iff : formallySmoothIff.{u,v} := by
  intro A B _ _ _
  exact Algebra.FormallySmooth.iff_comp_surjective.symm

theorem formallyUnramified_iff : formallyUnramifiedIff.{u,v} := by
  intro A B _ _ _
  exact Algebra.FormallyUnramified.iff_comp_injective_of_small.{max u v}.symm

theorem formallyEtale_iff : formallyEtaleIff.{u,v} := by
  intro A B _ _ _
  exact Algebra.FormallyEtale.iff_comp_bijective.symm

/-- Existence of lifts holds for test algebras in any universe. -/
theorem smooth_reduction_surjective : smoothReduction.{u,v,w} := by
  intro A B C _ _ _ _ _ h N hN
  let : Algebra.FormallySmooth A B := (formallySmooth_iff A B).mp h
  exact Algebra.FormallySmooth.comp_surjective A B N hN

/-- Uniqueness of lifts holds for test algebras in any universe. -/
theorem unramified_reduction_injective : unramifiedReduction.{u,v,w} := by
  intro A B C _ _ _ _ _ h N hN
  let : Algebra.FormallyUnramified A B := (formallyUnramified_iff A B).mp h
  exact Algebra.FormallyUnramified.comp_injective N hN

/-- Existence and uniqueness hold for test algebras in any universe. -/
theorem etale_reduction_bijective : etaleReduction.{u,v,w} := by
  intro A B C _ _ _ _ _ h N hN
  let : Algebra.FormallyEtale A B := (formallyEtale_iff A B).mp h
  exact Algebra.FormallyEtale.comp_bijective A B N hN

end AdvCommAlg.FormalLifting
