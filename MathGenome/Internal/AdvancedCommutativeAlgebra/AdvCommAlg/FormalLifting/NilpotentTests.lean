import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.FormalLifting.Definitions
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.FormalLifting.NilpotentTests

/-! FL-02: the square-zero tests extend to all nilpotent ideals.
Mathlib's `exists_lift` and `lift_unique` prove this extension by induction on
nilpotent ideals and composition of quotient maps. The reverse implications
use the exponent two. No finiteness or nontriviality assumption is used.
-/
namespace AdvCommAlg.FormalLifting

universe u v w

open Specs.AdvCommAlg.FormalLifting

/-- Formal smoothness gives lifts through every nilpotent quotient, in every
test universe. -/
theorem smooth_nilpotent_reduction_surjective : smoothNilpotentReduction.{u,v,w} := by
  intro A B C _ _ _ _ _ h N hN
  let : Algebra.FormallySmooth A B := (formallySmooth_iff A B).mp h
  exact fun g => Algebra.FormallySmooth.exists_lift N hN g

/-- Formal unramifiedness gives uniqueness through every nilpotent quotient,
in every test universe. -/
theorem unramified_nilpotent_reduction_injective : unramifiedNilpotentReduction.{u,v,w} := by
  intro A B C _ _ _ _ _ h N hN
  let : Algebra.FormallyUnramified A B := (formallyUnramified_iff A B).mp h
  exact fun f g e => Algebra.FormallyUnramified.lift_unique N hN f g e

/-- Formal étaleness gives bijectivity through every nilpotent quotient,
in every test universe. -/
theorem etale_nilpotent_reduction_bijective : etaleNilpotentReduction.{u,v,w} := by
  intro A B C _ _ _ _ _ h N hN
  let : Algebra.FormallyEtale A B := (formallyEtale_iff A B).mp h
  exact ⟨fun f g e => Algebra.FormallyUnramified.lift_unique N hN f g e,
    fun g => Algebra.FormallySmooth.exists_lift N hN g⟩

/-- The existence condition can equivalently test all nilpotent ideals. -/
theorem formallySmooth_iff_nilpotent : smoothNilpotentIff.{u,v} := by
  intro A B _ _ _
  constructor
  · intro h C _ _ N hN
    exact smooth_nilpotent_reduction_surjective h N hN
  · intro h C _ _ N hN
    exact h N ⟨2, hN⟩

/-- The uniqueness condition can equivalently test all nilpotent ideals. -/
theorem formallyUnramified_iff_nilpotent : unramifiedNilpotentIff.{u,v} := by
  intro A B _ _ _
  constructor
  · intro h C _ _ N hN
    exact unramified_nilpotent_reduction_injective h N hN
  · intro h C _ _ N hN
    exact h N ⟨2, hN⟩

/-- The bijectivity condition can equivalently test all nilpotent ideals. -/
theorem formallyEtale_iff_nilpotent : etaleNilpotentIff.{u,v} := by
  intro A B _ _ _
  constructor
  · intro h C _ _ N hN
    exact etale_nilpotent_reduction_bijective h N hN
  · intro h C _ _ N hN
    exact h N ⟨2, hN⟩

end AdvCommAlg.FormalLifting
