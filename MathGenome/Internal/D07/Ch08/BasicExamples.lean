import MathGenome.Internal.Specs.D07.Ch08.BasicExamples
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
Arithmetic, product, function and residue rings (paper.tex:1192–1209).
The canonical Mathlib structures have the specified primitive operations.
For residue classes we additionally prove surjectivity, the exact equality
criterion, the formulas on representatives and their well-definedness.
-/

universe u v

namespace D07.Ch08.BasicExamples

open Specs.D07.Ch08.BasicExamples

theorem ringOnGivenOperations (R : Type u) [Ring R] : RingOnGivenOperations R :=
  ⟨inferInstance, rfl, rfl, rfl, rfl, rfl⟩

theorem commRingOnGivenOperations (R : Type u) [CommRing R] :
    CommRingOnGivenOperations R :=
  ⟨inferInstance, rfl, rfl, rfl, rfl, rfl⟩

theorem arithmeticRings : ArithmeticRings :=
  ⟨commRingOnGivenOperations ℤ, commRingOnGivenOperations ℚ,
    commRingOnGivenOperations ℝ, commRingOnGivenOperations ℂ⟩

theorem productRing : ProductRing.{u, v} := by
  intro I R _
  exact ringOnGivenOperations (∀ i, R i)

theorem productOperations : ProductOperations.{u, v} := by
  intro I R _ a b i
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem functionRing : FunctionRing.{u, v} := by
  intro X R _
  exact productRing X (fun _ => R)

theorem functionMultiplication : FunctionMultiplication.{u, v} := by
  intro X R _ f g x
  rfl

theorem emptyFunctions : EmptyFunctions.{u, v} := by
  intro X R _ _
  refine ⟨0, trivial, ?_⟩
  intro f _
  exact funext fun x => isEmptyElim x

theorem nontrivialFunctions : NontrivialFunctions.{u, v} := by
  intro X R _ _ _
  obtain ⟨x⟩ := ‹Nonempty X›
  have h : (0 : X → R) ≠ 1 := by
    intro h
    exact zero_ne_one (congrFun h x)
  exact ⟨h, ⟨⟨0, 1, h⟩⟩⟩

theorem representativesCompatible : RepresentativesCompatible := by
  intro n _ a a' b b' ha hb
  constructor
  · convert dvd_add ha hb using 1
    ring
  · have h : a * b - a' * b' = a * (b - b') + (a - a') * b' := by ring
    rw [h]
    exact dvd_add (dvd_mul_of_dvd_right hb a) (dvd_mul_of_dvd_left ha b')

theorem residueRepresentatives : ResidueRepresentatives := by
  intro n _
  exact ZMod.intCast_surjective

theorem residueClassEquality : ResidueClassEquality := by
  intro n _ a b
  rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem residueOperations : ResidueOperations := by
  intro n _
  exact ⟨fun a b => Int.cast_add a b, fun a b => Int.cast_mul a b,
    fun a => Int.cast_neg a, Int.cast_zero, Int.cast_one⟩

theorem residueRing : ResidueRing := by
  intro n _
  exact commRingOnGivenOperations (ZMod n)

theorem modulusOne : ModulusOne := by
  refine ⟨Subsingleton.elim _ _, 0, trivial, ?_⟩
  intro z _
  exact Subsingleton.elim _ _

end D07.Ch08.BasicExamples
