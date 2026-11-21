import MathGenome.Internal.Specs.D07.Ch08.MatrixRing
import MathGenome.Internal.D07.Ch08.RingDefinition
import Mathlib.LinearAlgebra.Matrix.Unique

/-!
K07.08.matrix_ring, paper.tex:1257–1271. The canonical matrix operations
are the same operations used in D05.M04.MatrixProduct; their ring laws
here require only `Ring R`, not a commutative or nontrivial base ring.
-/

universe u

namespace D07.Ch08.MatrixRing

open Specs.D07.Ch08.MatrixRing
open scoped BigOperators

theorem ringConstruction : RingConstruction.{u} := by
  intro R _ n
  exact ⟨inferInstance, rfl, rfl, rfl⟩

theorem entries : Entries.{u} := by
  intro R _ n A B i j
  exact ⟨rfl, rfl, Matrix.one_apply, rfl, rfl⟩

theorem tripleProductEntries : TripleProductEntries.{u} := by
  intro R _ n A B C i j
  have h : (A * (B * C)) i j = ∑ k, ∑ l, (A i k * B k l) * C l j := by
    simp only [Matrix.mul_apply, Finset.mul_sum, mul_assoc]
  constructor
  · rw [Matrix.mul_assoc]
    exact h
  · exact h

theorem ringLaws : RingLaws.{u} := by
  intro R _ n
  exact {
    mul_assoc := _root_.mul_assoc
    left_distrib := _root_.mul_add
    right_distrib := _root_.add_mul
    one_mul := _root_.one_mul
    mul_one := _root_.mul_one }

theorem matrixUnitProduct : MatrixUnitProduct.{u} := by
  intro R _ n i j k l
  by_cases h : j = k
  · subst k
    simp
  · simp [h]

private theorem matrixUnit_ne_zero {R : Type u} [Ring R] [Nontrivial R]
    {n : ℕ} (i j : Fin n) : Matrix.single i j (1 : R) ≠ 0 := by
  intro h
  have hentry := congrArg (fun A : Matrix (Fin n) (Fin n) R => A i j) h
  simp at hentry

theorem matrixUnitExamples : MatrixUnitExamples.{u} := by
  intro R _ _ n i j hij
  refine ⟨?_, matrixUnit_ne_zero i j, ?_, ?_,
    matrixUnit_ne_zero i i, matrixUnit_ne_zero j j⟩
  · simp
  · simp [hij.symm]
  · simp [hij]

theorem noncommutative : Noncommutative.{u} := by
  intro R _ _ n hn hcomm
  let i : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  let j : Fin n := ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hn⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  obtain ⟨hprod, hne, hrev, _⟩ := matrixUnitExamples R n i j hij
  exact hne (hprod.symm.trans ((hcomm _ _).trans hrev))

theorem hasZeroDivisors : HasZeroDivisors.{u} := by
  intro R _ _ n hn
  let i : Fin n := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  let j : Fin n := ⟨1, lt_of_lt_of_le (by decide : 1 < 2) hn⟩
  have hij : i ≠ j := by
    intro h
    have := congrArg Fin.val h
    simp [i, j] at this
  obtain ⟨_, _, _, hzero, hi, hj⟩ := matrixUnitExamples R n i j hij
  exact ⟨Matrix.single i i 1, Matrix.single j j 1, hi, hj, hzero⟩

theorem sizeOne : SizeOne.{u} := by
  intro R _
  refine ⟨Matrix.uniqueRingEquiv, ?_, ?_⟩
  · intro A
    rfl
  · intro r i j
    rfl

theorem sizeZero : SizeZero.{u} := by
  intro R _
  exact ⟨inferInstance, Subsingleton.elim _ _⟩

end D07.Ch08.MatrixRing
