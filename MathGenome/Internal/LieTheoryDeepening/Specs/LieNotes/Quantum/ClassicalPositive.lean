import Mathlib.Algebra.Lie.Classical
import Mathlib.Algebra.Lie.UniversalEnveloping
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Quantum.SerrePresentation

/-! The classical specialization of the type A₂ positive Serre presentation. -/

namespace Specs.LieNotes.Quantum.ClassicalPositive

open SerrePresentation

universe u

attribute [local instance 100] LieRing.ofAssociativeRing

variable (A : Type u) [CommRing A]

/-- The strictly upper triangular matrices, with the matrix commutator. -/
def positive : LieSubalgebra A (Matrix (Fin 3) (Fin 3) A) where
  carrier := {M | ∀ i j, j ≤ i → M i j = 0}
  zero_mem' := fun _ _ _ => rfl
  add_mem' {M N} hM hN i j hij := by
    change M i j + N i j = 0
    simp [hM i j hij, hN i j hij]
  smul_mem' r M hM i j hij := by
    change r • M i j = 0
    simp [hM i j hij]
  lie_mem' {M N} hM hN := by
    have mul_zero {U V : Matrix (Fin 3) (Fin 3) A}
        (hU : ∀ i j, j ≤ i → U i j = 0) (hV : ∀ i j, j ≤ i → V i j = 0)
        (i j : Fin 3) (hij : j ≤ i) : (U * V) i j = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro k _
      rcases le_total k i with hk | hk
      · rw [hU i k hk, zero_mul]
      · rw [hV k j (hij.trans hk), mul_zero]
    intro i j hij
    change (M * N) i j - (N * M) i j = 0
    rw [mul_zero hM hN i j hij, mul_zero hN hM i j hij, sub_self]

private def upperUnit (i j : Fin 3) (h : i < j) : positive A :=
  ⟨Matrix.single i j 1, fun a b hab =>
    Matrix.single_apply_of_ne i j 1 a b (by
      rintro ⟨rfl, rfl⟩
      exact h.not_ge hab)⟩

/-- Matrix units use zero-based Lean indices and one-based mathematical names. -/
def e12 : positive A := upperUnit A 0 1 (by decide)

def e23 : positive A := upperUnit A 1 2 (by decide)

def e13 : positive A := upperUnit A 0 2 (by decide)

def positiveType :=
  ∀ (A : Type u) [CommRing A], LieSubalgebra A (Matrix (Fin 3) (Fin 3) A)

def matrixUnitType := ∀ (A : Type u) [CommRing A], positive A

def positiveLeSlProp : Prop :=
  ∀ (A : Type u) [CommRing A], positive A ≤ LieAlgebra.SpecialLinear.sl (Fin 3) A

def zEqLieProp : Prop :=
  ∀ (A : Type u) [CommRing A], z (1 : Aˣ) = ⁅x (1 : Aˣ), y (1 : Aˣ)⁆

def zCentralProp : Prop :=
  ∀ (A : Type u) [CommRing A] (a : SerreAlgebra A 1), Commute (z (1 : Aˣ)) a

def classicalSpecializationProp : Prop :=
  ∀ (A : Type u) [CommRing A],
    ∃ e : SerreAlgebra A 1 ≃ₐ[A] UniversalEnvelopingAlgebra A (positive A),
      e (x (1 : Aˣ)) = UniversalEnvelopingAlgebra.ι A (e12 A) ∧
      e (y (1 : Aˣ)) = UniversalEnvelopingAlgebra.ι A (e23 A) ∧
      e (z (1 : Aˣ)) = UniversalEnvelopingAlgebra.ι A (e13 A)

end Specs.LieNotes.Quantum.ClassicalPositive
