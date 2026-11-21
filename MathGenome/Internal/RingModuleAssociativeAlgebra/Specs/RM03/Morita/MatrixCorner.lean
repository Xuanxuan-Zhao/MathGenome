import MathGenome.Internal.RingModuleAssociativeAlgebra.Specs.RM03.Morita.FullEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Data.Matrix.Basis

/-! The full corner at the first diagonal matrix unit. -/

universe u v

namespace RM03.Morita

open CategoryTheory

/-- The first diagonal matrix unit, with the indices numbered from zero. -/
def matrixIdempotent (R : Type u) [Ring R] {n : ℕ} (hn : 0 < n) :
    Idempotent (Matrix (Fin n) (Fin n) R) :=
  let j : Fin n := ⟨0, hn⟩
  ⟨Matrix.single j j 1, by
    change Matrix.single j j (1 : R) * Matrix.single j j 1 = Matrix.single j j 1
    rw [Matrix.single_mul_single_same, one_mul]⟩

namespace MatrixCornerSpec

/-- The indicated matrix-unit sum exhibits fullness. -/
def fullType : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ) (hn : 0 < n),
    let j : Fin n := ⟨0, hn⟩
    let e := matrixIdempotent R hn
    IsFull e ∧ (∑ i, Matrix.single i j (1 : R) * e.val * Matrix.single j i 1) = 1

/-- The corner is identified with the coefficient ring by its first entry.
Both functors are the full-corner functors transported along that identification. -/
def equivalenceType : Prop :=
  ∀ (R : Type u) [Ring R] (n : ℕ) (hn : 0 < n),
    let j : Fin n := ⟨0, hn⟩
    let e := matrixIdempotent R hn
    ∃ φ : Corner e ≃+* R,
      (∀ a : Corner e, φ a = a.val j j) ∧
      (∀ r : R, (φ.symm r).val = Matrix.single j j r) ∧
      ∃ E : ModuleCat.{max u v} (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ ≌
          ModuleCat.{max u v} Rᵐᵒᵖ,
        E.functor = CornerSpec.cornerFunctorValue e ⋙
          ModuleCat.restrictScalars φ.symm.op.toRingHom ∧
        E.inverse = ModuleCat.restrictScalars φ.op.toRingHom ⋙ fromCornerFunctor e

end MatrixCornerSpec
end RM03.Morita
