import Mathlib.FieldTheory.Galois.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

universe u v

namespace Specs.GaloisFormalization.PV

/-- Finite semilinear descent of a matrix (`res:PV18`). The Galois group acts
entrywise on invertible matrices. -/
def FiniteSemilinearDescent : Prop :=
  ∀ (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    [FiniteDimensional k E] [IsGalois k E] (m : ℕ)
    (a : Gal(E/k) → Matrix.GeneralLinearGroup (Fin m) E),
    (∀ γ η, a (γ * η) = a γ * Matrix.GeneralLinearGroup.map γ.toRingEquiv.toRingHom (a η)) →
    ∃ B : Matrix.GeneralLinearGroup (Fin m) E,
      ∀ γ, Matrix.GeneralLinearGroup.map γ.toRingEquiv.toRingHom B = B * a γ

end Specs.GaloisFormalization.PV
