import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.QuadraticForm.Basic

namespace LinearAlgebraicGroups.Specs.Arithmetic.SpinOrthogonalWords

universe u v

/-- Every isometry of a regular quadratic form over an infinite field is an ordered
product of reflections (symmetries in characteristic two) using the full polar form. -/
def OrthogonalWords : Prop :=
  ∀ {F : Type u} [Field F] [Infinite F] {V : Type v} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (q : QuadraticForm F V),
    (LinearMap.ker q.polarBilin = ⊥ ∨
      ∃ r : V, q r ≠ 0 ∧ LinearMap.ker q.polarBilin = F ∙ r) →
    ∀ g : V ≃ₗ[F] V, (∀ x : V, q (g x) = q x) →
      ∃ l : List V, (∀ w ∈ l, q w ≠ 0) ∧
        ∀ x : V, g x = l.foldr (fun w z => z - (q.polarBilin w z / q w) • w) x

end LinearAlgebraicGroups.Specs.Arithmetic.SpinOrthogonalWords
