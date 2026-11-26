import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.Dimension.Finrank

namespace LinearAlgebraicGroups.Arithmetic.LocalCubicFormsSpec

/-- An arbitrary cubic form in (n) coordinates over a nonarchimedean local
field has a nonzero zero if (n>9). -/
def coordinateCubicIsotropy : Prop :=
  ∀ {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {n : ℕ} (p : MvPolynomial (Fin n) F),
    p.IsHomogeneous 3 → 9 < n → ∃ x : Fin n → F, x ≠ 0 ∧ MvPolynomial.eval x p = 0

/-- A cubic form on a finite-dimensional vector space is represented by
a homogeneous polynomial in the coordinates of a basis. -/
def cubicFormIsotropy : Prop :=
  ∀ {F V : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (b : Module.Basis (Fin (Module.finrank F V)) F V)
    (p : MvPolynomial (Fin (Module.finrank F V)) F),
    p.IsHomogeneous 3 → 9 < Module.finrank F V →
      ∃ x : V, x ≠ 0 ∧ MvPolynomial.eval (b.equivFun x) p = 0

end LinearAlgebraicGroups.Arithmetic.LocalCubicFormsSpec
