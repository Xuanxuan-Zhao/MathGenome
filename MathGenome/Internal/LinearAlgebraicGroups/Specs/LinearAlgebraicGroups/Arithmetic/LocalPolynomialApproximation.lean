import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.Padics.LocalField

universe u

namespace LinearAlgebraicGroups.Arithmetic.LocalPolynomialApproximation

/-- A finite-dimensional topological extension of the p-adic field contains
a dense embedded number field in its given topology. -/
def Statement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Algebra ℚ_[p] F]
    [ContinuousSMul ℚ_[p] F] [FiniteDimensional ℚ_[p] F],
    ∃ (K : Type u) (_ : Field K) (_ : NumberField K) (i : K →+* F), DenseRange i

end LinearAlgebraicGroups.Arithmetic.LocalPolynomialApproximation
