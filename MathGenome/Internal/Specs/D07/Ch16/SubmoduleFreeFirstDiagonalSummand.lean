import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.RingTheory.PrincipalIdealDomain

/-! Independent specification of the first reduction in the proof of
`K07.16.submodule_free`, paper.tex:3035–3080. A supplied `Fin n` basis
expresses finite freeness and its rank without imposing any extra hypotheses
on the module. The two internal direct sums are expressed by disjointness
and their supremum. Pointwise scalar multiplication of submodules means
actual scalar multiples of their elements. The last assertion supplies a
basis of the kernel, including its empty basis when `n = 1`. -/

universe u v

namespace Specs.D07.Ch16.SubmoduleFreeFirstDiagonalSummand

open Module
open scoped Pointwise

/-- The independent first diagonal summand, with the divisibility needed to
join it to the remaining diagonal entries. No classification hypothesis is used. -/
def FirstDiagonalSummand : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (M : Type v) [AddCommGroup M] [Module R M]
    (n : ℕ) (_b : Basis (Fin n) R M), 0 < n →
    ∀ N : Submodule R M, N ≠ ⊥ →
      ∃ (a : R) (φ : M →ₗ[R] R) (e : M),
        a ≠ 0 ∧ φ e = 1 ∧ a • e ∈ N ∧
        N.map φ = Ideal.span {a} ∧
        IsCompl (Submodule.span R {e}) (LinearMap.ker φ) ∧
        Disjoint (Submodule.span R {a • e}) (N ⊓ LinearMap.ker φ) ∧
        Submodule.span R {a • e} ⊔ (N ⊓ LinearMap.ker φ) = N ∧
        N ⊓ LinearMap.ker φ ≤ a • LinearMap.ker φ ∧
        Nonempty (Basis (Fin (n - 1)) R (LinearMap.ker φ))

end Specs.D07.Ch16.SubmoduleFreeFirstDiagonalSummand
