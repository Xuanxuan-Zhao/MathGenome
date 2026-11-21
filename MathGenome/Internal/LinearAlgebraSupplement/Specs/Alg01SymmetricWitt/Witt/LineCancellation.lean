import Mathlib.LinearAlgebra.QuadraticForm.Prod
import Mathlib.LinearAlgebra.QuadraticForm.Radical

namespace Specs.Alg01SymmetricWitt.Witt.LineCancellation

universe u v w

/-- Cancellation of the same nondegenerate line from two orthogonal sums. -/
def cancelLine : Prop :=
  ∀ {k : Type u} {U : Type v} {V : Type w} [Field k]
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V]
    [Invertible (2 : k)] [FiniteDimensional k U] [FiniteDimensional k V]
    (qU : QuadraticForm k U) (qV : QuadraticForm k V),
    qU.Nondegenerate → qV.Nondegenerate → ∀ {a : k}, a ≠ 0 →
    let line := a • (QuadraticMap.sq (R := k) : QuadraticForm k k)
    (qU.prod line).IsometryEquiv (qV.prod line) → qU.Equivalent qV

end Specs.Alg01SymmetricWitt.Witt.LineCancellation
