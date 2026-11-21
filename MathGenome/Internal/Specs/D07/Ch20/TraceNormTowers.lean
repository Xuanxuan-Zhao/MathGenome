import MathGenome.Internal.Specs.D07.Ch20.MultiplicationTraceNorm
import Mathlib.RingTheory.AlgebraTower

/-!
Independent specification of K07.20.trace_norm_towers, paper.tex:5903–5919.

The three chosen embeddings are compatible by IsScalarTower. Both steps
have finite vector-space dimension; the total extension is consequently
finite as well. The fields and their universes are arbitrary. In particular,
there is no separability, normality, or characteristic hypothesis.

Algebra.trace and Algebra.norm are precisely the operator trace and
determinant of multiplication specified in MultiplicationTraceNorm.
-/

universe u v w

namespace Specs.D07.Ch20.TraceNormTowers

/-- Trace is transitive in every finite tower, including inseparable towers. -/
def TraceTower : Prop :=
  ∀ (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] (a : L),
    Algebra.trace K L a = Algebra.trace K M (Algebra.trace M L a)

/-- The multiplication-operator norm is transitive in every finite tower. -/
def NormTower : Prop :=
  ∀ (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L] [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] (a : L),
    Algebra.norm K a = Algebra.norm K (Algebra.norm M a)

end Specs.D07.Ch20.TraceNormTowers
