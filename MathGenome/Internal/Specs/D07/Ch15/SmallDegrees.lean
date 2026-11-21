import MathGenome.Internal.Specs.D07.Ch15.RadicalEquivalenceCharZero

/-!
K07.15.small_degrees, paper.tex:4436–4442.
Every root is taken in the specified algebraic closure Ω and belongs to a
finite radical tower with the shared meaning of radical solvability.
For a nonzero polynomial the natural-degree bound expresses degree at most
four, including nonzero constants. No separability or irreducibility of the
polynomial is assumed; in particular repeated factors are allowed.
The explicit formulas are specified separately in
`Specs.D07.Ch15.SmallDegreesCubicQuarticFormulas`.
-/

universe u v

namespace Specs.D07.Ch15.SmallDegrees

open Polynomial Specs.D07.Ch15.RadicalDefinition

def DegreeAtMostFourSolvable : Prop :=
  ∀ (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
    [Algebra.IsAlgebraic K Ω] [IsAlgClosed Ω] [CharZero K]
    (f : K[X]), f ≠ 0 → f.natDegree ≤ 4 →
      ∀ a : Ω, aeval a f = 0 → solvableByRadicalsValue K Ω a

end Specs.D07.Ch15.SmallDegrees
