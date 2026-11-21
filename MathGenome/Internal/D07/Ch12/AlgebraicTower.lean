import MathGenome.Internal.Specs.D07.Ch12.AlgebraicTower
import Mathlib.RingTheory.Algebraic.Integral

/-!
Transitivity of algebraicity (K07.12.algebraic_tower).

`IsAlgebraic.restrictScalars` applies to an element algebraic over E when
E is algebraic over K and the scalar maps form a compatible tower. Its
`NoZeroDivisors E` hypothesis follows from `Field E`. Applying it to every
element of L proves the extension assertion, including infinite algebraic
extensions. Neither finiteness nor a closed ambient field is needed.
-/

universe u v w

namespace D07.Ch12.AlgebraicTower

theorem algebraic_tower :
    Specs.D07.Ch12.AlgebraicTower.AlgebraicityTransitive.{u, v, w} := by
  intro K E L _ _ _ _ _ _ _ hKE hEL
  let : Algebra.IsAlgebraic K E := hKE
  refine ⟨fun α => ?_⟩
  exact (hEL.isAlgebraic α).restrictScalars K

end D07.Ch12.AlgebraicTower
