import Mathlib.Algebra.Field.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Subgroup

/-!
Independent specification of `lem:finite-multiplicative-cyclic`
(paper.tex:3802–3810; chapters/M07.12.tex:261).

The multiplicative group of a field is its group of units. Finiteness is
required only of the subgroup, so the ambient field may be infinite.
`IsCyclic H` uses the inherited group operations and means that every
member is an integer power of a single member of H. The trivial subgroup
is included.
-/

namespace Specs.D07.Ch12.FiniteMultiplicativeCyclic

universe u

/-- Every finite subgroup of the multiplicative group of any field is cyclic. -/
def FiniteMultiplicativeSubgroupIsCyclic : Prop :=
  ∀ (K : Type u) [Field K] (H : Subgroup Kˣ) [Finite H], IsCyclic H

end Specs.D07.Ch12.FiniteMultiplicativeCyclic
