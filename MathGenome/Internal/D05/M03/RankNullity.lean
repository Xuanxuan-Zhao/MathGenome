import MathGenome.Internal.Specs.D05.M03.RankNullity
import MathGenome.Internal.D05.M03.Kernel
import MathGenome.Internal.D05.M03.Image
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! K05.03.rank_nullity: rank–nullity for a finite-dimensional domain. -/

namespace D05.M03.RankNullity

/-- The range and kernel dimensions sum to the domain dimension; no finiteness
assumption on the codomain is needed. -/
theorem rank_nullity : Specs.D05.M03.RankNullity.rank_nullity := by
  intro K V W _ _ _ _ _ _ T
  simpa only [Nat.add_comm] using T.finrank_range_add_finrank_ker.symm

end D05.M03.RankNullity
