import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.WeakEntireLiouville
import Mathlib.Analysis.Complex.Liouville

/-!
The weak Liouville clause of `fa2:p1:frechet-holomorphy`.
For each continuous complex-linear functional, scalar Liouville gives
equality of the values at `z` and `0`. The separating dual turns these
scalar equalities into equality in the original TVS.
-/

namespace ExpandedFA.P1

universe u

theorem weak_entire_liouville :
    WeakEntireLiouvilleSpec.WeakEntireConstant.{u} := by
  intro E _ _ _ _ _ f hhol hbounded
  refine ⟨f 0, fun z => ?_⟩
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  intro ℓ
  exact (hhol ℓ).apply_eq_apply_of_bounded (hbounded ℓ) z 0

end ExpandedFA.P1
