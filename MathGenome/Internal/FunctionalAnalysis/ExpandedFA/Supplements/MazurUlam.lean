import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.MazurUlam
import Mathlib.Analysis.Normed.Affine.MazurUlam

/-!
Mazur--Ulam for arbitrary surjective isometries of real normed spaces.
Injectivity follows from isometry, so surjectivity supplies the equivalence
needed by Mathlib's theorem. Both witnesses below have exactly the original
function as their underlying map. Completeness is never assumed.
-/

namespace ExpandedFA.Supplements.MazurUlam

universe u v

/-- A surjective isometry between real normed spaces is affine. -/
theorem surjective_isometry_is_affine : MazurUlamSpec.AffineConclusion.{u, v} := by
  intro E F _ _ _ _ T hT hsurj
  let e : E ≃ᵢ F :=
    { Equiv.ofBijective T ⟨hT.injective, hsurj⟩ with
      isometry_toFun := hT }
  exact ⟨e.toRealAffineIsometryEquiv.toAffineEquiv.toAffineMap, fun _ => rfl⟩

/-- A surjective isometry fixing zero is real linear. -/
theorem surjective_isometry_zero_is_linear : MazurUlamSpec.LinearConclusion.{u, v} := by
  intro E F _ _ _ _ T hT hsurj hzero
  let e : E ≃ᵢ F :=
    { Equiv.ofBijective T ⟨hT.injective, hsurj⟩ with
      isometry_toFun := hT }
  exact ⟨(e.toRealLinearIsometryEquivOfMapZero hzero).toLinearEquiv.toLinearMap,
    fun _ => rfl⟩

end ExpandedFA.Supplements.MazurUlam
