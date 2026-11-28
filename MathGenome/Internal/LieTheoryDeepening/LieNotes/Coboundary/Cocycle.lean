import MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.Basic
import Mathlib.Tactic.Abel

/-! The adjoint action on the exterior square and the coboundary cocycle of LD04. -/

namespace LieNotes.Coboundary

universe u v

variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]

/-- The commutator of two exterior-square adjoint operators acts by their Lie bracket. -/
theorem exteriorAdjoint_wedge₂_lie (x y : g) (r : ⋀[k]^2 g) :
    exteriorAdjoint 2 ⁅x, y⁆ r =
      exteriorAdjoint 2 x (exteriorAdjoint 2 y r) -
        exteriorAdjoint 2 y (exteriorAdjoint 2 x r) := by
  have h : exteriorAdjoint (k := k) 2 ⁅x, y⁆ =
      (exteriorAdjoint 2 x).comp (exteriorAdjoint 2 y) -
        (exteriorAdjoint 2 y).comp (exteriorAdjoint 2 x) := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    simp only [LinearMap.compAlternatingMap_apply]
    rw [hv, ← wedge₂_apply]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, exteriorAdjoint_wedge₂,
      map_add, lie_lie, map_sub]
    abel
  exact DFunLike.congr_fun h r

/-- Every coboundary satisfies the Lie bialgebra cocycle identity. -/
theorem coboundary_isCocycle (r : ⋀[k]^2 g) : isCobracketCocycle (coboundary r) := by
  intro x y
  simpa only [coboundary_apply] using exteriorAdjoint_wedge₂_lie x y r

end LieNotes.Coboundary
