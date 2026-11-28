import MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.Cocycle
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.DualJacobi
import MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.Schouten
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-! Coboundary Lie bialgebras and invariant Schouten squares. -/

namespace LieNotes.Coboundary

open private wedge₂_linearMap_ext from MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.DualJacobi

universe u v

section CommRing

variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]

private theorem wedgeWithVector_adjoint_wedge₂ (x a b z : g) :
    wedgeWithVector (k := k) (exteriorAdjoint 2 x (wedge₂ a b)) z =
      -wedgeWithVector (wedge₂ ⁅a, x⁆ b) z + wedgeWithVector (wedge₂ ⁅b, x⁆ a) z := by
  rw [exteriorAdjoint_wedge₂, wedge₂_swap ⁅x, b⁆ a, ← lie_skew x a, ← lie_skew x b]
  simp only [map_add, map_neg, LinearMap.add_apply, LinearMap.neg_apply, neg_neg]

/-- Bracketing with `r` is the negative of the exterior differential of its coboundary. -/
theorem schouten_eq_neg_cobracketDifferential (r s : ⋀[k]^2 g) :
    schouten r s = -cobracketDifferential (coboundary r) s := by
  have hs : schouten r = -cobracketDifferential (coboundary r) := by
    apply wedge₂_linearMap_ext
    intro c d
    have hr : (schouten (k := k)).flip (wedge₂ c d) =
        -((wedgeWithVector.flip d).comp (exteriorAdjoint 2 c) -
          (wedgeWithVector.flip c).comp (exteriorAdjoint 2 d)) := by
      apply wedge₂_linearMap_ext
      intro a b
      change schouten (k := k) (wedge₂ a b) (wedge₂ c d) =
        -(wedgeWithVector (exteriorAdjoint 2 c (wedge₂ a b)) d -
          wedgeWithVector (exteriorAdjoint 2 d (wedge₂ a b)) c)
      simp only [schouten_wedge₂_wedge₂, ← wedgeWithVector_wedge₂,
        wedgeWithVector_adjoint_wedge₂]
      abel
    simpa only [LinearMap.flip_apply, LinearMap.neg_apply, LinearMap.sub_apply,
      LinearMap.comp_apply, cobracketDifferential_wedge₂, coboundary_apply]
      using LinearMap.congr_fun hr r
  exact LinearMap.congr_fun hs s

end CommRing

section Field

variable {k : Type u} {g : Type v} [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]

/-- The exterior co-Jacobi expression is minus half the adjoint action on the square. -/
theorem cobracketDifferential_coboundary (r : ⋀[k]^2 g) (x : g) :
    cobracketDifferential (coboundary r) (coboundary r x) =
      -((1 / 2 : k) • exteriorAdjoint 3 x (schouten r r)) := by
  have h : exteriorAdjoint 3 x (schouten r r) = (2 : k) • schouten r (coboundary r x) := by
    rw [exteriorAdjoint_schouten, schouten_symmetric (exteriorAdjoint 2 x r) r,
      ← coboundary_apply, two_smul]
  rw [h, one_div, inv_smul_smul₀ (by norm_num : (2 : k) ≠ 0),
    schouten_eq_neg_cobracketDifferential, neg_neg]

/-- A coboundary is a Lie bialgebra cobracket exactly when its Schouten square is invariant. -/
theorem coboundary_isLieBialgebra_iff_invariantSquare [Module.Finite k g] (r : ⋀[k]^2 g) :
    isLieBialgebraCobracket (coboundary r) ↔
      ∀ x : g, exteriorAdjoint 3 x (schouten r r) = 0 := by
  change (isCobracketCocycle (coboundary r) ∧ dualJacobi (coboundary r)) ↔ _
  rw [and_iff_right (coboundary_isCocycle r), dualJacobi_iff_cobracketDifferential]
  have hzero (x : g) : cobracketDifferential (coboundary r) (coboundary r x) = 0 ↔
      exteriorAdjoint 3 x (schouten r r) = 0 := by
    rw [cobracketDifferential_coboundary, neg_eq_zero,
      smul_eq_zero_iff_right (by norm_num : (1 / 2 : k) ≠ 0)]
  exact ⟨fun h x => (hzero x).mp (LinearMap.congr_fun h x),
    fun h => LinearMap.ext fun x => (hzero x).mpr (h x)⟩

end Field

end LieNotes.Coboundary
