import MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.Basic
import MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.Schouten
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-! The Schouten bracket on two bivectors and its adjoint equivariance. -/

open scoped TensorProduct

namespace LieNotes.Coboundary

universe u v

variable {k : Type u} {g : Type v} [CommRing k] [LieRing g] [LieAlgebra k g]

open private wedgeThree tensorBracket from MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.Schouten

/-- The bilinear Schouten bracket of bivectors, with values in the exterior cube. -/
noncomputable def schouten : ⋀[k]^2 g →ₗ[k] ⋀[k]^2 g →ₗ[k] ⋀[k]^3 g :=
  Specs.LieNotes.Coboundary.schoutenValue

private theorem wedgeThree_apply (a b c : g) :
    wedgeThree (k := k) a b c = exteriorPower.ιMulti k 3 ![a, b, c] := by
  change exteriorPower.ιMulti k 3 (Fin.cons a (Fin.cons b (fun _ => c))) = _
  congr 1
  funext i
  fin_cases i <;> rfl

private theorem tensorBracket_tmul (a b c d : g) :
    tensorBracket (a ⊗ₜ[k] b) (c ⊗ₜ[k] d) = wedgeThree (k := k) ⁅a, c⁆ b d := by
  rw [tensorBracket, TensorProduct.lift.tmul]
  simp only [LinearMap.compr₂_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.lift.equiv_apply, LinearMap.lflip_apply, LinearMap.flip_apply]
  rfl

private theorem schouten_apply_wedgeThree (a b c d : g) :
    schouten (k := k) (wedge₂ a b) (wedge₂ c d) =
      wedgeThree ⁅a, c⁆ b d - wedgeThree ⁅a, d⁆ b c -
        wedgeThree ⁅b, c⁆ a d + wedgeThree ⁅b, d⁆ a c := by
  change tensorBracket (alternatingTensor (wedge₂ a b)) (alternatingTensor (wedge₂ c d)) = _
  simp only [alternatingTensor_wedge₂, map_sub, LinearMap.sub_apply, tensorBracket_tmul]
  abel

/-- The sign convention of Proposition LD05 on decomposable bivectors. -/
theorem schouten_wedge₂_wedge₂ (a b c d : g) :
    schouten (k := k) (wedge₂ a b) (wedge₂ c d) =
      exteriorPower.ιMulti k 3 ![⁅a, c⁆, b, d] - exteriorPower.ιMulti k 3 ![⁅a, d⁆, b, c] -
        exteriorPower.ιMulti k 3 ![⁅b, c⁆, a, d] + exteriorPower.ιMulti k 3 ![⁅b, d⁆, a, c] := by
  simp only [schouten_apply_wedgeThree, wedgeThree_apply]

private theorem exteriorSquare_ext {N : Type*} [AddCommGroup N] [Module k N]
    {f h : ⋀[k]^2 g →ₗ[k] N} (hw : ∀ a b : g, f (wedge₂ a b) = h (wedge₂ a b)) : f = h := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  change f (exteriorPower.ιMulti k 2 v) = h (exteriorPower.ιMulti k 2 v)
  rw [hv, ← wedge₂_apply]
  exact hw _ _

private theorem exteriorSquare_bilinear_ext {N : Type*} [AddCommGroup N] [Module k N]
    {f h : ⋀[k]^2 g →ₗ[k] ⋀[k]^2 g →ₗ[k] N}
    (hw : ∀ a b c d : g, f (wedge₂ a b) (wedge₂ c d) = h (wedge₂ a b) (wedge₂ c d)) :
    f = h := by
  apply exteriorSquare_ext
  intro a b
  exact exteriorSquare_ext (hw a b)

private theorem wedgeThree_swap (a b c : g) :
    wedgeThree (k := k) a c b = -wedgeThree a b c := by
  rw [wedgeThree_apply, wedgeThree_apply]
  have h := (exteriorPower.ιMulti k 3).map_add_swap ![a, c, b] (i := 1) (j := 2) (by decide)
  have hv : (![a, c, b] : Fin 3 → g) ∘ Equiv.swap 1 2 = ![a, b, c] := by
    funext i
    fin_cases i <;> rfl
  rw [hv] at h
  exact eq_neg_of_add_eq_zero_left h

private theorem wedgeThree_bracket_swap (a b c d : g) :
    wedgeThree (k := k) ⁅c, a⁆ d b = wedgeThree ⁅a, c⁆ b d := by
  rw [wedgeThree_swap, ← lie_skew c a]
  let wedgeWith := ((wedgeThree (k := k)).flip b).flip d
  change -wedgeWith (-⁅a, c⁆) = wedgeWith ⁅a, c⁆
  rw [map_neg, neg_neg]

/-- The Schouten bracket is symmetric in degree two. -/
theorem schouten_symmetric (r s : ⋀[k]^2 g) : schouten r s = schouten s r := by
  have h : schouten (k := k) (g := g) = schouten.flip := by
    apply exteriorSquare_bilinear_ext
    intro a b c d
    change schouten (k := k) (wedge₂ a b) (wedge₂ c d) = schouten (wedge₂ c d) (wedge₂ a b)
    simp only [schouten_apply_wedgeThree]
    rw [wedgeThree_bracket_swap a b c d, wedgeThree_bracket_swap b a c d,
      wedgeThree_bracket_swap a b d c, wedgeThree_bracket_swap b a d c]
    abel
  exact LinearMap.congr_fun (LinearMap.congr_fun h r) s

private theorem exteriorAdjoint_wedgeThree (x a b c : g) :
    exteriorAdjoint (k := k) 3 x (wedgeThree a b c) =
      wedgeThree ⁅x, a⁆ b c + wedgeThree a ⁅x, b⁆ c + wedgeThree a b ⁅x, c⁆ := by
  simp only [wedgeThree_apply, exteriorAdjoint_wedge₃]

/-- The exterior adjoint action is a derivation of the Schouten bracket. -/
theorem exteriorAdjoint_schouten (x : g) (r s : ⋀[k]^2 g) :
    exteriorAdjoint 3 x (schouten r s) =
      schouten (exteriorAdjoint 2 x r) s + schouten r (exteriorAdjoint 2 x s) := by
  have h : (schouten (k := k)).compr₂ (exteriorAdjoint 3 x) =
      schouten.comp (exteriorAdjoint 2 x) + schouten.compl₂ (exteriorAdjoint 2 x) := by
    apply exteriorSquare_bilinear_ext
    intro a b c d
    change exteriorAdjoint 3 x (schouten (k := k) (wedge₂ a b) (wedge₂ c d)) =
      schouten (exteriorAdjoint 2 x (wedge₂ a b)) (wedge₂ c d) +
        schouten (wedge₂ a b) (exteriorAdjoint 2 x (wedge₂ c d))
    simp only [exteriorAdjoint_wedge₂, map_add, LinearMap.add_apply, schouten_apply_wedgeThree,
      map_sub, exteriorAdjoint_wedgeThree, leibniz_lie x a c, leibniz_lie x a d,
      leibniz_lie x b c, leibniz_lie x b d]
    abel
  exact LinearMap.congr_fun (LinearMap.congr_fun h r) s

end LieNotes.Coboundary
