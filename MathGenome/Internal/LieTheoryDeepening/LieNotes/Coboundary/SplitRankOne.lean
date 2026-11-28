import MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.InvariantSquare
import MathGenome.Internal.LieAlgebrasAndRepresentations.LieAlgebrasAndRepresentations.Sl2Model
import Batteries.Tactic.OpenPrivate
import Mathlib.Tactic.NormNum

/-! Two explicit coboundary Lie bialgebra structures on split `sl₂`. -/

namespace LieNotes.Coboundary.SplitRankOne

open LieAlgebrasAndRepresentations (sl2 sl2_h sl2_e sl2_f sl2_basis sl2_relations sl2_expansion)

open private wedgeThree from MathGenome.Internal.LieTheoryDeepening.Specs.LieNotes.Coboundary.Schouten
open private wedgeThree_apply wedgeThree_swap schouten_apply_wedgeThree
  exteriorAdjoint_wedgeThree from MathGenome.Internal.LieTheoryDeepening.LieNotes.Coboundary.Schouten

universe u

variable (k : Type u) [Field k]

local notation "H" => sl2_h
local notation "E" => sl2_e
local notation "F" => sl2_f

/-- The bivector for the standard split rank-one cobracket. -/
def r₁ : ⋀[k]^2 (sl2 k) := wedge₂ (F k) (E k)

/-- The bivector for the triangular split rank-one cobracket. -/
def r₂ : ⋀[k]^2 (sl2 k) := wedge₂ (H k) (E k)

private theorem lie_e_h : ⁅E k, H k⁆ = (-2 : k) • E k := by
  rw [← lie_skew, (sl2_relations k).1, neg_smul]

private theorem lie_f_h : ⁅F k, H k⁆ = (2 : k) • F k := by
  rw [← lie_skew, (sl2_relations k).2.1, neg_smul, neg_neg]

private theorem lie_f_e : ⁅F k, E k⁆ = -H k := by
  rw [← lie_skew, (sl2_relations k).2.2]

section ExteriorCube

variable {k} {g : Type*} [LieRing g] [LieAlgebra k g]

private theorem wedgeThree_repeat₀₁ (a b : g) : wedgeThree (k := k) a a b = 0 := by
  rw [wedgeThree_apply]
  exact (exteriorPower.ιMulti k 3).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)

private theorem wedgeThree_repeat₀₂ (a b : g) : wedgeThree (k := k) a b a = 0 := by
  rw [wedgeThree_apply]
  exact (exteriorPower.ιMulti k 3).map_eq_zero_of_eq _ (i := 0) (j := 2) rfl (by decide)

private theorem wedgeThree_neg_first (a b c : g) :
    wedgeThree (k := k) (-a) b c = -wedgeThree a b c := by
  change (((wedgeThree (k := k)).flip b).flip c) (-a) = _
  rw [map_neg]
  rfl

private theorem wedgeThree_neg_middle (a b c : g) :
    wedgeThree (k := k) a (-b) c = -wedgeThree a b c := by
  change ((wedgeThree (k := k) a).flip c) (-b) = _
  rw [map_neg]
  rfl

private theorem schouten_decomposable_square (a b : g) :
    schouten (k := k) (wedge₂ a b) (wedge₂ a b) = (2 : k) • wedgeThree ⁅a, b⁆ a b := by
  rw [schouten_apply_wedgeThree, ← lie_skew b a, wedgeThree_swap ⁅a, b⁆ a b]
  simp only [lie_self, map_zero, LinearMap.zero_apply, wedgeThree_neg_first, zero_add,
    add_zero, sub_neg_eq_add, two_smul]

end ExteriorCube

private theorem standardSquare :
    schouten (r₁ k) (r₁ k) = (2 : k) • wedgeThree (H k) (E k) (F k) := by
  rw [r₁, schouten_decomposable_square, lie_f_e]
  rw [wedgeThree_neg_first, wedgeThree_swap (H k) (E k) (F k), neg_neg]

private theorem triangularSquare : schouten (r₂ k) (r₂ k) = 0 := by
  rw [r₂, schouten_decomposable_square, (sl2_relations k).1]
  simp only [map_smul, LinearMap.smul_apply, wedgeThree_repeat₀₂, smul_zero]

private theorem volume_invariant (x : sl2 k) :
    exteriorAdjoint (k := k) 3 x (wedgeThree (H k) (E k) (F k)) = 0 := by
  let action := (exteriorAdjoint (k := k) 3).flip (wedgeThree (H k) (E k) (F k))
  change action x = 0
  have he : action (E k) = 0 := by
    change exteriorAdjoint (k := k) 3 (E k) (wedgeThree (H k) (E k) (F k)) = 0
    simp only [exteriorAdjoint_wedgeThree, lie_e_h k, lie_self, (sl2_relations k).2.2,
      map_smul, LinearMap.smul_apply, map_zero, LinearMap.zero_apply,
      wedgeThree_repeat₀₁, wedgeThree_repeat₀₂, smul_zero, add_zero]
  have hf : action (F k) = 0 := by
    change exteriorAdjoint (k := k) 3 (F k) (wedgeThree (H k) (E k) (F k)) = 0
    simp only [exteriorAdjoint_wedgeThree, lie_f_h k, lie_f_e k, lie_self,
      map_smul, LinearMap.smul_apply, map_zero, wedgeThree_neg_middle,
      wedgeThree_repeat₀₂, wedgeThree_repeat₀₁, smul_zero, neg_zero, add_zero]
  have hh : action (H k) = 0 := by
    change exteriorAdjoint (k := k) 3 (H k) (wedgeThree (H k) (E k) (F k)) = 0
    simp only [exteriorAdjoint_wedgeThree, lie_self, (sl2_relations k).1,
      (sl2_relations k).2.1, map_smul, LinearMap.smul_apply, map_zero,
      LinearMap.zero_apply, zero_add]
    rw [← add_smul]
    norm_num
  calc
    action x = action (x.val 0 1 • E k + x.val 1 0 • F k + x.val 0 0 • H k) :=
      congrArg action (sl2_expansion k x)
    _ = 0 := by simp only [map_add, map_smul, he, hf, hh, smul_zero, add_zero]

variable [CharZero k]

/-- The first bivector yields a Lie bialgebra with the stated basis values. -/
theorem standardCobracket :
    let δ := coboundary (r₁ k)
    isLieBialgebraCobracket δ ∧
      δ (H k) = 0 ∧
      δ (E k) = wedge₂ (H k) (E k) ∧
      δ (F k) = wedge₂ (H k) (F k) := by
  obtain ⟨b, _⟩ := sl2_basis k
  let : Module.Finite k (sl2 k) := Module.Finite.of_basis b
  refine ⟨(coboundary_isLieBialgebra_iff_invariantSquare _).2 ?_, ?_, ?_, ?_⟩
  · intro x
    rw [standardSquare, map_smul, volume_invariant, smul_zero]
  · simp only [r₁, coboundary_apply, exteriorAdjoint_wedge₂, (sl2_relations k).2.1,
      (sl2_relations k).1, map_smul, LinearMap.smul_apply]
    rw [neg_smul, neg_add_cancel]
  · simp only [r₁, coboundary_apply, exteriorAdjoint_wedge₂, (sl2_relations k).2.2,
      lie_self, map_zero, add_zero]
  · simp only [r₁, coboundary_apply, exteriorAdjoint_wedge₂, lie_self, lie_f_e k,
      map_zero, LinearMap.zero_apply, map_neg, zero_add, wedge₂_swap (H k) (F k), neg_neg]

/-- The second bivector has square zero and yields the stated triangular cobracket. -/
theorem triangularCobracket :
    let δ := coboundary (r₂ k)
    isLieBialgebraCobracket δ ∧
      schouten (r₂ k) (r₂ k) = 0 ∧
      δ (H k) = (2 : k) • wedge₂ (H k) (E k) ∧
      δ (E k) = 0 ∧
      δ (F k) = (-2 : k) • wedge₂ (E k) (F k) := by
  obtain ⟨b, _⟩ := sl2_basis k
  let : Module.Finite k (sl2 k) := Module.Finite.of_basis b
  refine ⟨(coboundary_isLieBialgebra_iff_invariantSquare _).2 ?_, triangularSquare k, ?_, ?_, ?_⟩
  · intro x
    rw [triangularSquare, map_zero]
  · simp only [r₂, coboundary_apply, exteriorAdjoint_wedge₂, lie_self, (sl2_relations k).1,
      map_zero, LinearMap.zero_apply, map_smul, zero_add]
  · simp only [r₂, coboundary_apply, exteriorAdjoint_wedge₂, lie_e_h k, lie_self,
      map_zero, map_smul, LinearMap.smul_apply, wedge₂_self, smul_zero, add_zero]
  · simp only [r₂, coboundary_apply, exteriorAdjoint_wedge₂, lie_f_h k, lie_f_e k,
      map_smul, LinearMap.smul_apply, map_neg, wedge₂_self, neg_zero, add_zero,
      wedge₂_swap (E k) (F k), smul_neg]
    exact (neg_smul (2 : k) (wedge₂ (E k) (F k))).symm

end LieNotes.Coboundary.SplitRankOne
