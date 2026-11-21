import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.OrbitStabilizer
import Mathlib.GroupTheory.GroupAction.Quotient

/-! Fixed points, stabilizers, the orbit partition, and the orbit–stabilizer count
for the arbitrary left actions used in Chapter 5 of paper.tex. -/

namespace FiniteCombinatorics.Action

universe u v

/-- The points fixed by a single element of the acting group. -/
def fixedBy (G : Type u) (X : Type v) [Group G] [MulAction G X] (g : G) : Set X :=
  MulAction.fixedBy X g

/-- The subgroup of group elements fixing a point. -/
def stabilizer (G : Type u) (X : Type v) [Group G] [MulAction G X] (x : X) : Subgroup G :=
  MulAction.stabilizer G x

/-- The orbit under the canonical left-action interface. -/
def orbit (G : Type u) (X : Type v) [Group G] [MulAction G X] (x : X) : Set X :=
  MulAction.orbit G x

/-- Distinct orbits are disjoint and together cover the entire action set.
The stronger statement for arbitrary groups and sets includes the finite case. -/
theorem orbits_partition (G : Type u) (X : Type v) [Group G] [MulAction G X] :
    (∀ x : X, x ∈ MulAction.orbit G x) ∧
    (⋃ x : X, MulAction.orbit G x) = Set.univ ∧
    ∀ x y : X, MulAction.orbit G x = MulAction.orbit G y ∨
      Disjoint (MulAction.orbit G x) (MulAction.orbit G y) := by
  classical
  refine ⟨fun x => MulAction.mem_orbit_self x, ?_, ?_⟩
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨x, MulAction.mem_orbit_self x⟩
  · intro x y
    by_cases h : MulAction.orbit G x = MulAction.orbit G y
    · exact Or.inl h
    · right
      apply Set.disjoint_left.mpr
      intro z hzx hzy
      exact h ((MulAction.orbit_eq_iff.mpr hzx).symm.trans
        (MulAction.orbit_eq_iff.mpr hzy))

/-- Orbit–stabilizer, with no faithfulness requirement; an empty action set gives
no points to quantify over. -/
theorem orbit_card_mul_stabilizer_card (G : Type u) (X : Type v) [Group G]
    [MulAction G X] [Finite G] [Finite X] (x : X) :
    Nat.card (MulAction.orbit G x) * Nat.card (MulAction.stabilizer G x) = Nat.card G := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G x)

end FiniteCombinatorics.Action
