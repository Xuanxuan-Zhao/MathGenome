import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.FixedColorings
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.CycleIndex
import Mathlib.SetTheory.Cardinal.Finite

namespace FiniteCombinatorics.Action
open scoped BigOperators
universe u v w
variable (G : Type u) (X : Type v) (C : Type w) [Group G] [MulAction G X]

@[instance_reducible] def coloringAction : MulAction G (X → C) := arrowAction
attribute [local instance] coloringAction

def fixedColorings (g : G) := {f : X → C // g • f = f}

@[simp] theorem coloringAction_apply (g : G) (f : X → C) (x : X) :
    (g • f) x = f (g⁻¹ • x) := rfl

variable [Fintype X]
def constantOnCycles (g : G) (f : X → C) : Prop :=
  ∀ D ∈ cycles G X g, ∀ x ∈ D, ∀ y ∈ D, f x = f y

/-- Invariance under inverse precomposition is invariance along forward edges. -/
theorem coloring_fixed_iff (g : G) (f : X → C) :
    g • f = f ↔ ∀ x, f (g • x) = f x := by
  constructor
  · intro h x
    have hx := congrFun h (g • x)
    simpa using hx.symm
  · intro h
    funext x
    exact (by simpa using (h (g⁻¹ • x)).symm)

theorem coloring_fixed_iff_constant (g : G) (f : X → C) :
    g • f = f ↔ constantOnCycles G X C g f := by
  rw [coloring_fixed_iff]
  constructor
  · intro h D hD x hx y hy
    have hp (n : ℕ) (z : X) : f ((g ^ n) • z) = f z := by
      induction n with
      | zero => simp
      | succ n ih => simpa only [pow_succ', mul_smul] using (h ((g ^ n) • z)).trans ih
    have hDx : D = cyclicOrbit G X g x :=
      Permutation.eq_cyclicOrbit_of_mem (actionPermutation G X g) hD hx
    obtain ⟨n, hn⟩ := (mem_cyclicOrbit_iff_pow G X g x y).mp (hDx ▸ hy)
    rw [← hn]
    exact (hp n x).symm
  · intro h x
    exact h (cyclicOrbit G X g x)
      (Permutation.cyclicOrbit_mem_cycles (actionPermutation G X g) x)
      (g • x) ((mem_cyclicOrbit_iff_pow G X g x _).mpr ⟨1, by simp⟩)
      x (Permutation.self_mem_cyclicOrbit (actionPermutation G X g) x)


/-- The complete cycle containing a position, as an element of the cycle set. -/
noncomputable def cycleAt (g : G) (x : X) : ↥(cycles G X g) :=
  ⟨cyclicOrbit G X g x,
    Permutation.cyclicOrbit_mem_cycles (actionPermutation G X g) x⟩

theorem cycleAt_eq_of_mem (g : G) (D : ↥(cycles G X g)) (x : X)
    (hx : x ∈ D.val) : cycleAt G X g x = D := by
  apply Subtype.ext
  exact (Permutation.eq_cyclicOrbit_of_mem (actionPermutation G X g) D.property hx).symm

/-- A representative exists because every complete cycle is nonempty. -/
noncomputable def cycleRepresentative (g : G) (D : ↥(cycles G X g)) : X :=
  Classical.choose (Finset.card_pos.mp (cycleLength_bounds G X g D.val D.property).1)

theorem cycleRepresentative_mem (g : G) (D : ↥(cycles G X g)) :
    cycleRepresentative G X g D ∈ D.val :=
  Classical.choose_spec (Finset.card_pos.mp (cycleLength_bounds G X g D.val D.property).1)

/-- Assigning a color to each complete cycle gives a fixed coloring. -/
noncomputable def coloringFromCycles (g : G) (a : ↥(cycles G X g) → C) :
    fixedColorings G X C g := by
  refine ⟨fun x => a (cycleAt G X g x), (coloring_fixed_iff_constant G X C g _).mpr ?_⟩
  intro D hD x hx y hy
  exact congrArg a ((cycleAt_eq_of_mem G X g ⟨D, hD⟩ x hx).trans
    (cycleAt_eq_of_mem G X g ⟨D, hD⟩ y hy).symm)

/-- Restriction to a cycle's common color, with inverse assigning that color
at every position on the cycle. No color or position is assumed to exist. -/
noncomputable def fixedColoringsEquiv (g : G) :
    fixedColorings G X C g ≃ (↥(cycles G X g) → C) where
  toFun f D := f.val (cycleRepresentative G X g D)
  invFun := coloringFromCycles G X C g
  left_inv f := by
    apply Subtype.ext
    funext x
    exact (coloring_fixed_iff_constant G X C g f.val).mp f.property
      (cyclicOrbit G X g x) (cycleAt G X g x).property
      (cycleRepresentative G X g (cycleAt G X g x))
      (cycleRepresentative_mem G X g (cycleAt G X g x))
      x (Permutation.self_mem_cyclicOrbit (actionPermutation G X g) x)
  right_inv a := by
    funext D
    change a (cycleAt G X g (cycleRepresentative G X g D)) = a D
    rw [cycleAt_eq_of_mem G X g D _ (cycleRepresentative_mem G X g D)]

theorem fixedColoringsEquiv_apply (g : G) (f : fixedColorings G X C g)
    (D : ↥(cycles G X g)) (x : X) (hx : x ∈ D.val) :
    fixedColoringsEquiv G X C g f D = f.val x := by
  exact (coloring_fixed_iff_constant G X C g f.val).mp f.property
    D.val D.property _ (cycleRepresentative_mem G X g D) x hx

theorem fixedColorings_bijection (g : G) :
    ∃ e : fixedColorings G X C g ≃ (↥(cycles G X g) → C),
      ∀ (f : fixedColorings G X C g) (D : ↥(cycles G X g))
        (x : X), x ∈ D.val → e f D = f.val x :=
  ⟨fixedColoringsEquiv G X C g, fixedColoringsEquiv_apply G X C g⟩

/-- The number of cycles is the sum of the counts at every possible length. -/
theorem card_cycles_eq_sum_countCycles (g : G) :
    (cycles G X g).card =
      ∑ k ∈ Finset.Icc 1 (Fintype.card X), countCycles G X g k :=
  (Permutation.totalCycles_eq_card (actionPermutation G X g)).symm

theorem card_fixedColorings [Fintype C] (g : G) :
    Nat.card (fixedColorings G X C g) =
      Fintype.card C ^ (∑ k ∈ Finset.Icc 1 (Fintype.card X), countCycles G X g k) := by
  classical
  rw [Nat.card_congr (fixedColoringsEquiv G X C g), Nat.card_eq_fintype_card,
    Fintype.card_fun, Fintype.card_coe, card_cycles_eq_sum_countCycles]

theorem card_fixedColorings_empty [IsEmpty X] (g : G) :
    Nat.card (fixedColorings G X C g) = 1 := by
  classical
  rw [Nat.card_congr (fixedColoringsEquiv G X C g)]
  haveI : IsEmpty ↥(cycles G X g) := by
    rw [cycles_empty G X g]
    infer_instance
  exact Nat.card_unique

theorem fixedColorings_isEmpty [Nonempty X] [IsEmpty C] (g : G) :
    IsEmpty (fixedColorings G X C g) :=
  ⟨fun f => isEmptyElim (f.val (Classical.choice (inferInstance : Nonempty X)))⟩

end FiniteCombinatorics.Action
