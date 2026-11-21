import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.CycleIndex
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.PermutationCycles
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Algebra.Module.Rat
import Mathlib.SetTheory.Cardinal.Finite

/-! The cycle index of an arbitrary finite left group action (paper.tex W31).
All cycles are complete cyclic orbits, including fixed points. -/
namespace FiniteCombinatorics

open scoped BigOperators

/-- Summing a function through a surjective group homomorphism repeats each
value exactly as many times as there are elements in the kernel. -/
theorem sum_comp_surjective_hom {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f)
    {V : Type*} [AddCommMonoid V] (F : H → V) :
    ∑ g : G, F (f g) = Nat.card f.ker • ∑ h : H, F h := by
  classical
  let : Fintype f.ker := Fintype.ofFinite _
  have hc (h : H) : Fintype.card {g : G // f g = h} = Nat.card f.ker := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr (MonoidHom.fiberEquivKerOfSurjective hf h)
  rw [← Fintype.sum_fiberwise f (fun g => F (f g))]
  simp_rw [show ∀ (h : H) (g : {g : G // f g = h}), F (f g.val) = F h from
    fun h g => congrArg F g.property]
  simp_rw [Finset.sum_const, Finset.card_univ, hc]
  rw [Finset.smul_sum]

theorem card_eq_ker_mul_card_of_surjective {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f) :
    Fintype.card G = Nat.card f.ker * Fintype.card H := by
  simpa using sum_comp_surjective_hom f hf (fun _ => (1 : ℕ))

theorem average_comp_surjective_hom {G H : Type*} [Group G] [Group H]
    [Fintype G] [Fintype H] (f : G →* H) (hf : Function.Surjective f)
    {V : Type*} [AddCommGroup V] [Module ℚ V] (F : H → V) :
    (Fintype.card G : ℚ)⁻¹ • ∑ g : G, F (f g) =
      (Fintype.card H : ℚ)⁻¹ • ∑ h : H, F h := by
  classical
  rw [sum_comp_surjective_hom f hf, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  rw [card_eq_ker_mul_card_of_surjective f hf, Nat.cast_mul]
  have hk : (Nat.card f.ker : ℚ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.card_pos (α := f.ker)).ne'
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hk, mul_one]

end FiniteCombinatorics

namespace FiniteCombinatorics.Action

open scoped BigOperators
attribute [local instance] Classical.propDecidable
universe u v
variable (G : Type u) (X : Type v) [Group G] [MulAction G X]

def actionPermutation : G →* Equiv.Perm X := MulAction.toPermHom G X

def actionImage : Subgroup (Equiv.Perm X) := (actionPermutation G X).range

@[simp] theorem actionPermutation_apply (g : G) (x : X) :
    actionPermutation G X g x = g • x := rfl

variable [Fintype X]

noncomputable def cyclicOrbit (g : G) (x : X) : Finset X :=
  Permutation.cyclicOrbit (actionPermutation G X g) x
noncomputable def cycles (g : G) : Finset (Finset X) :=
  Permutation.cycles (actionPermutation G X g)
noncomputable def countCycles (g : G) (k : ℕ) : ℕ :=
  Permutation.countCyclesOfLength (actionPermutation G X g) k

/-- Variable i represents s_(i+1). In particular i = 0 counts fixed points. -/
noncomputable def permutationMonomial (σ : Equiv.Perm X) :
    MvPolynomial (Fin (Fintype.card X)) ℚ :=
  ∏ i : Fin (Fintype.card X),
    MvPolynomial.X i ^ Permutation.countCyclesOfLength σ (i.val + 1)

noncomputable def elementMonomial (g : G) : MvPolynomial (Fin (Fintype.card X)) ℚ :=
  permutationMonomial X (actionPermutation G X g)

noncomputable def cycleIndex [Fintype G] : MvPolynomial (Fin (Fintype.card X)) ℚ :=
  (Fintype.card G : ℚ)⁻¹ • ∑ g : G, elementMonomial G X g

noncomputable def imageCycleIndex [Fintype G] : MvPolynomial (Fin (Fintype.card X)) ℚ :=
  CycleIndexSpec.imageCycleIndex G X

theorem mem_cyclicOrbit_iff_pow (g : G) (x y : X) :
    y ∈ cyclicOrbit G X g x ↔ ∃ n : ℕ, (g ^ n) • x = y := by
  rw [cyclicOrbit, Permutation.mem_cyclicOrbit_iff_pow]
  simp only [← map_pow, actionPermutation_apply]

@[simp] theorem mem_cycles (g : G) (C : Finset X) :
    C ∈ cycles G X g ↔ ∃ x, cyclicOrbit G X g x = C :=
  Permutation.mem_cycles (actionPermutation G X g) C

theorem cycles_partition (g : G) (x : X) :
    ∃! C : Finset X, C ∈ cycles G X g ∧ x ∈ C :=
  Permutation.cycles_partition (actionPermutation G X g) x

theorem cycles_pairwise_disjoint (g : G) :
    (↑(cycles G X g) : Set (Finset X)).PairwiseDisjoint id :=
  Permutation.cycles_pairwise_disjoint (actionPermutation G X g)

theorem cycles_cover (g : G) :
    (cycles G X g).biUnion id = (Finset.univ : Finset X) := by
  classical
  exact Permutation.cycles_cover (actionPermutation G X g)

theorem cycleLength_bounds (g : G) (C : Finset X) (hC : C ∈ cycles G X g) :
    0 < C.card ∧ C.card ≤ Fintype.card X :=
  Permutation.cycleLength_bounds (actionPermutation G X g) C hC

theorem sum_cycleLength (g : G) :
    ∑ C ∈ cycles G X g, C.card = Fintype.card X :=
  Permutation.sum_cycleLength (actionPermutation G X g)

theorem sum_length_mul_count (g : G) :
    ∑ k ∈ Finset.Icc 1 (Fintype.card X), k * countCycles G X g k = Fintype.card X :=
  Permutation.sum_length_mul_count (actionPermutation G X g)

theorem singleton_mem_cycles_iff (g : G) (x : X) :
    {x} ∈ cycles G X g ↔ g • x = x :=
  Permutation.singleton_mem_cycles_iff (actionPermutation G X g) x

theorem countCycles_one (g : G) :
    countCycles G X g 1 = (Finset.univ.filter (fun x : X => g • x = x)).card := by
  classical
  exact Permutation.countCyclesOfLength_one (actionPermutation G X g)

theorem countCycles_zero (g : G) : countCycles G X g 0 = 0 :=
  Permutation.countCyclesOfLength_zero (actionPermutation G X g)

theorem countCycles_eq_zero_of_gt (g : G) (k : ℕ) (hk : Fintype.card X < k) :
    countCycles G X g k = 0 :=
  Permutation.countCyclesOfLength_eq_zero_of_gt (actionPermutation G X g) k hk

@[simp] theorem cycles_empty [IsEmpty X] (g : G) : cycles G X g = ∅ :=
  Permutation.cycles_empty (actionPermutation G X g)

@[simp] theorem countCycles_empty [IsEmpty X] (g : G) (k : ℕ) :
    countCycles G X g k = 0 :=
  Permutation.countCyclesOfLength_empty (actionPermutation G X g) k

@[simp] theorem elementMonomial_empty [IsEmpty X] (g : G) :
    elementMonomial G X g = 1 := by
  classical
  simp [elementMonomial, permutationMonomial]

@[simp] theorem cycleIndex_empty [Fintype G] [IsEmpty X] : cycleIndex G X = 1 := by
  classical
  have hc : (Fintype.card G : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [cycleIndex, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, hc]

/-- Averaging over the original group agrees with averaging over its action
image, even when the action has a nontrivial kernel. -/
theorem cycleIndex_eq_imageCycleIndex [Fintype G] :
    cycleIndex G X = imageCycleIndex G X := by
  classical
  exact average_comp_surjective_hom (H := CycleIndexSpec.actionImage G X) (actionPermutation G X).rangeRestrict
    (actionPermutation G X).rangeRestrict_surjective
    (fun σ : actionImage G X => permutationMonomial X σ.val)

end FiniteCombinatorics.Action
