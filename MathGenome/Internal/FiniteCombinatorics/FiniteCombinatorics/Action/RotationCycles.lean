import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.RotationCycles
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.CycleIndex
import Mathlib.GroupTheory.SpecificGroups.Cyclic

namespace FiniteCombinatorics.Rotation
open scoped BigOperators

def rotation {n : ℕ} (a : ZMod n) : Equiv.Perm (ZMod n) :=
  RotationCyclesSpec.rotation a

def returnTime {n : ℕ} (a : ZMod n) : ℕ := RotationCyclesSpec.returnTime a

noncomputable def lengthVariable (n : ℕ) [NeZero n] (d : ℕ) :
    MvPolynomial (Fin (Fintype.card (ZMod n))) ℚ :=
  RotationCyclesSpec.lengthVariable n d

@[simp] theorem rotation_apply {n : ℕ} (a x : ZMod n) : rotation a x = x + a := rfl

variable {n : ℕ} [NeZero n]

theorem returnTime_eq_addOrderOf (a : ZMod n) : returnTime a = addOrderOf a := by
  rw [returnTime, RotationCyclesSpec.returnTime, ← ZMod.addOrderOf_coe _ (NeZero.ne n),
    ZMod.natCast_zmod_val]

theorem returnTime_natCast (k : ℕ) : returnTime (k : ZMod n) = n / n.gcd k := by
  rw [returnTime_eq_addOrderOf, ZMod.addOrderOf_coe _ (NeZero.ne n)]

omit [NeZero n] in
theorem rotation_pow_apply (a x : ZMod n) (m : ℕ) :
    (rotation a ^ m) x = x + m • a := by
  rw [Equiv.Perm.coe_pow]
  exact add_right_iterate_apply a x

theorem return_iff (a x : ZMod n) (m : ℕ) :
    (rotation a ^ m) x = x ↔ returnTime a ∣ m := by
  rw [rotation_pow_apply, add_eq_left, returnTime_eq_addOrderOf,
    addOrderOf_dvd_iff_nsmul_eq_zero]

theorem returnTime_bounds (a : ZMod n) :
    0 < returnTime a ∧ returnTime a ≤ n ∧ returnTime a ∣ n := by
  rw [returnTime_eq_addOrderOf]
  have hd : addOrderOf a ∣ n := by simpa only [ZMod.card] using (addOrderOf_dvd_card (x := a))
  exact ⟨addOrderOf_pos a, Nat.le_of_dvd (NeZero.pos n) hd, hd⟩

/-- Parameterize the orbit by the distinct first d iterates. -/
theorem cyclicOrbit_card (a x : ZMod n) :
    (Permutation.cyclicOrbit (rotation a) x).card = returnTime a := by
  classical
  have he : Permutation.cyclicOrbit (rotation a) x =
      Finset.univ.image (fun i : Fin (addOrderOf a) => x + i.val • a) := by
    ext y
    rw [Permutation.mem_cyclicOrbit_iff_pow, Finset.mem_image]
    constructor
    · rintro ⟨m, rfl⟩
      refine ⟨⟨m % addOrderOf a, Nat.mod_lt _ (addOrderOf_pos a)⟩, Finset.mem_univ _, ?_⟩
      simp only [rotation_pow_apply, mod_addOrderOf_nsmul]
    · rintro ⟨i, _, rfl⟩
      exact ⟨i.val, rotation_pow_apply a x i.val⟩
  rw [he, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin,
    returnTime_eq_addOrderOf]
  intro i j hij
  apply Fin.ext
  exact nsmul_injOn_Iio_addOrderOf i.isLt j.isLt (add_left_cancel hij)


theorem cycle_card (a : ZMod n) (C : Finset (ZMod n))
    (hC : C ∈ Permutation.cycles (rotation a)) : C.card = returnTime a := by
  obtain ⟨x, rfl⟩ := (Permutation.mem_cycles (rotation a) C).mp hC
  exact cyclicOrbit_card a x

/-- All cycles have the common length, and partition the n positions. -/
theorem cycles_card_mul (a : ZMod n) :
    (Permutation.cycles (rotation a)).card * returnTime a = n := by
  calc
    _ = ∑ C ∈ Permutation.cycles (rotation a), Permutation.cycleLength C := by
      symm
      exact Finset.sum_const_nat (fun C hC => cycle_card a C hC)
    _ = _ := by simpa only [ZMod.card] using Permutation.sum_cycleLength (rotation a)

theorem cycles_card (a : ZMod n) :
    (Permutation.cycles (rotation a)).card = n / returnTime a := by
  calc
    _ = ((Permutation.cycles (rotation a)).card * returnTime a) / returnTime a :=
      (Nat.mul_div_cancel _ (returnTime_bounds a).1).symm
    _ = _ := by rw [cycles_card_mul]

theorem countCyclesOfLength_eq (a : ZMod n) (k : ℕ) :
    Permutation.countCyclesOfLength (rotation a) k =
      if k = returnTime a then n / returnTime a else 0 := by
  classical
  change ((Permutation.cycles (rotation a)).filter
    (fun C => Permutation.cycleLength C = k)).card = _
  by_cases hk : k = returnTime a
  · rw [ite_eq_left hk, Finset.filter_eq_self.mpr ?_, cycles_card]
    intro C hC
    exact (cycle_card a C hC).trans hk.symm
  · rw [ite_eq_right hk]
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro C hC hlen
    exact hk (hlen.symm.trans (cycle_card a C hC))

theorem permutationMonomial_eq (a : ZMod n) :
    Action.permutationMonomial (ZMod n) (rotation a) =
      lengthVariable n (returnTime a) ^ (n / returnTime a) := by
  classical
  obtain ⟨hdpos, hdle, _⟩ := returnTime_bounds a
  let i : Fin (Fintype.card (ZMod n)) :=
    ⟨returnTime a - 1, by rw [ZMod.card]; omega⟩
  have hi : i.val + 1 = returnTime a := by dsimp [i]; omega
  unfold Action.permutationMonomial
  rw [Finset.prod_eq_single i]
  · rw [countCyclesOfLength_eq, ite_eq_left hi]
    congr 1
    simp only [lengthVariable, RotationCyclesSpec.lengthVariable,
      dite_eq_left (show 0 < returnTime a ∧ returnTime a ≤ n from ⟨hdpos, hdle⟩)]
    rfl
  · intro j _ hji
    rw [countCyclesOfLength_eq, ite_eq_right ?_, pow_zero]
    intro h
    apply hji
    apply Fin.ext
    omega
  · simp

theorem card_returnTime_eq_totient (d : ℕ) (_hdpos : 0 < d) (hd : d ∣ n) :
    (Finset.univ.filter (fun a : ZMod n => returnTime a = d)).card = Nat.totient d := by
  classical
  simp_rw [returnTime_eq_addOrderOf]
  exact IsAddCyclic.card_addOrderOf_eq_totient (by simpa only [ZMod.card] using hd)

@[simp] theorem returnTime_zero : returnTime (0 : ZMod n) = 1 := by
  rw [returnTime_eq_addOrderOf, addOrderOf_zero]

end FiniteCombinatorics.Rotation
