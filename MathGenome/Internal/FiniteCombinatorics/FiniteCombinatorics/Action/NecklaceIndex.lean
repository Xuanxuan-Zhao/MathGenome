import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.NecklaceIndex
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.RotationCycles
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.Polya
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.WeightedPolya

namespace FiniteCombinatorics.Necklace
open scoped BigOperators
universe u v
attribute [local instance] NecklaceIndexSpec.rotationAction Action.coloringAction
attribute [local instance] Classical.propDecidable

@[instance_reducible] def rotationAction := NecklaceIndexSpec.rotationAction
def Necklaces := NecklaceIndexSpec.Necklaces
def EmptyNecklaces := NecklaceIndexSpec.EmptyNecklaces
noncomputable def cycleIndex := NecklaceIndexSpec.cycleIndex
noncomputable def inventory := NecklaceIndexSpec.inventory

@[simp] theorem rotation_apply (n : ℕ) (a x : ZMod n) :
    (Multiplicative.ofAdd a) • x = x + a := add_comm a x

noncomputable local instance necklacesFintype (n : ℕ) [NeZero n] (C : Type u) [Fintype C] :
    Fintype (Necklaces n C) := by
  unfold Necklaces NecklaceIndexSpec.Necklaces
  exact Fintype.ofFinite _

variable (n : ℕ) [NeZero n]

theorem necklace_eq_iff (C : Type u) (f h : ZMod n → C) :
    Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod n)) (ZMod n → C)) f =
      Quotient.mk (MulAction.orbitRel (Multiplicative (ZMod n)) (ZMod n → C)) h ↔
      ∃ a : ZMod n, ∀ x, f (x + a) = h x := by
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.toAdd, fun x => ?_⟩
    have hh := congrFun ha (x + a.toAdd)
    change h (-a.toAdd + (x + a.toAdd)) = f (x + a.toAdd) at hh
    simpa [add_assoc, add_comm, add_left_comm] using hh.symm
  · rintro ⟨a, ha⟩
    refine ⟨Multiplicative.ofAdd a, funext (fun x => ?_)⟩
    change h (-a + x) = f x
    simpa [add_assoc, add_comm, add_left_comm] using (ha (-a + x)).symm


omit [NeZero n] in
private theorem actionPermutation_eq (a : Multiplicative (ZMod n)) :
    Action.actionPermutation (Multiplicative (ZMod n)) (ZMod n) a = Rotation.rotation a.toAdd := by
  ext x
  exact add_comm _ _

private theorem sum_by_returnTime {A : Type*} [AddCommMonoid A] (F : ℕ → A) :
    (∑ a : ZMod n, F (Rotation.returnTime a)) =
      ∑ d ∈ n.divisors, Nat.totient d • F d := by
  classical
  have hmap : ∀ a ∈ (Finset.univ : Finset (ZMod n)), Rotation.returnTime a ∈ n.divisors := by
    intro a _
    exact Nat.mem_divisors.mpr ⟨(Rotation.returnTime_bounds a).2.2, NeZero.ne n⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (NeZero.pos n)
  calc
    _ = (Finset.univ.filter (fun a : ZMod n => Rotation.returnTime a = d)).card • F d := by
      rw [← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro a ha
      rw [(Finset.mem_filter.mp ha).2]
    _ = _ := by rw [Rotation.card_returnTime_eq_totient d hdpos (Nat.dvd_of_mem_divisors hd)]

theorem cycle_index_formula :
    cycleIndex n = (n : ℚ)⁻¹ • ∑ d ∈ n.divisors,
      (Nat.totient d : ℚ) • Rotation.lengthVariable n d ^ (n / d) := by
  change Action.cycleIndex (Multiplicative (ZMod n)) (ZMod n) = _
  unfold Action.cycleIndex Action.elementMonomial
  simp_rw [actionPermutation_eq, Rotation.permutationMonomial_eq]
  have hcard : Fintype.card (Multiplicative (ZMod n)) = n := by simp
  rw [hcard]
  congr 1
  rw [← Equiv.sum_comp Multiplicative.ofAdd]
  change (∑ a : ZMod n, Rotation.lengthVariable n (Rotation.returnTime a) ^
    (n / Rotation.returnTime a)) = _
  rw [sum_by_returnTime n (fun d => Rotation.lengthVariable n d ^ (n / d))]
  simp only [Nat.cast_smul_eq_nsmul]

private theorem eval_lengthVariable (d : ℕ) (hdpos : 0 < d) (hdle : d ≤ n) (q : ℚ) :
    MvPolynomial.eval (fun _ => q) (Rotation.lengthVariable n d) = q := by
  simp [Rotation.lengthVariable, RotationCyclesSpec.lengthVariable, hdpos, hdle]

private theorem substitute_lengthVariable (C : Type u) [Fintype C]
    (d : ℕ) (hdpos : 0 < d) (hdle : d ≤ n) :
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun i : Fin (Fintype.card (ZMod n)) =>
        ∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ (i.val + 1))
      (Rotation.lengthVariable n d) = ∑ c : C, MvPolynomial.X c ^ d := by
  have hsub : d - 1 + 1 = d := by omega
  simp [Rotation.lengthVariable, RotationCyclesSpec.lengthVariable, hdpos, hdle, hsub]

theorem necklace_count (C : Type u) [Fintype C] :
    (Nat.card (Necklaces n C) : ℚ) =
      (n : ℚ)⁻¹ * ∑ d ∈ n.divisors,
        (Nat.totient d : ℚ) * (Fintype.card C : ℚ) ^ (n / d) := by
  calc
    _ = MvPolynomial.eval (fun _ => (Fintype.card C : ℚ)) (cycleIndex n) :=
      Action.polya (Multiplicative (ZMod n)) (ZMod n) C
    _ = _ := by
      rw [cycle_index_formula, MvPolynomial.smul_eval, map_sum]
      simp only [MvPolynomial.smul_eval, map_pow]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      rw [eval_lengthVariable n d
        (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (NeZero.pos n))
        (Nat.le_of_dvd (NeZero.pos n) (Nat.dvd_of_mem_divisors hd))]

theorem necklace_weighted (C : Type u) [Fintype C] :
    MvPolynomial.map (Nat.castRingHom ℚ) (inventory n C) =
      (n : ℚ)⁻¹ • ∑ d ∈ n.divisors, (Nat.totient d : ℚ) •
        (∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ d) ^ (n / d) := by
  change MvPolynomial.map (Nat.castRingHom ℚ)
    (Action.orbitEnumerator (Multiplicative (ZMod n)) (ZMod n) C) = _
  rw [Action.weighted_polya]
  change MvPolynomial.eval₂Hom MvPolynomial.C
    (fun i : Fin (Fintype.card (ZMod n)) => ∑ c : C, MvPolynomial.X c ^ (i.val + 1))
    (cycleIndex n) = _
  rw [cycle_index_formula, MvPolynomial.eval₂Hom_smul, map_sum]
  simp only [MvPolynomial.eval₂Hom_smul, map_pow, smul_eq_mul, MvPolynomial.C_mul']
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [substitute_lengthVariable n C d
    (Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (NeZero.pos n))
    (Nat.le_of_dvd (NeZero.pos n) (Nat.dvd_of_mem_divisors hd))]

theorem inventory_coeff (C : Type u) [Fintype C] (m : C →₀ ℕ) :
    (inventory n C).coeff m =
      (Finset.univ.filter (fun O : Necklaces n C =>
        Action.orbitMultiplicity (Multiplicative (ZMod n)) (ZMod n) C O = m)).card := by
  convert Action.orbitEnumerator_coeff (Multiplicative (ZMod n)) (ZMod n) C m using 1
  · rfl
  · congr 2

theorem inventory_specialize (C : Type u) [Fintype C]
    (R : Type v) [CommSemiring R] (w : C → R) :
    MvPolynomial.eval₂ (Nat.castRingHom R) w (inventory n C) =
      ∑ O : Necklaces n C, ∏ x : ZMod n, w (O.out x) :=
  Action.orbitEnumerator_specialize (Multiplicative (ZMod n)) (ZMod n) C R w

theorem necklace_count_empty_colors (C : Type u) [Fintype C] [IsEmpty C] :
    Nat.card (Necklaces n C) = 0 := by
  unfold Necklaces NecklaceIndexSpec.Necklaces
  exact Nat.card_of_isEmpty

theorem inventory_empty_colors (C : Type u) [Fintype C] [IsEmpty C] :
    inventory n C = 0 :=
  Action.orbitEnumerator_empty_colors (Multiplicative (ZMod n)) (ZMod n) C

omit [NeZero n] in
-- This separate action implements the source's n=0 convention, also for no colors.
theorem empty_necklace_count (C : Type u) : Nat.card (EmptyNecklaces C) = 1 := by
  unfold EmptyNecklaces NecklaceIndexSpec.EmptyNecklaces
  exact Nat.card_unique

theorem empty_cycle_index : Action.cycleIndex (Equiv.Perm (Fin 0)) (Fin 0) = 1 :=
  Action.cycleIndex_empty _ _

theorem empty_inventory (C : Type u) [Fintype C] :
    Action.orbitEnumerator (Equiv.Perm (Fin 0)) (Fin 0) C = 1 :=
  Action.orbitEnumerator_empty_positions _ _ _

end FiniteCombinatorics.Necklace
