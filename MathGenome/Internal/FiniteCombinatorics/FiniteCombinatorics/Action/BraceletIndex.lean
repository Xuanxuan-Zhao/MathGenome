import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Action.BraceletIndex
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.ReflectionCycles
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Action.NecklaceIndex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Module

namespace FiniteCombinatorics.Bracelet
open scoped BigOperators
universe u v
attribute [local instance] NecklaceIndexSpec.rotationAction Action.coloringAction
attribute [local instance] Classical.propDecidable

def Bracelets := BraceletIndexSpec.Bracelets
def EmptyBracelets := BraceletIndexSpec.EmptyBracelets
noncomputable def cycleIndex := BraceletIndexSpec.cycleIndex
noncomputable def rotationIndex := BraceletIndexSpec.rotationIndex
noncomputable def inventory := BraceletIndexSpec.inventory

noncomputable local instance braceletsFintype (n : ℕ) [NeZero n]
    (C : Type u) [Fintype C] : Fintype (Bracelets n C) := by
  unfold Bracelets BraceletIndexSpec.Bracelets
  exact Fintype.ofFinite _

variable (n : ℕ) [NeZero n]

theorem bracelet_eq_iff (C : Type u) (f h : ZMod n → C) :
    Quotient.mk (MulAction.orbitRel (DihedralGroup n) (ZMod n → C)) f =
      Quotient.mk (MulAction.orbitRel (DihedralGroup n) (ZMod n → C)) h ↔
      ∃ (a : ZMod n) (e : Bool), ∀ x, f (a + if e then -x else x) = h x := by
  rw [Quotient.eq, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨⟨a, e⟩, rfl⟩ := (Reflection.pairEquiv n).surjective g
    refine ⟨a, e, fun x => ?_⟩
    have hh := congrFun hg (Reflection.pair a e • x)
    change h ((Reflection.pair a e)⁻¹ • (Reflection.pair a e • x)) = _ at hh
    rw [inv_smul_smul] at hh
    simpa only [Reflection.pair_action] using hh.symm
  · rintro ⟨a, e, ha⟩
    refine ⟨Reflection.pair a e, funext (fun x => ?_)⟩
    change h ((Reflection.pair a e)⁻¹ • x) = f x
    have hh := ha ((Reflection.pair a e)⁻¹ • x)
    rw [← Reflection.pair_action, smul_inv_smul] at hh
    exact hh.symm

private theorem rotation_permutation (a : ZMod n) :
    Action.actionPermutation (DihedralGroup n) (ZMod n) (Reflection.pair a false) =
      Action.actionPermutation (Multiplicative (ZMod n)) (ZMod n) (Multiplicative.ofAdd a) := by
  ext x
  change Reflection.pair a false • x = a + x
  simp [Reflection.pair_action]

/-- Split the average over the abstract group into its n rotations and n
reflections, even when the action has a kernel. -/
theorem cycle_index_split :
    cycleIndex n = (1 / 2 : ℚ) • rotationIndex n +
      (2 * (n : ℚ))⁻¹ • ∑ a : ZMod n,
        Reflection.reflectionMonomial a (MvPolynomial.X : ℕ → MvPolynomial ℕ ℚ) := by
  classical
  have hsum :
      (∑ g : DihedralGroup n,
        MvPolynomial.rename (fun i : Fin (Fintype.card (ZMod n)) => i.val + 1)
          (Action.elementMonomial (DihedralGroup n) (ZMod n) g)) =
      (∑ a : ZMod n,
        MvPolynomial.rename (fun i : Fin (Fintype.card (ZMod n)) => i.val + 1)
          (Action.elementMonomial (Multiplicative (ZMod n)) (ZMod n) (Multiplicative.ofAdd a))) +
        ∑ a : ZMod n, Reflection.reflectionMonomial a
          (MvPolynomial.X : ℕ → MvPolynomial ℕ ℚ) := by
    rw [← Equiv.sum_comp (Reflection.pairEquiv n)]
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, Reflection.pairEquiv,
      ReflectionSpec.pairEquiv]
    have hr (a : ZMod n) :
        Action.elementMonomial (DihedralGroup n) (ZMod n) (Reflection.pair a false) =
          Action.elementMonomial (Multiplicative (ZMod n)) (ZMod n) (Multiplicative.ofAdd a) := by
      unfold Action.elementMonomial
      rw [rotation_permutation]
    change (∑ a : ZMod n,
      (MvPolynomial.rename (fun i : Fin (Fintype.card (ZMod n)) => i.val + 1)
        (Action.elementMonomial (DihedralGroup n) (ZMod n) (Reflection.pair a true)) +
      MvPolynomial.rename (fun i : Fin (Fintype.card (ZMod n)) => i.val + 1)
        (Action.elementMonomial (DihedralGroup n) (ZMod n) (Reflection.pair a false)))) = _
    simp_rw [hr, Reflection.monomial_bridge]
    rw [Finset.sum_add_distrib, add_comm]
  change MvPolynomial.rename _ (Action.cycleIndex (DihedralGroup n) (ZMod n)) = _
  rw [Action.cycleIndex, map_smul, map_sum, hsum,
    Reflection.group_card, Nat.cast_mul, Nat.cast_ofNat, smul_add]
  congr 1
  change _ = (1 / 2 : ℚ) • MvPolynomial.rename _
    (Action.cycleIndex (Multiplicative (ZMod n)) (ZMod n))
  rw [Action.cycleIndex, map_smul, map_sum,
    ← Equiv.sum_comp Multiplicative.ofAdd]
  have hc : Fintype.card (Multiplicative (ZMod n)) = n := by simp
  rw [hc, smul_smul]
  congr 1
  field_simp

theorem cycle_index_odd (hn : Odd n) :
    cycleIndex n = (1 / 2 : ℚ) • rotationIndex n +
      (1 / 2 : ℚ) • (MvPolynomial.X 1 * MvPolynomial.X 2 ^ ((n - 1) / 2)) := by
  rw [cycle_index_split]
  simp_rw [Reflection.odd_monomial hn]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 2
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  field_simp

private theorem reflection_sum_even (hn : Even n) :
    (∑ a : ZMod n, Reflection.reflectionMonomial a
      (MvPolynomial.X : ℕ → MvPolynomial ℕ ℚ)) =
    (n / 2) • (MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 ^ ((n - 2) / 2) +
      MvPolynomial.X 2 ^ (n / 2) : MvPolynomial ℕ ℚ) := by
  simp_rw [Reflection.even_monomial hn]
  rw [Finset.sum_ite]
  have hs : Finset.univ.filter (fun a : ZMod n => a ∈ Reflection.solvableOffsets n) =
      Reflection.solvableOffsets n := by ext a; simp
  have ht : Finset.univ.filter (fun a : ZMod n => a ∉ Reflection.solvableOffsets n) =
      (Finset.univ : Finset (ZMod n)) \ Reflection.solvableOffsets n := by ext a; simp
  rw [hs, ht]
  simp only [Finset.sum_const]
  rw [(Reflection.even_distribution hn).1, (Reflection.even_distribution hn).2, smul_add]

theorem cycle_index_even (hn : Even n) :
    cycleIndex n = (1 / 2 : ℚ) • rotationIndex n +
      (1 / 4 : ℚ) • (MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 ^ ((n - 2) / 2) +
        MvPolynomial.X 2 ^ (n / 2)) := by
  rw [cycle_index_split, reflection_sum_even n hn,
    ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 2
  have hn0 : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hh : (n / 2 : ℕ) * 2 = n := Nat.div_two_mul_two_of_even hn
  have hcast := congrArg (fun k : ℕ => (k : ℚ)) hh
  push_cast at hcast
  field_simp
  nlinarith

private theorem count_substitution (C : Type u) [Fintype C] :
    (Nat.card (Bracelets n C) : ℚ) =
      MvPolynomial.eval (fun _ => (Fintype.card C : ℚ)) (cycleIndex n) := by
  change (Nat.card (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n → C)) : ℚ) =
    MvPolynomial.eval _ (MvPolynomial.rename _ (Action.cycleIndex (DihedralGroup n) (ZMod n)))
  rw [MvPolynomial.eval_rename]
  exact Action.polya (DihedralGroup n) (ZMod n) C

private theorem rotation_count_substitution (C : Type u) [Fintype C] :
    (Nat.card (Necklace.Necklaces n C) : ℚ) =
      MvPolynomial.eval (fun _ => (Fintype.card C : ℚ)) (rotationIndex n) := by
  change (Nat.card (MulAction.orbitRel.Quotient (Multiplicative (ZMod n)) (ZMod n → C)) : ℚ) =
    MvPolynomial.eval _ (MvPolynomial.rename _ (Action.cycleIndex (Multiplicative (ZMod n)) (ZMod n)))
  rw [MvPolynomial.eval_rename]
  exact Action.polya (Multiplicative (ZMod n)) (ZMod n) C

theorem bracelet_count_odd (hn : Odd n) (C : Type u) [Fintype C] :
    (Nat.card (Bracelets n C) : ℚ) =
      (1 / 2 : ℚ) * (Nat.card (Necklace.Necklaces n C) : ℚ) +
        (1 / 2 : ℚ) * ((Fintype.card C : ℚ) * (Fintype.card C : ℚ) ^ ((n - 1) / 2)) := by
  rw [count_substitution, cycle_index_odd n hn]
  simp only [map_add, MvPolynomial.smul_eval, map_mul, map_pow, MvPolynomial.eval_X]
  rw [← rotation_count_substitution]

theorem bracelet_count_even (hn : Even n) (C : Type u) [Fintype C] :
    (Nat.card (Bracelets n C) : ℚ) =
      (1 / 2 : ℚ) * (Nat.card (Necklace.Necklaces n C) : ℚ) +
        (1 / 4 : ℚ) * ((Fintype.card C : ℚ) ^ 2 * (Fintype.card C : ℚ) ^ ((n - 2) / 2) +
          (Fintype.card C : ℚ) ^ (n / 2)) := by
  rw [count_substitution, cycle_index_even n hn]
  simp only [map_add, MvPolynomial.smul_eval, map_mul, map_pow, MvPolynomial.eval_X]
  rw [← rotation_count_substitution]

private theorem weighted_substitution (C : Type u) [Fintype C] :
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun k : ℕ => ∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ k) (cycleIndex n) =
        MvPolynomial.map (Nat.castRingHom ℚ) (inventory n C) := by
  change MvPolynomial.eval₂Hom MvPolynomial.C _ (MvPolynomial.rename _
    (Action.cycleIndex (DihedralGroup n) (ZMod n))) =
      MvPolynomial.map (Nat.castRingHom ℚ)
        (Action.orbitEnumerator (DihedralGroup n) (ZMod n) C)
  rw [MvPolynomial.eval₂Hom_rename, Action.weighted_polya]
  rfl

private theorem rotation_weighted_substitution (C : Type u) [Fintype C] :
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun k : ℕ => ∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ k) (rotationIndex n) =
        MvPolynomial.map (Nat.castRingHom ℚ) (Necklace.inventory n C) := by
  change MvPolynomial.eval₂Hom MvPolynomial.C _ (MvPolynomial.rename _
    (Action.cycleIndex (Multiplicative (ZMod n)) (ZMod n))) =
      MvPolynomial.map (Nat.castRingHom ℚ)
        (Action.orbitEnumerator (Multiplicative (ZMod n)) (ZMod n) C)
  rw [MvPolynomial.eval₂Hom_rename, Action.weighted_polya]
  rfl

theorem bracelet_weighted_odd (hn : Odd n) (C : Type u) [Fintype C] :
    MvPolynomial.map (Nat.castRingHom ℚ) (inventory n C) =
      (1 / 2 : ℚ) • MvPolynomial.map (Nat.castRingHom ℚ) (Necklace.inventory n C) +
        (1 / 2 : ℚ) • ((∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ)) *
          (∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ 2) ^ ((n - 1) / 2)) := by
  rw [← weighted_substitution, cycle_index_odd n hn]
  simp only [map_add, MvPolynomial.eval₂Hom_smul, map_mul, map_pow,
    MvPolynomial.eval₂Hom_X', pow_one, rotation_weighted_substitution,
    smul_eq_mul, MvPolynomial.C_mul']

theorem bracelet_weighted_even (hn : Even n) (C : Type u) [Fintype C] :
    MvPolynomial.map (Nat.castRingHom ℚ) (inventory n C) =
      (1 / 2 : ℚ) • MvPolynomial.map (Nat.castRingHom ℚ) (Necklace.inventory n C) +
        (1 / 4 : ℚ) • ((∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ)) ^ 2 *
          (∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ 2) ^ ((n - 2) / 2) +
          (∑ c : C, (MvPolynomial.X c : MvPolynomial C ℚ) ^ 2) ^ (n / 2)) := by
  rw [← weighted_substitution, cycle_index_even n hn]
  simp only [map_add, MvPolynomial.eval₂Hom_smul, map_mul, map_pow,
    MvPolynomial.eval₂Hom_X', pow_one, rotation_weighted_substitution,
    smul_eq_mul, MvPolynomial.C_mul']

theorem inventory_coeff (C : Type u) [Fintype C] (m : C →₀ ℕ) :
    (inventory n C).coeff m = (Finset.univ.filter (fun O : Bracelets n C =>
      Action.orbitMultiplicity (DihedralGroup n) (ZMod n) C O = m)).card := by
  convert Action.orbitEnumerator_coeff (DihedralGroup n) (ZMod n) C m using 1
  · rfl
  · congr 2

theorem inventory_specialize (C : Type u) [Fintype C]
    (R : Type v) [CommSemiring R] (w : C → R) :
    MvPolynomial.eval₂ (Nat.castRingHom R) w (inventory n C) =
      ∑ O : Bracelets n C, ∏ x : ZMod n, w (O.out x) :=
  Action.orbitEnumerator_specialize (DihedralGroup n) (ZMod n) C R w

theorem bracelet_count_empty_colors (C : Type u) [Fintype C] [IsEmpty C] :
    Nat.card (Bracelets n C) = 0 := by
  unfold Bracelets BraceletIndexSpec.Bracelets
  exact Nat.card_of_isEmpty

theorem inventory_empty_colors (C : Type u) [Fintype C] [IsEmpty C] :
    inventory n C = 0 :=
  Action.orbitEnumerator_empty_colors (DihedralGroup n) (ZMod n) C

omit [NeZero n] in
theorem empty_bracelet_count (C : Type u) : Nat.card (EmptyBracelets C) = 1 := by
  unfold EmptyBracelets BraceletIndexSpec.EmptyBracelets
  exact Nat.card_unique

theorem empty_cycle_index : Action.cycleIndex (Equiv.Perm (Fin 0)) (Fin 0) = 1 :=
  Action.cycleIndex_empty _ _

theorem empty_inventory (C : Type u) [Fintype C] :
    Action.orbitEnumerator (Equiv.Perm (Fin 0)) (Fin 0) C = 1 :=
  Action.orbitEnumerator_empty_positions _ _ _

private theorem rotation_index_formula :
    rotationIndex n = (n : ℚ)⁻¹ • ∑ d ∈ n.divisors,
      (Nat.totient d : ℚ) • (MvPolynomial.X d : MvPolynomial ℕ ℚ) ^ (n / d) := by
  change MvPolynomial.rename _ (Necklace.cycleIndex n) = _
  rw [Necklace.cycle_index_formula, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  rw [map_smul, map_pow]
  congr 2
  have hpos := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) (NeZero.pos n)
  have hle := Nat.le_of_dvd (NeZero.pos n) (Nat.dvd_of_mem_divisors hd)
  simp [Rotation.lengthVariable, RotationCyclesSpec.lengthVariable, hpos, hle,
    (by omega : d - 1 + 1 = d)]

/-- The n=1 formula has no s₂ factor. -/
theorem cycle_index_one : cycleIndex 1 = MvPolynomial.X 1 := by
  have hr : rotationIndex 1 = MvPolynomial.X 1 := by
    rw [rotation_index_formula]
    norm_num
  rw [cycle_index_odd 1 (by decide), hr]
  norm_num
  module

/-- At n=2 the abstract group still has four elements, two for each
permutation in its image. -/
theorem cycle_index_two : cycleIndex 2 =
    (1 / 2 : ℚ) • (MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2) := by
  have hr : rotationIndex 2 =
      (1 / 2 : ℚ) • (MvPolynomial.X 1 ^ 2 + MvPolynomial.X 2) := by
    rw [rotation_index_formula]
    have hd : (2 : ℕ).divisors = {1, 2} := by decide
    rw [hd]
    norm_num
  rw [cycle_index_even 2 (by decide), hr]
  norm_num
  module

end FiniteCombinatorics.Bracelet
