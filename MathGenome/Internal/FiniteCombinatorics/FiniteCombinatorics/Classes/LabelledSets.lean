import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Classes.LabelledSets
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Classes.Foundations
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.CoefficientAlgebra
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-! Labelled sets: actual unordered components and orders of their label blocks.
Source: paper.tex, p204:W20 (labelled part).
-/
noncomputable section
attribute [local instance] Classical.propDecidable
universe u v r
open scoped BigOperators
namespace FiniteCombinatorics.Classes

abbrev FixedSetObjects := Specs.FiniteCombinatorics.Classes.LabelledSets.fixedObjectsValue
abbrev OrderedSetObjects := Specs.FiniteCombinatorics.Classes.LabelledSets.orderedObjectsValue
def fixedSetCount (A : LabelledClass.{u,v}) (k n : ℕ) : ℕ :=
  Nat.card (FixedSetObjects A k (StandardLabels.{u} n))
def labelledSetCount (A : LabelledClass.{u,v}) (n : ℕ) : ℕ :=
  Nat.card (LabelledComponentObjects A (StandardLabels.{u} n))
def orderedSetCount (A : LabelledClass.{u,v}) (k n : ℕ) : ℕ :=
  Nat.card (OrderedSetObjects A k (StandardLabels.{u} n))
def fixedSetEGF {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (k : ℕ) : PowerSeries R :=
  Series.egf (fun n => (fixedSetCount A k n : R))
def labelledSetEGF {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) : PowerSeries R :=
  Series.egf (fun n => (labelledSetCount A n : R))
def orderedSetEGF {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (k : ℕ) : PowerSeries R :=
  Series.egf (fun n => (orderedSetCount A k n : R))

instance fixedSetObjects_finite (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] : Finite (FixedSetObjects A k S) := by
  change Finite {x : LabelledComponentObjects A S // x.1.parts.card = k}
  infer_instance

theorem labelledSets_finite (A : LabelledClass.{u,v})
    (S : Type u) [Finite S] : Finite (LabelledComponentObjects A S) := inferInstance

instance orderedSetObjects_finite (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] : Finite (OrderedSetObjects A k S) := by
  classical
  change Finite ((x : FixedSetObjects A k S) × (Fin k ≃ x.1.1.parts))
  infer_instance

/-- The order is a bijection onto the actual nonempty blocks. In particular,
even equal component structures on different blocks cannot identify two orders. -/
theorem blockOrders_card (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] (x : FixedSetObjects A k S) :
    Nat.card (Fin k ≃ x.1.1.parts) = k.factorial := by
  classical
  let := Fintype.ofFinite S
  have h : Fintype.card (Fin k) = Fintype.card x.1.1.parts := by
    simpa using x.2.symm
  rw [Nat.card_eq_fintype_card, Fintype.card_equiv (Fintype.equivOfCardEq h)]
  simp

/-- Forgetting the order has constant fibre size `k!`, including `k=0`. -/
theorem orderedSetObjects_card (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] :
    Nat.card (OrderedSetObjects A k S) = k.factorial * Nat.card (FixedSetObjects A k S) := by
  classical
  let := Fintype.ofFinite (FixedSetObjects A k S)
  change Nat.card ((x : FixedSetObjects A k S) × (Fin k ≃ x.1.1.parts)) = _
  rw [Nat.card_sigma]
  simp only [blockOrders_card, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [Nat.card_eq_fintype_card, mul_comm]

theorem component_count_le (A : LabelledClass.{u,v}) (S : Type u) [Finite S]
    (x : LabelledComponentObjects A S) : x.1.parts.card ≤ Nat.card S := by
  classical
  let := Fintype.ofFinite S
  simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using x.1.card_parts_le_card

theorem fixedSetCount_above (A : LabelledClass.{u,v}) (k n : ℕ) (h : n < k) :
    fixedSetCount A k n = 0 := by
  haveI : IsEmpty (FixedSetObjects A k (StandardLabels.{u} n)) :=
    ⟨fun x => by
      have hx := component_count_le A (StandardLabels.{u} n) x.1
      rw [card_standardLabels, x.2] at hx
      exact (Nat.not_le_of_lt h) hx⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

/-- Decompose an actual unordered set by its number of blocks. The finite
range is justified by the nonemptiness and disjointness of the blocks. -/
theorem labelledSetCount_sum (A : LabelledClass.{u,v}) (n : ℕ) :
    labelledSetCount A n = ∑ k ∈ Finset.range (n + 1), fixedSetCount A k n := by
  classical
  letI : DecidableEq (StandardLabels.{u} n) := Classical.decEq _
  let := Fintype.ofFinite (LabelledComponentObjects A (StandardLabels.{u} n))
  let f : LabelledComponentObjects A (StandardLabels.{u} n) → Fin (n + 1) :=
    fun x => ⟨x.1.parts.card, Nat.lt_succ_of_le (by
      simpa using component_count_le A (StandardLabels.{u} n) x)⟩
  let e : ((k : Fin (n + 1)) × FixedSetObjects A k.val (StandardLabels.{u} n)) ≃
      LabelledComponentObjects A (StandardLabels.{u} n) := {
    toFun := fun x => x.2.1
    invFun := fun x => ⟨f x, ⟨x, rfl⟩⟩
    left_inv := by
      rintro ⟨k, x, hx⟩
      have hk : f x = k := Fin.ext hx
      subst k
      rfl
    right_inv := fun _ => rfl }
  unfold labelledSetCount
  rw [← Nat.card_congr e, Nat.card_sigma]
  exact Fin.sum_univ_eq_sum_range (fun k => fixedSetCount A k n) (n + 1)

private theorem empty_parts (S : Type u) [Finite S] [IsEmpty S]
    (P : LabelBlockPartition S) : P.parts = ∅ := by
  let := Fintype.ofFinite S
  exact P.parts_eq_empty_iff.mpr (by simp)

private def emptyComponents (A : LabelledClass.{u,v}) (S : Type u) [Finite S] [IsEmpty S] :
    LabelledComponentObjects A S := by
  classical
  letI := Fintype.ofFinite S
  letI : DecidableEq S := Classical.decEq S
  let P : LabelBlockPartition S := by
    unfold LabelBlockPartition
    simpa using (Finpartition.empty (Finset S))
  exact ⟨P, fun b => (Finset.notMem_empty b.val (empty_parts S P ▸ b.property)).elim⟩

private theorem empty_components_subsingleton (A : LabelledClass.{u,v})
    (S : Type u) [Finite S] [IsEmpty S] : Subsingleton (LabelledComponentObjects A S) := by
  constructor
  rintro ⟨P, a⟩ ⟨Q, b⟩
  have h : P = Q := Finpartition.ext (by rw [empty_parts S P, empty_parts S Q])
  subst Q
  congr 1
  funext x
  exact (Finset.notMem_empty x.val (empty_parts S P ▸ x.property)).elim

theorem labelledSetCount_zero (A : LabelledClass.{u,v}) : labelledSetCount A 0 = 1 := by
  haveI := empty_components_subsingleton A (StandardLabels.{u} 0)
  haveI : Nonempty (LabelledComponentObjects A (StandardLabels.{u} 0)) :=
    ⟨emptyComponents A _⟩
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

theorem fixedSetCount_zero (A : LabelledClass.{u,v}) (n : ℕ) :
    fixedSetCount A 0 n = if n = 0 then 1 else 0 := by
  letI : DecidableEq (StandardLabels.{u} n) := Classical.decEq _
  split_ifs with hn
  · subst n
    haveI := empty_components_subsingleton A (StandardLabels.{u} 0)
    haveI : Subsingleton (FixedSetObjects A 0 (StandardLabels.{u} 0)) :=
      inferInstanceAs (Subsingleton {x : LabelledComponentObjects A (StandardLabels.{u} 0) // _})
    haveI : Nonempty (FixedSetObjects A 0 (StandardLabels.{u} 0)) :=
      ⟨⟨emptyComponents A _, by rw [empty_parts]; rfl⟩⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  · haveI : IsEmpty (FixedSetObjects A 0 (StandardLabels.{u} n)) := ⟨fun x => by
      have hp : x.1.1.parts = ∅ := Finset.card_eq_zero.mp x.2
      have hu := x.1.1.parts_eq_empty_iff.mp hp
      have : Nat.card (StandardLabels.{u} n) = 0 := by
        let := Fintype.ofFinite (StandardLabels.{u} n)
        rw [Nat.card_eq_fintype_card, ← Finset.card_univ, hu]
        rfl
      exact hn ((card_standardLabels n).symm.trans this)⟩
    exact Nat.card_of_isEmpty

theorem fixedSetEGF_zero {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) : fixedSetEGF (R := R) A 0 = 1 := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp [fixedSetEGF, fixedSetCount_zero]
  · simp [fixedSetEGF, fixedSetCount_zero, hn, PowerSeries.coeff_one]

/-- All fixed-block EGFs can be summed coefficientwise over a finite range. -/
theorem coeff_labelledSetEGF {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (n : ℕ) :
    PowerSeries.coeff n (labelledSetEGF (R := R) A) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff n (fixedSetEGF (R := R) A k) := by
  simp only [labelledSetEGF, fixedSetEGF, Series.coeff_egf,
    labelledSetCount_sum, Nat.cast_sum, Finset.sum_mul]

theorem orderedSetEGF_eq_factorial_mul {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (k : ℕ) :
    orderedSetEGF (R := R) A k = PowerSeries.C (k.factorial : R) * fixedSetEGF A k := by
  apply PowerSeries.ext
  intro n
  simp only [orderedSetEGF, fixedSetEGF, Series.coeff_egf, PowerSeries.coeff_C_mul,
    orderedSetCount, fixedSetCount, orderedSetObjects_card, Nat.cast_mul, mul_assoc]

/-- The purely algebraic step from the ordered EGF to the fixed-block EGF.
The block enumeration below supplies the ordered EGF identity independently. -/
theorem fixedSetEGF_of_ordered {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (k : ℕ)
    (h : orderedSetEGF (R := R) A k = A.egf ^ k) :
    fixedSetEGF (R := R) A k =
      PowerSeries.C (algebraMap ℚ R ((k.factorial : ℚ)⁻¹)) * A.egf ^ k := by
  rw [← h, orderedSetEGF_eq_factorial_mul, ← mul_assoc, ← map_mul]
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hunit : algebraMap ℚ R ((k.factorial : ℚ)⁻¹) * (k.factorial : R) = 1 := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, inv_mul_cancel₀ hk, map_one]
  rw [hunit, map_one, one_mul]

/-- Formal exponential substitution, written as the finite sum that supplies
each coefficient. No topology or analytic convergence is involved. -/
theorem coeff_formalExp {R : Type r} [CommRing R] [Algebra ℚ R]
    (F : PowerSeries R) (hF : F.constantCoeff = 0) (n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.exp R).subst F) =
      ∑ k ∈ Finset.range (n + 1),
        algebraMap ℚ R ((k.factorial : ℚ)⁻¹) * PowerSeries.coeff n (F ^ k) := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' hF)]
  simp only [PowerSeries.coeff_exp, one_div, smul_eq_mul]
  apply finsum_eq_sum_of_support_subset
  intro k hk
  apply Finset.mem_range.mpr
  by_contra hkn
  have hnk : n < k := Nat.lt_of_succ_le (Nat.le_of_not_gt hkn)
  have hz : PowerSeries.coeff n (F ^ k) = 0 := by
    apply PowerSeries.coeff_of_lt_order
    exact lt_of_lt_of_le (by exact_mod_cast hnk)
      (PowerSeries.le_order_pow_of_constantCoeff_eq_zero k hF)
  exact hk (by simp [hz])

/-- Assemble the total EGF from its fixed-block EGFs, using the finite support
bound on the coefficient of each power. -/
theorem labelledSetEGF_of_fixed {R : Type r} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (h0 : A.count 0 = 0)
    (hfixed : ∀ k, fixedSetEGF (R := R) A k =
      PowerSeries.C (algebraMap ℚ R ((k.factorial : ℚ)⁻¹)) * A.egf ^ k) :
    labelledSetEGF (R := R) A = (PowerSeries.exp R).subst A.egf := by
  have hA : (A.egf (R := R)).constantCoeff = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, LabelledClass.coeff_egf, h0]
    simp
  apply PowerSeries.ext
  intro n
  rw [coeff_labelledSetEGF, coeff_formalExp _ hA]
  apply Finset.sum_congr rfl
  intro k _
  rw [hfixed, PowerSeries.coeff_C_mul]

end FiniteCombinatorics.Classes

namespace FiniteCombinatorics.Classes.LabelledSetEnumeration
/-! Weighted partitions give a direct proof of the fixed-block formula. Marking
one of the `k+1` blocks removes it and leaves a partition of its complement.
This recurrence, together with the binomial subset count, matches multiplication
of EGFs. Decoration counts are related to these weights only after the purely
partition-theoretic calculation, so the desired generating function is never
used to define the objects or their counts. -/
variable {α : Type*} [DecidableEq α] [Fintype α] {s b : Finset α}

theorem avoid_parts_of_mem (P : Finpartition s) (hb : b ∈ P.parts) :
    (P.avoid b).parts = P.parts.erase b := by
  ext c
  rw [P.mem_avoid, Finset.mem_erase]
  constructor
  · rintro ⟨d, hd, hnd, rfl⟩
    have hdb : d ≠ b := fun he => hnd (he ▸ le_rfl)
    have hdiff : d \ b = d := by simpa only [id_eq] using (P.disjoint hd hb hdb).sdiff_eq_left
    rw [hdiff]
    exact ⟨hdb, hd⟩
  · rintro ⟨hcb, hc⟩
    refine ⟨c, hc, ?_, (P.disjoint hc hb hcb).sdiff_eq_left⟩
    intro hle
    exact P.ne_bot hc ((P.disjoint hc hb hcb).eq_bot_of_le hle)

def appendBlock (b : {b : Finset α // b ⊆ s ∧ b.Nonempty})
    (Q : Finpartition (s \ b.val)) : Finpartition s :=
  Q.extend (Finset.nonempty_iff_ne_empty.mp b.2.2) disjoint_sdiff_self_left
    (Finset.sdiff_union_of_subset b.2.1)

theorem appendBlock_parts (b : {b : Finset α // b ⊆ s ∧ b.Nonempty})
    (Q : Finpartition (s \ b.val)) :
    (appendBlock b Q).parts = insert b.val Q.parts := rfl

theorem block_not_mem (b : {b : Finset α // b ⊆ s ∧ b.Nonempty})
    (Q : Finpartition (s \ b.val)) : b.val ∉ Q.parts := by
  intro hb
  have hd : Disjoint b.val b.val := disjoint_sdiff_self_left.mono_left (Q.le hb)
  exact (Finset.nonempty_iff_ne_empty.mp b.2.2) (disjoint_self.mp hd)

/-- Remove the marked block; insertion of that block is the inverse. -/
def markedPartitionEquiv (s : Finset α) :
    ((P : Finpartition s) × P.parts) ≃
      ((b : {b : Finset α // b ⊆ s ∧ b.Nonempty}) × Finpartition (s \ b.val)) where
  toFun x := ⟨⟨x.2.val, x.1.le x.2.property, x.1.nonempty_of_mem_parts x.2.property⟩,
    x.1.avoid x.2.val⟩
  invFun y := ⟨appendBlock y.1 y.2, ⟨y.1.val, by rw [appendBlock_parts]; simp⟩⟩
  left_inv := by
    rintro ⟨P, b, hb⟩
    have h : appendBlock ⟨b, P.le hb, P.nonempty_of_mem_parts hb⟩ (P.avoid b) = P := by
      apply Finpartition.ext
      rw [appendBlock_parts, avoid_parts_of_mem P hb, Finset.insert_erase hb]
    apply Sigma.ext h
    exact (Subtype.heq_iff_coe_eq (fun a => by dsimp only; rw [h])).mpr rfl
  right_inv := by
    rintro ⟨b, Q⟩
    apply Sigma.ext (by apply Subtype.ext; rfl)
    apply heq_of_eq
    change (appendBlock b Q).avoid b.val = Q
    apply Finpartition.ext
    rw [avoid_parts_of_mem _ (by rw [appendBlock_parts]; simp), appendBlock_parts,
      Finset.erase_insert (block_not_mem b Q)]

variable {R : Type*} [CommRing R]

def weight (a : ℕ → R) {s : Finset α} (P : Finpartition s) : R :=
  ∏ b ∈ P.parts, a b.card

def partitionSum (a : ℕ → R) (k : ℕ) (s : Finset α) : R :=
  ∑ P : Finpartition s, if P.parts.card = k then weight a P else 0

theorem weight_append (a : ℕ → R) (b : {b : Finset α // b ⊆ s ∧ b.Nonempty})
    (Q : Finpartition (s \ b.val)) :
    weight a (appendBlock b Q) = a b.val.card * weight a Q := by
  simp [weight, appendBlock_parts, block_not_mem b Q]

theorem card_append (b : {b : Finset α // b ⊆ s ∧ b.Nonempty})
    (Q : Finpartition (s \ b.val)) :
    (appendBlock b Q).parts.card = Q.parts.card + 1 := by
  rw [appendBlock_parts, Finset.card_insert_of_notMem (block_not_mem b Q)]

/-- Count a partition with one distinguished block in two ways. -/
theorem partitionSum_succ (a : ℕ → R) (ha : a 0 = 0) (k : ℕ) (s : Finset α) :
    (k + 1 : R) * partitionSum a (k + 1) s =
      ∑ b ∈ s.powerset, a b.card * partitionSum a k (s \ b) := by
  calc
    _ = ∑ P : Finpartition s, ∑ _b : P.parts,
          if P.parts.card = k + 1 then weight a P else 0 := by
      rw [partitionSum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      by_cases hp : P.parts.card = k + 1 <;> simp [hp]
    _ = ∑ x : ((P : Finpartition s) × P.parts),
          if x.1.parts.card = k + 1 then weight a x.1 else 0 :=
      (Fintype.sum_sigma' _).symm
    _ = ∑ y : ((b : {b : Finset α // b ⊆ s ∧ b.Nonempty}) × Finpartition (s \ b.val)),
          if y.2.parts.card = k then a y.1.val.card * weight a y.2 else 0 := by
      symm
      apply Fintype.sum_equiv (markedPartitionEquiv s).symm
      intro y
      change (if y.2.parts.card = k then _ else 0) =
        (if (appendBlock y.1 y.2).parts.card = k + 1 then weight a (appendBlock y.1 y.2) else 0)
      rw [card_append, weight_append]
      simp only [Nat.add_right_cancel_iff]
    _ = ∑ b : {b : Finset α // b ⊆ s ∧ b.Nonempty},
          a b.val.card * partitionSum a k (s \ b.val) := by
      trans ∑ b : {b : Finset α // b ⊆ s ∧ b.Nonempty},
        ∑ Q : Finpartition (s \ b.val),
          if Q.parts.card = k then a b.val.card * weight a Q else 0
      · exact Fintype.sum_sigma' (fun (b : {b : Finset α // b ⊆ s ∧ b.Nonempty})
          (Q : Finpartition (s \ b.val)) =>
          if Q.parts.card = k then a b.val.card * weight a Q else 0)
      · apply Finset.sum_congr rfl
        intro b _
        simp only [partitionSum, Finset.mul_sum, mul_ite, mul_zero]
    _ = ∑ b ∈ s.powerset.filter Finset.Nonempty,
          a b.card * partitionSum a k (s \ b) := by
      symm
      apply Finset.sum_subtype
      intro b
      simp
    _ = _ := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro b hb hbn
      have hbe : b = ∅ := by
        by_contra hn
        exact hbn (Finset.mem_filter.mpr ⟨hb, Finset.nonempty_iff_ne_empty.mpr hn⟩)
      simp [hbe, ha]


theorem partitionSum_zero (a : ℕ → R) (s : Finset α) :
    partitionSum a 0 s = if s = ∅ then 1 else 0 := by
  by_cases hs : s = ∅
  · subst s
    letI : Unique (Finpartition (∅ : Finset α)) := {
      default := Finpartition.empty (Finset α)
      uniq := fun P => Finpartition.ext (by
        rw [P.parts_eq_empty_iff.mpr rfl]; rfl) }
    have hd : (default : Finpartition (∅ : Finset α)).parts = ∅ :=
      Finpartition.parts_eq_empty_iff.mpr rfl
    simp [partitionSum, weight, hd]
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro P _
    rw [ite_eq_right]
    intro hp
    exact hs (P.parts_eq_empty_iff.mp (Finset.card_eq_zero.mp hp))

theorem choose_factorial_ratio (n i : ℕ) (hi : i ≤ n) :
    (n.choose i : ℚ) * ((n - i).factorial : ℚ) =
      (n.factorial : ℚ) * (i.factorial : ℚ)⁻¹ := by
  rw [← div_eq_mul_inv]
  apply (eq_div_iff (by exact_mod_cast Nat.factorial_ne_zero i)).mpr
  have h : (n.choose i : ℚ) * (i.factorial : ℚ) * ((n - i).factorial : ℚ) =
      (n.factorial : ℚ) := by exact_mod_cast Nat.choose_mul_factorial_mul_factorial hi
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- The weighted partition identity, with both factorials made explicit. -/
theorem partitionSum_formula (a : ℕ → ℚ) (ha : a 0 = 0) (k : ℕ) (s : Finset α) :
    partitionSum a k s * (k.factorial : ℚ) =
      (s.card.factorial : ℚ) * PowerSeries.coeff s.card ((Series.egf a) ^ k) := by
  induction k generalizing s with
  | zero =>
    rw [partitionSum_zero]
    by_cases hs : s = ∅
    · subst s; simp
    · have hc : s.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
      simp [hs, hc, PowerSeries.coeff_one]
  | succ k ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    calc
      _ = ((k + 1 : ℚ) * partitionSum a (k + 1) s) * k.factorial := by ring
      _ = (∑ b ∈ s.powerset, a b.card * partitionSum a k (s \ b)) * k.factorial := by
        rw [partitionSum_succ a ha]
      _ = ∑ b ∈ s.powerset, a b.card * ((s.card - b.card).factorial : ℚ) *
          PowerSeries.coeff (s.card - b.card) ((Series.egf a) ^ k) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b hb
        rw [mul_assoc, ih, Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hb)]
        ring
      _ = ∑ i ∈ Finset.range (s.card + 1), (s.card.choose i : ℚ) *
          (a i * ((s.card - i).factorial : ℚ) *
            PowerSeries.coeff (s.card - i) ((Series.egf a) ^ k)) := by
        simpa only [nsmul_eq_mul] using Finset.sum_powerset_apply_card
          (fun i => a i * ((s.card - i).factorial : ℚ) *
            PowerSeries.coeff (s.card - i) ((Series.egf a) ^ k))
      _ = _ := by
        rw [pow_succ', Series.coeff_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Series.coeff_egf]
        have hh := choose_factorial_ratio s.card i (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        simp only [map_inv₀, map_natCast]
        calc
          _ = ((s.card.choose i : ℚ) * ((s.card - i).factorial : ℚ)) * a i *
              PowerSeries.coeff (s.card - i) ((Series.egf a) ^ k) := by ring
          _ = _ := by rw [hh]; ring


end FiniteCombinatorics.Classes.LabelledSetEnumeration

namespace FiniteCombinatorics.Classes
open LabelledSetEnumeration

/-- Count the independent choices of structures on each actual block. -/
theorem fixedCard_partitionSum (A : LabelledClass.{u,v}) (k : ℕ)
    (S : Type u) [Finite S] :
    (Nat.card (Specs.FiniteCombinatorics.Classes.LabelledSets.fixedObjectsValue A k S) : ℚ) =
      @partitionSum S (Classical.decEq S) ℚ _
        (fun n => (A.count n : ℚ)) k (@Finset.univ S (Fintype.ofFinite S)) := by
  letI : DecidableEq S := Classical.decEq S
  let := Fintype.ofFinite S
  change (Nat.card {x : ((P : Finpartition (Finset.univ : Finset S)) ×
    ((b : P.parts) → A.Obj ↥b.val)) // x.1.parts.card = k} : ℚ) = _
  rw [Nat.card_congr (Equiv.subtypeSigmaEquiv
    (fun P : Finpartition (Finset.univ : Finset S) => ((b : P.parts) → A.Obj ↥b.val))
    (fun P => P.parts.card = k)), Nat.card_sigma, Nat.cast_sum]
  unfold partitionSum
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype (p := fun P : Finpartition (Finset.univ : Finset S) => P.parts.card = k) (Finset.univ.filter (fun P : Finpartition (Finset.univ : Finset S) =>
    P.parts.card = k)) (by intro P; simp) (weight (fun n => (A.count n : ℚ)))]
  apply Finset.sum_congr rfl
  intro P _
  rw [Nat.card_pi, Nat.cast_prod]
  simp only [A.card_on_labels, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact Finset.prod_coe_sort P.1.parts (fun b : Finset S => (A.count b.card : ℚ))


theorem fixedSetEGF_rat (A : LabelledClass.{u,v}) (h0 : A.count 0 = 0) (k : ℕ) :
    fixedSetEGF (R := ℚ) A k =
      PowerSeries.C ((k.factorial : ℚ)⁻¹) * A.egf ^ k := by
  apply PowerSeries.ext
  intro n
  letI : DecidableEq (StandardLabels.{u} n) := Classical.decEq _
  let := Fintype.ofFinite (StandardLabels.{u} n)
  have hc : Fintype.card (StandardLabels.{u} n) = n := by
    simpa only [Nat.card_eq_fintype_card] using card_standardLabels.{u} n
  have hp := partitionSum_formula (fun j => (A.count j : ℚ)) (by simp [h0]) k
    (Finset.univ : Finset (StandardLabels.{u} n))
  rw [← fixedCard_partitionSum A k (StandardLabels.{u} n), Finset.card_univ, hc] at hp
  change (fixedSetCount A k n : ℚ) * k.factorial =
    (n.factorial : ℚ) * PowerSeries.coeff n (A.egf ^ k) at hp
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  simp only [fixedSetEGF, Series.coeff_egf, PowerSeries.coeff_C_mul, map_inv₀, map_natCast]
  field_simp
  simpa only [mul_comm] using hp


theorem map_egf_natCounts {R : Type*} [CommRing R] [Algebra ℚ R] (a : ℕ → ℕ) :
    PowerSeries.map (algebraMap ℚ R) (Series.egf (fun n => (a n : ℚ))) =
      Series.egf (fun n => (a n : R)) := by
  apply PowerSeries.ext
  intro n
  simp only [PowerSeries.coeff_map, Series.coeff_egf, map_mul, map_inv₀, map_natCast]

theorem fixedSetEGF_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (h0 : A.count 0 = 0) (k : ℕ) :
    fixedSetEGF (R := R) A k =
      PowerSeries.C (algebraMap ℚ R ((k.factorial : ℚ)⁻¹)) * A.egf ^ k := by
  have h := congrArg (PowerSeries.map (algebraMap ℚ R)) (fixedSetEGF_rat A h0 k)
  simpa only [map_mul, map_pow, PowerSeries.map_C, fixedSetEGF,
    LabelledClass.egf, map_egf_natCounts] using h

theorem labelledSetEGF_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (h0 : A.count 0 = 0) :
    labelledSetEGF (R := R) A = (PowerSeries.exp R).subst A.egf :=
  labelledSetEGF_of_fixed A h0 (fixedSetEGF_eq A h0)

theorem orderedSetEGF_eq {R : Type*} [CommRing R] [Algebra ℚ R]
    (A : LabelledClass.{u,v}) (h0 : A.count 0 = 0) (k : ℕ) :
    orderedSetEGF (R := R) A k = A.egf ^ k := by
  rw [orderedSetEGF_eq_factorial_mul, fixedSetEGF_eq A h0, ← mul_assoc, ← map_mul]
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hu : (k.factorial : R) * algebraMap ℚ R ((k.factorial : ℚ)⁻¹) = 1 := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, mul_inv_cancel₀ hk, map_one]
  rw [hu, map_one, one_mul]

end FiniteCombinatorics.Classes
