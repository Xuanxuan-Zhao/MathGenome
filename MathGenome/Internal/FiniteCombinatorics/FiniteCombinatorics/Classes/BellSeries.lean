import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Classes.BellSeries
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Classes.LabelledSets
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Counting.StirlingSecond
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.Substitution

/-! The block-marking and Bell-number assertions of p204:W22.
We first identify actual block partitions with equivalence relations, preserving
block cardinality. The upstream weighted partition formula then gives the
fixed-block coefficients of `(exp z - 1)^k`. Summing the formal exponential and
cancelling `k!` proves the marked identity, including degree zero. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open FiniteCombinatorics
namespace FiniteCombinatorics.Classes.BellSeries

def bell := Specs.FiniteCombinatorics.Classes.BellSeries.bellValue
def blockPolynomial := Specs.FiniteCombinatorics.Classes.BellSeries.blockPolynomialValue

variable {α : Type*} [Fintype α] [DecidableEq α]

def partitionSetoid (P : Finpartition (Finset.univ : Finset α)) : Setoid α :=
  Setoid.ker P.part

theorem part_ofSetoid (s : Setoid α) (a b : α) :
    (Finpartition.ofSetoid s).part a = (Finpartition.ofSetoid s).part b ↔ s a b := by
  rw [← Finpartition.mem_part_iff_part_eq_part _ (Finset.mem_univ a) (Finset.mem_univ b)]
  rw [Finpartition.mem_part_ofSetoid_iff_rel]
  exact ⟨s.symm, s.symm⟩

def finpartitionEquivSetoid : Finpartition (Finset.univ : Finset α) ≃ Setoid α where
  toFun := partitionSetoid
  invFun := fun s => Finpartition.ofSetoid s
  left_inv P := by
    apply Finpartition.ext
    ext b
    constructor
    · intro hb
      obtain ⟨a, ha⟩ := (Finpartition.ofSetoid (partitionSetoid P)).nonempty_of_mem_parts hb
      have he := (Finpartition.ofSetoid (partitionSetoid P)).part_eq_of_mem hb ha
      have hh : (Finpartition.ofSetoid (partitionSetoid P)).part a = P.part a := by
        ext c
        rw [Finpartition.mem_part_ofSetoid_iff_rel]
        change P.part a = P.part c ↔ c ∈ P.part a
        exact eq_comm.trans (P.mem_part_iff_part_eq_part (by simp) (by simp)).symm
      rw [← he, hh]
      simp
    · intro hb
      obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts hb
      have hh : (Finpartition.ofSetoid (partitionSetoid P)).part a = b := by
        ext c
        rw [Finpartition.mem_part_ofSetoid_iff_rel]
        change P.part a = P.part c ↔ c ∈ b
        rw [P.part_eq_of_mem hb ha]
        exact eq_comm.trans (P.part_eq_iff_mem hb)
      rw [← hh]
      simp
  right_inv s := by
    ext a b
    exact part_ofSetoid s a b

def quotientEquivParts (P : Finpartition (Finset.univ : Finset α)) :
    Quotient (partitionSetoid P) ≃ P.parts :=
  (Quotient.congr (ra := partitionSetoid P)
    (rb := Setoid.ker (fun a => (⟨P.part a, by simp⟩ : P.parts))) (Equiv.refl α) (by
    intro a b
    change P.part a = P.part b ↔ (⟨P.part a, by simp⟩ : P.parts) = ⟨P.part b, by simp⟩
    constructor
    · intro h; exact Subtype.ext h
    · intro h; exact congrArg Subtype.val h)).trans
  (Setoid.quotientKerEquivOfSurjective
    (f := fun a => (⟨P.part a, by simp⟩ : P.parts)) (by
      intro b
      obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts b.2
      exact ⟨a, Subtype.ext (P.part_eq_of_mem b.2 ha)⟩))

theorem quotient_partitionSetoid_card (P : Finpartition (Finset.univ : Finset α)) :
    Nat.card (Quotient (partitionSetoid P)) = P.parts.card := by
  rw [Nat.card_congr (quotientEquivParts P), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem fixed_finpartition_card (k : ℕ) :
    Nat.card {P : Finpartition (Finset.univ : Finset α) // P.parts.card = k} =
      Nat.stirlingSecond (Fintype.card α) k := by
  let e := (finpartitionEquivSetoid (α := α)).subtypeEquiv
    (p := fun P => P.parts.card = k)
    (q := fun s => Nat.card (Quotient s) = k) (fun P => by
      change P.parts.card = k ↔ Nat.card (Quotient (partitionSetoid P)) = k
      rw [quotient_partitionSetoid_card])
  rw [Nat.card_congr e]
  exact StirlingSecond.card_setoids α k

/-- Group the literal unordered partitions by their block count. -/
theorem sum_by_blocks {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    (∑ P : Finpartition (Finset.univ : Finset α), f P.parts.card) =
      ∑ k ∈ Finset.range (Fintype.card α + 1),
        (Nat.stirlingSecond (Fintype.card α) k) • f k := by
  have hm : ∀ P ∈ (Finset.univ : Finset (Finpartition (Finset.univ : Finset α))),
      P.parts.card ∈ Finset.range (Fintype.card α + 1) := by
    intro P _
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (by simpa using P.card_parts_le_card))
  rw [← Finset.sum_fiberwise_of_maps_to' hm f]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_const]
  have hc := fixed_finpartition_card (α := α) k
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  rw [hc]

theorem marked_counting (α : Type*) [Fintype α] [DecidableEq α] :
    (∑ P : Finpartition (Finset.univ : Finset α), (Polynomial.X : Polynomial ℚ) ^ P.parts.card) =
      blockPolynomial (Fintype.card α) := by
  rw [sum_by_blocks]
  simp [blockPolynomial, Specs.FiniteCombinatorics.Classes.BellSeries.blockPolynomialValue,
    nsmul_eq_mul]

theorem finpartition_card :
    Nat.card (Finpartition (Finset.univ : Finset α)) = bell (Fintype.card α) := by
  have h := sum_by_blocks (α := α) (R := ℕ) (fun _ => 1)
  simpa [bell, Specs.FiniteCombinatorics.Classes.BellSeries.bellValue,
    Nat.card_eq_fintype_card] using h

theorem bell_counting (α : Type*) [Fintype α] :
    Nat.card (Setoid.Partitions α) = bell (Fintype.card α) := by
  classical
  rw [← Nat.card_congr (Setoid.Partition.orderIso (α := α)).toEquiv,
    ← Nat.card_congr (finpartitionEquivSetoid (α := α))]
  exact finpartition_card

open LabelledSetEnumeration

def nonemptyBlock (n : ℕ) : ℚ := if n = 0 then 0 else 1

theorem nonemptyBlock_egf : Series.egf nonemptyBlock = PowerSeries.exp ℚ - 1 := by
  apply PowerSeries.ext
  intro n
  by_cases hn : n = 0
  · subst n; simp [nonemptyBlock]
  · simp [nonemptyBlock, hn, PowerSeries.coeff_one, one_div]

theorem unstructured_partitionSum (k : ℕ) :
    partitionSum nonemptyBlock k (Finset.univ : Finset α) =
      (Nat.stirlingSecond (Fintype.card α) k : ℚ) := by
  have hw (P : Finpartition (Finset.univ : Finset α)) : weight nonemptyBlock P = 1 := by
    apply Finset.prod_eq_one
    intro b hb
    exact ite_eq_right (Finset.card_ne_zero.mpr (P.nonempty_of_mem_parts hb))
  simp only [partitionSum, hw]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc := fixed_finpartition_card (α := α) k
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at hc
  exact_mod_cast hc

/-- The fixed-block formula is obtained from weighted actual partitions,
not from a definition of Stirling numbers by power-series coefficients. -/
theorem stirling_power_coeff (n k : ℕ) :
    PowerSeries.coeff n ((PowerSeries.exp ℚ - 1) ^ k) =
      (Nat.stirlingSecond n k : ℚ) * (k.factorial : ℚ) * (n.factorial : ℚ)⁻¹ := by
  have h := partitionSum_formula nonemptyBlock (by simp [nonemptyBlock]) k
    (Finset.univ : Finset (Fin n))
  rw [unstructured_partitionSum, Finset.card_univ, Fintype.card_fin, nonemptyBlock_egf] at h
  have hn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply (eq_mul_inv_iff_mul_eq₀ hn).mpr
  simpa [mul_comm] using h.symm

/-- Lift the rational fixed-block identity to any commutative rational algebra. -/
theorem stirling_power_coeff_algebra {R : Type*} [CommRing R] [Algebra ℚ R]
    (n k : ℕ) :
    PowerSeries.coeff n ((PowerSeries.exp R - 1) ^ k) =
      (Nat.stirlingSecond n k : R) * (k.factorial : R) *
        algebraMap ℚ R ((n.factorial : ℚ)⁻¹) := by
  have h := congrArg (algebraMap ℚ R) (stirling_power_coeff n k)
  rw [← PowerSeries.coeff_map] at h
  simpa only [map_pow, map_sub, PowerSeries.map_exp, map_one, map_mul, map_natCast] using h

/-- The complete block-marking formula, allowing an arbitrary marker in any
commutative rational algebra. The constant coefficient of the inner series is
zero, which makes every coefficient a finite sum. -/
theorem marked_exp {R : Type*} [CommRing R] [Algebra ℚ R] (u : R) :
    (PowerSeries.exp R).subst (PowerSeries.C u * (PowerSeries.exp R - 1)) =
      Series.egf (fun n => ∑ k ∈ Finset.range (n + 1),
        (Nat.stirlingSecond n k : R) * u ^ k) := by
  apply PowerSeries.ext
  intro n
  rw [coeff_formalExp _ (by simp), Series.coeff_egf, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_pow, ← map_pow PowerSeries.C u k, PowerSeries.coeff_C_mul,
    stirling_power_coeff_algebra]
  have hk : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hu : algebraMap ℚ R ((k.factorial : ℚ)⁻¹) * (k.factorial : R) = 1 := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, inv_mul_cancel₀ hk, map_one]
  calc
    _ = (algebraMap ℚ R ((k.factorial : ℚ)⁻¹) * (k.factorial : R)) *
        ((Nat.stirlingSecond n k : R) * u ^ k *
          algebraMap ℚ R ((n.factorial : ℚ)⁻¹)) := by ring
    _ = _ := by rw [hu, one_mul]

theorem bivariate_egf :
    (PowerSeries.exp (Polynomial ℚ)).subst
      (PowerSeries.C Polynomial.X * (PowerSeries.exp (Polynomial ℚ) - 1)) =
        Series.egf blockPolynomial := by
  change (PowerSeries.exp (Polynomial ℚ)).subst
    (PowerSeries.C Polynomial.X * (PowerSeries.exp (Polynomial ℚ) - 1)) =
      Series.egf (fun n => ∑ k ∈ Finset.range (n + 1),
        Polynomial.C (Nat.stirlingSecond n k : ℚ) * Polynomial.X ^ k)
  simpa only [Polynomial.C_eq_natCast] using marked_exp (Polynomial.X : Polynomial ℚ)

theorem bell_egf :
    Series.egf (fun n => (bell n : ℚ)) =
      (PowerSeries.exp ℚ).subst (PowerSeries.exp ℚ - 1) := by
  simpa [bell, Specs.FiniteCombinatorics.Classes.BellSeries.bellValue] using (marked_exp (1 : ℚ)).symm

theorem empty_counts : bell 0 = 1 ∧ blockPolynomial 0 = 1 := by
  simp [bell, blockPolynomial, Specs.FiniteCombinatorics.Classes.BellSeries.bellValue,
    Specs.FiniteCombinatorics.Classes.BellSeries.blockPolynomialValue]

theorem formal_conditions : Specs.FiniteCombinatorics.Classes.BellSeries.FormalConditions := by
  have hq : PowerSeries.constantCoeff (PowerSeries.exp ℚ - 1) = 0 := by simp
  have hp : PowerSeries.constantCoeff
      (PowerSeries.C Polynomial.X * (PowerSeries.exp (Polynomial ℚ) - 1)) = 0 := by simp
  exact ⟨hq, PowerSeries.HasSubst.of_constantCoeff_zero' hq,
    hp, PowerSeries.HasSubst.of_constantCoeff_zero' hp⟩

end FiniteCombinatorics.Classes.BellSeries
