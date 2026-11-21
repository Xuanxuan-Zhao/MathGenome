import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Classes.Sequences
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Classes.SumProduct
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Series.MultiplicativeInverse
import Mathlib.Algebra.Ring.GeomSum
import Lean.Elab.Tactic.Omega

noncomputable section
universe v r
open scoped BigOperators
namespace FiniteCombinatorics.Classes

/-- Ordered tuples of exactly `k` objects, with additive total size. -/
def fixedLength (A : UnlabelledClass.{v}) (k : ℕ) : UnlabelledClass.{v} :=
  Specs.FiniteCombinatorics.Classes.Sequences.fixedLengthValue A k

/-- All lengths allowed by positive component sizes. -/
def sequences (A : UnlabelledClass.{v}) : UnlabelledClass.{v} :=
  Specs.FiniteCombinatorics.Classes.Sequences.sequencesValue A

theorem fixedLength_length_le (A : UnlabelledClass.{v}) (h : IsEmpty (A.Obj 0))
    (k n : ℕ) (x : (fixedLength A k).Obj n) : k ≤ n := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    change (i : Fin (n + 1)) × (A.Obj i.val × (fixedLength A k).Obj (n - i.val)) at x
    rcases x with ⟨i, a, t⟩
    have hi : i.val ≠ 0 := by
      intro hi
      exact h.false (hi ▸ a)
    have := ih (n - i.val) t
    have := i.isLt
    omega

theorem allSequences (A : UnlabelledClass.{v}) (h : IsEmpty (A.Obj 0)) (n : ℕ) :
    Nonempty ((sequences A).Obj n ≃ ((k : ℕ) × (fixedLength A k).Obj n)) := by
  exact ⟨{
    toFun := fun x => ⟨x.1.val, x.2⟩
    invFun := fun x => ⟨⟨x.1, Nat.lt_succ_of_le (fixedLength_length_le A h x.1 n x.2)⟩, x.2⟩
    left_inv := fun x => by cases x; rfl
    right_inv := fun x => by cases x; rfl }⟩

theorem sequences_locallyFinite (A : UnlabelledClass.{v}) (h : IsEmpty (A.Obj 0)) (n : ℕ) :
    Finite ((k : ℕ) × (fixedLength A k).Obj n) :=
  Finite.of_equiv _ (allSequences A h n).some

private theorem emptySequence_ogf {R : Type r} [CommRing R] :
    UnlabelledClass.ogf (R := R) (Specs.FiniteCombinatorics.Classes.Sequences.emptySequence.{v}) = 1 := by
  apply PowerSeries.ext
  intro n
  simp only [UnlabelledClass.coeff_ogf, UnlabelledClass.count,
    Specs.FiniteCombinatorics.Classes.Sequences.emptySequence, Nat.card_ulift, Nat.card_fin]
  by_cases hn : n = 0 <;> simp [hn, PowerSeries.coeff_one]

theorem fixedLength_ogf {R : Type r} [CommRing R]
    (A : UnlabelledClass.{v}) (k : ℕ) :
    (fixedLength A k).ogf (R := R) = A.ogf ^ k := by
  induction k with
  | zero => simpa [fixedLength, Specs.FiniteCombinatorics.Classes.Sequences.fixedLengthValue] using
      (emptySequence_ogf (R := R))
  | succ k ih =>
    change (unlabelledProduct A (fixedLength A k)).ogf = _
    rw [unlabelledProduct_ogf, ih, pow_succ']

theorem sequences_count_zero (A : UnlabelledClass.{v}) : (sequences A).count 0 = 1 := by
  change Nat.card ((k : Fin 1) ×
    (Specs.FiniteCombinatorics.Classes.Sequences.fixedLengthValue A k.val).Obj 0) = 1
  rw [Nat.card_sigma]
  simp [Specs.FiniteCombinatorics.Classes.Sequences.fixedLengthValue,
    Specs.FiniteCombinatorics.Classes.Sequences.emptySequence]

theorem ogf_constant_zero {R : Type r} [CommRing R]
    (A : UnlabelledClass.{v}) (h : IsEmpty (A.Obj 0)) :
    PowerSeries.constantCoeff (A.ogf (R := R)) = 0 := by
  letI := h
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, UnlabelledClass.coeff_ogf]
  simp [UnlabelledClass.count]

theorem coeff_pow_vanish {R : Type r} [CommRing R]
    (A : UnlabelledClass.{v}) (h : IsEmpty (A.Obj 0))
    (k n : ℕ) (hn : n < k) : PowerSeries.coeff n ((A.ogf (R := R)) ^ k) = 0 := by
  rw [← fixedLength_ogf A k, UnlabelledClass.coeff_ogf]
  haveI : IsEmpty ((fixedLength A k).Obj n) :=
    ⟨fun x => (Nat.not_le_of_lt hn) (fixedLength_length_le A h k n x)⟩
  simp [UnlabelledClass.count]

theorem sequences_geometric_coeff {R : Type r} [CommRing R]
    (A : UnlabelledClass.{v}) (_h : IsEmpty (A.Obj 0)) (n : ℕ) :
    PowerSeries.coeff n ((sequences A).ogf (R := R)) =
      ∑ k ∈ Finset.range (n + 1), PowerSeries.coeff n ((A.ogf) ^ k) := by
  rw [UnlabelledClass.coeff_ogf]
  change (Nat.card ((k : Fin (n + 1)) × (fixedLength A k.val).Obj n) : R) = _
  rw [Nat.card_sigma, Nat.cast_sum]
  change (∑ k : Fin (n + 1), ((fixedLength A k.val).count n : R)) = _
  simp_rw [← UnlabelledClass.coeff_ogf (R := R), fixedLength_ogf]
  exact Fin.sum_univ_eq_sum_range
    (fun k => PowerSeries.coeff n ((A.ogf (R := R)) ^ k)) (n + 1)

/-- Every degree up to `n` already agrees with the finite geometric sum. -/
private theorem sequences_coeff_partial {R : Type r} [CommRing R]
    (A : UnlabelledClass.{v}) (h : IsEmpty (A.Obj 0)) (m n : ℕ) (hmn : m ≤ n) :
    PowerSeries.coeff m ((sequences A).ogf (R := R)) =
      PowerSeries.coeff m (∑ k ∈ Finset.range (n + 1), (A.ogf (R := R)) ^ k) := by
  rw [sequences_geometric_coeff A h m, map_sum]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hmn 1))
  intro k _ hk
  apply coeff_pow_vanish A h k m
  simp only [Finset.mem_range] at hk
  omega

theorem sequences_inverse_identities {R : Type r} [CommRing R]
    (A : UnlabelledClass.{v}) (h : IsEmpty (A.Obj 0)) :
    (1 - A.ogf (R := R)) * (sequences A).ogf = 1 ∧
      (sequences A).ogf * (1 - A.ogf (R := R)) = 1 := by
  have hleft : (1 - A.ogf (R := R)) * (sequences A).ogf = 1 := by
    apply PowerSeries.ext
    intro n
    calc
      PowerSeries.coeff n ((1 - A.ogf (R := R)) * (sequences A).ogf) =
          PowerSeries.coeff n ((1 - A.ogf (R := R)) *
            ∑ k ∈ Finset.range (n + 1), (A.ogf (R := R)) ^ k) := by
        rw [Series.coeff_mul, Series.coeff_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [sequences_coeff_partial A h (n - i) n (Nat.sub_le n i)]
      _ = PowerSeries.coeff n (1 - (A.ogf (R := R)) ^ (n + 1)) := by
        rw [mul_neg_geom_sum]
      _ = PowerSeries.coeff n (1 : PowerSeries R) := by
        rw [map_sub, coeff_pow_vanish A h (n + 1) n (by omega), sub_zero]
  exact ⟨hleft, by simpa only [mul_comm] using hleft⟩

/-- The reciprocal of `1-A` over any commutative ring, expressed using its
constant unit `1`; this is the formal meaning of `1/(1-A(z))`. -/
theorem sequences_ogf_inverse {R : Type r} [CommRing R]
    (A : UnlabelledClass.{v}) (h : IsEmpty (A.Obj 0)) :
    (sequences A).ogf (R := R) = PowerSeries.invOfUnit (1 - A.ogf) 1 := by
  have hc : PowerSeries.constantCoeff (1 - A.ogf (R := R)) = ((1 : Rˣ) : R) := by
    simp [ogf_constant_zero A h]
  calc
    (sequences A).ogf (R := R) = (sequences A).ogf * 1 := (mul_one _).symm
    _ = (sequences A).ogf * ((1 - A.ogf) * PowerSeries.invOfUnit (1 - A.ogf) 1) := by
      rw [PowerSeries.mul_invOfUnit _ _ hc]
    _ = PowerSeries.invOfUnit (1 - A.ogf) 1 := by
      rw [← mul_assoc, (sequences_inverse_identities A h).2, one_mul]

end FiniteCombinatorics.Classes
