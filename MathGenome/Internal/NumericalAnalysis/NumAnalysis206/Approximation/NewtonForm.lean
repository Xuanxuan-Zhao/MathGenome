import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.NewtonForm
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.DividedDifferences
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.TakeDrop

/-! Newton expansion and exact backward evaluation for paper.tex W48.
The divided differences and Lagrange interpolant are the upstream constructions. -/

noncomputable section
open Polynomial
universe u
namespace NumAnalysis206.Approximation
variable {K : Type u} [Field K]
local instance : DecidableEq (K × K) := Classical.decEq _

def newtonProduct (l : List (K × K)) (k : ℕ) : K[X] :=
  Specs.NumAnalysis206.Approximation.newtonProductValue l k

def newtonPolynomial (l : List (K × K)) : K[X] :=
  Specs.NumAnalysis206.Approximation.newtonPolynomialValue l

def newtonR (l : List (K × K)) (z : K) (k : ℕ) : K :=
  Specs.NumAnalysis206.Approximation.newtonRValue l z k

@[simp] theorem newtonProduct_zero (l : List (K × K)) : newtonProduct l 0 = 1 := by
  simp [newtonProduct, Specs.NumAnalysis206.Approximation.newtonProductValue]

private theorem product_eq_nodal (l : List (K × K)) (h : l.Nodup) :
    newtonProduct l l.length = Lagrange.nodal l.toFinset Prod.fst := by
  simp only [newtonProduct, Specs.NumAnalysis206.Approximation.newtonProductValue,
    List.take_length, Lagrange.nodal]
  exact (List.prod_toFinset _ h).symm

/-- Remove the highest allowed coefficient using any monic polynomial of that
allowed degree. The argument also covers a vanishing top coefficient. -/
private theorem degree_sub_top_mul (p q : K[X]) (n : ℕ)
    (hp : p.degree < ((n + 1 : ℕ) : WithBot ℕ))
    (hq : q.Monic) (hd : q.natDegree = n) :
    (p - C (p.coeff n) * q).degree < (n : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [coeff_sub, coeff_C_mul]
  rcases eq_or_lt_of_le hm with rfl | hm
  · rw [← hd, hq.coeff_natDegree, mul_one, sub_self]
  · have hpm : p.coeff m = 0 :=
      coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp (by exact_mod_cast hm))
    have hqm : q.coeff m = 0 := coeff_eq_zero_of_natDegree_lt (by rw [hd]; exact hm)
    rw [hpm, hqm]
    simp

/-- Appending one node adds the top divided difference times the old nodal product. -/
private theorem listInterpolant_append (l : List (K × K)) (a : K × K)
    (hx : ((l ++ [a]).map Prod.fst).Nodup) :
    listInterpolant (l ++ [a]) = listInterpolant l +
      C (dividedDifference (l ++ [a])) * newtonProduct l l.length := by
  have hl : (l.map Prod.fst).Nodup := (List.nodup_append.mp (by
    simpa only [List.map_append] using hx)).1
  have hn : l.Nodup := List.Nodup.of_map Prod.fst hl
  have hc : l.toFinset.card = l.length := List.toFinset_card_of_nodup hn
  have hi : Set.InjOn (Prod.fst : K × K → K) l.toFinset := by
    intro b hb c hc hbc
    exact List.inj_on_of_nodup_map hl (List.mem_toFinset.mp hb)
      (List.mem_toFinset.mp hc) hbc
  rw [dividedDifference_eq_coeff _ (by simp) hx]
  simp only [List.length_append, List.length_singleton, Nat.add_sub_cancel]
  rw [product_eq_nodal l hn]
  let p := listInterpolant (l ++ [a])
  let q := Lagrange.nodal l.toFinset Prod.fst
  have hd : (p - C (p.coeff l.length) * q).degree < (l.toFinset.card : WithBot ℕ) := by
    rw [hc]
    exact degree_sub_top_mul p q l.length
      (by simpa [p] using listInterpolant_degree (l ++ [a]) hx)
      Lagrange.nodal_monic (by simp [q, Lagrange.natDegree_nodal, hc])
  have he : p - C (p.coeff l.length) * q = listInterpolant l := by
    apply Lagrange.eq_interpolate_of_eval_eq Prod.snd hi hd
    intro b hb
    have hbl : b ∈ l := List.mem_toFinset.mp hb
    simp only [eval_sub, eval_mul, eval_C]
    rw [show q.eval b.1 = 0 from Lagrange.eval_nodal_at_node hb,
      mul_zero, sub_zero]
    exact listInterpolant_eval _ hx b (List.mem_append_left _ hbl)
  exact sub_eq_iff_eq_add.mp he

private theorem newtonPolynomial_append (l : List (K × K)) (a : K × K) :
    newtonPolynomial (l ++ [a]) = newtonPolynomial l +
      C (dividedDifference (l ++ [a])) * newtonProduct l l.length := by
  unfold newtonPolynomial Specs.NumAnalysis206.Approximation.newtonPolynomialValue
  simp only [List.length_append, List.length_singleton, Finset.sum_range_succ]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    have hk' : k < l.length := Finset.mem_range.mp hk
    simp only [List.take_append_of_le_length (by omega : k + 1 ≤ l.length),
      Specs.NumAnalysis206.Approximation.newtonProductValue,
      List.take_append_of_le_length (Nat.le_of_lt hk')]
  · simp only [List.take_length_add_append, List.take_one,
      newtonProduct, Specs.NumAnalysis206.Approximation.newtonProductValue,
      List.take_append_of_le_length (Nat.le_refl l.length)]
    rfl

theorem newton_representation (l : List (K × K)) (hx : (l.map Prod.fst).Nodup) :
    listInterpolant l = newtonPolynomial l := by
  induction l using List.reverseRecOn with
  | nil =>
    simp [listInterpolant, Specs.NumAnalysis206.Approximation.listInterpolantValue,
      Specs.NumAnalysis206.Approximation.interpolantValue, newtonPolynomial,
      Specs.NumAnalysis206.Approximation.newtonPolynomialValue]
  | append_singleton l a ih =>
    have hl : (l.map Prod.fst).Nodup := (List.nodup_append.mp (by
      simpa only [List.map_append] using hx)).1
    rw [listInterpolant_append l a hx, newtonPolynomial_append, ih hl]

private theorem backwardValue_eq_sum (x c : ℕ → K) (z : K) (start count : ℕ) :
    Specs.NumAnalysis206.Approximation.backwardValue x c z start count =
      ∑ j ∈ Finset.range count,
        c (start + j) * ∏ i ∈ Finset.range j, (z - x (start + i)) := by
  induction count generalizing start with
  | zero => simp [Specs.NumAnalysis206.Approximation.backwardValue]
  | succ count ih =>
    rw [Specs.NumAnalysis206.Approximation.backwardValue, ih,
      Finset.sum_range_succ']
    simp only [Nat.add_zero, Finset.prod_range_zero, mul_one]
    conv_rhs => rw [add_comm]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.prod_range_succ']
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
    ring

private theorem eval_newtonProduct (l : List (K × K)) (z : K) (k : ℕ)
    (hk : k ≤ l.length) :
    (newtonProduct l k).eval z =
      ∏ j ∈ Finset.range k, (z - Specs.NumAnalysis206.Approximation.newtonNode l j) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkl : k < l.length := by omega
    have ht := List.take_concat_get' l k hkl
    unfold newtonProduct Specs.NumAnalysis206.Approximation.newtonProductValue
    rw [← ht, List.map_append, List.prod_append, List.map_singleton,
      List.prod_singleton, eval_mul]
    change (newtonProduct l k).eval z * (X - C l[k].1).eval z = _
    rw [ih (by omega), Finset.prod_range_succ]
    simp [Specs.NumAnalysis206.Approximation.newtonNode, List.getElem?_eq_getElem hkl]

theorem newton_evaluation (l : List (K × K)) (hx : (l.map Prod.fst).Nodup) (z : K) :
    (listInterpolant l).eval z = newtonR l z 0 := by
  rw [newton_representation l hx]
  unfold newtonPolynomial Specs.NumAnalysis206.Approximation.newtonPolynomialValue
  simp only [eval_finsetSum, eval_mul, eval_C]
  unfold newtonR Specs.NumAnalysis206.Approximation.newtonRValue
  rw [backwardValue_eq_sum]
  simp only [Nat.sub_zero, Nat.zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  rw [show (Specs.NumAnalysis206.Approximation.newtonProductValue l k).eval z =
      ∏ j ∈ Finset.range k, (z - Specs.NumAnalysis206.Approximation.newtonNode l j) from
    eval_newtonProduct l z k (Nat.le_of_lt (Finset.mem_range.mp hk))]

theorem newtonR_last (l : List (K × K)) (hne : l ≠ []) (z : K) :
    newtonR l z (l.length - 1) = dividedDifference l := by
  have hp : 0 < l.length := List.length_pos_iff_ne_nil.mpr hne
  have he : l.length - (l.length - 1) = 1 := by omega
  have ht : l.length - 1 + 1 = l.length := by omega
  simp [newtonR, Specs.NumAnalysis206.Approximation.newtonRValue, he,
    Specs.NumAnalysis206.Approximation.backwardValue, ht, dividedDifference]

theorem newtonR_step (l : List (K × K)) (z : K) (k : ℕ) (hk : k + 1 < l.length) :
    newtonR l z k = dividedDifference (l.take (k + 1)) +
      (z - Specs.NumAnalysis206.Approximation.newtonNode l k) * newtonR l z (k + 1) := by
  have he : l.length - k = (l.length - (k + 1)) + 1 := by omega
  unfold newtonR Specs.NumAnalysis206.Approximation.newtonRValue
  conv_lhs => rw [he, Specs.NumAnalysis206.Approximation.backwardValue]
  rfl

theorem newton_singleton (a : K × K) :
    newtonPolynomial [a] = C a.2 ∧ ∀ z : K, newtonR [a] z 0 = a.2 := by
  constructor
  · simp [newtonPolynomial, Specs.NumAnalysis206.Approximation.newtonPolynomialValue,
      Specs.NumAnalysis206.Approximation.newtonProductValue,
      Specs.NumAnalysis206.Approximation.dividedDifferenceValue]
  · intro z
    simpa using newtonR_last [a] (by simp) z

end NumAnalysis206.Approximation
