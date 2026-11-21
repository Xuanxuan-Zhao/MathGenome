import MathGenome.Internal.NumericalAnalysis.Specs.NumAnalysis206.Approximation.DividedDifferences
import MathGenome.Internal.NumericalAnalysis.NumAnalysis206.Approximation.Lagrange
import Mathlib.Data.List.Induction
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Lattice.Lemmas
import Mathlib.Tactic.Ring

noncomputable section
open Polynomial
universe u
namespace NumAnalysis206.Approximation
variable {K : Type u} [Field K]
local instance : DecidableEq (K × K) := Classical.decEq _

def dividedDifference (l : List (K × K)) : K :=
  Specs.NumAnalysis206.Approximation.dividedDifferenceValue l

def listInterpolant (l : List (K × K)) : K[X] :=
  Specs.NumAnalysis206.Approximation.listInterpolantValue l

private theorem listInterpolant_eq (l : List (K × K)) :
    listInterpolant l = interpolant l.toFinset Prod.fst Prod.snd := rfl

@[simp] theorem dividedDifference_singleton (a : K × K) :
    dividedDifference [a] = a.2 := by
  exact Specs.NumAnalysis206.Approximation.dividedDifferenceValue.eq_2 a

theorem dividedDifference_recursion (a b : K × K) (l : List (K × K)) :
    dividedDifference (a :: (l ++ [b])) =
      (dividedDifference (l ++ [b]) - dividedDifference (a :: l)) / (b.1 - a.1) := by
  cases l with
  | nil =>
      simp [dividedDifference, Specs.NumAnalysis206.Approximation.dividedDifferenceValue]
  | cons c l =>
      change Specs.NumAnalysis206.Approximation.dividedDifferenceValue (a :: c :: (l ++ [b])) = _
      rw [Specs.NumAnalysis206.Approximation.dividedDifferenceValue.eq_3]
      simp only [← List.cons_append, List.dropLast_concat, List.getLastD_concat,
        dividedDifference]

omit [Field K] in
private theorem nodes_injOn (l : List (K × K)) (h : (l.map Prod.fst).Nodup) :
    Set.InjOn (Prod.fst : K × K → K) l.toFinset := by
  classical
  intro a ha b hb hab
  exact List.inj_on_of_nodup_map h (List.mem_toFinset.mp ha)
    (List.mem_toFinset.mp hb) hab

theorem listInterpolant_eval (l : List (K × K)) (h : (l.map Prod.fst).Nodup)
    (a : K × K) (ha : a ∈ l) : (listInterpolant l).eval a.1 = a.2 := by
  classical
  exact interpolant_eval l.toFinset Prod.fst Prod.snd (nodes_injOn l h) a
    (List.mem_toFinset.mpr ha)

theorem listInterpolant_degree (l : List (K × K)) (h : (l.map Prod.fst).Nodup) :
    (listInterpolant l).degree < (l.length : WithBot ℕ) := by
  classical
  have hc : l.toFinset.card = l.length := List.toFinset_card_of_nodup (List.Nodup.of_map Prod.fst h)
  simpa only [listInterpolant_eq, hc] using
    interpolant_degree_lt l.toFinset Prod.fst Prod.snd (nodes_injOn l h)

/-- Multiplication by a normalized linear factor shifts the highest allowed
coefficient. This also applies when that coefficient is zero. -/
private theorem coeff_mul_basisDivisor (p : K[X]) (a b : K) (n : ℕ)
    (hp : p.degree < ((n + 1 : ℕ) : WithBot ℕ)) :
    (p * Lagrange.basisDivisor a b).coeff (n + 1) = p.coeff n / (a - b) := by
  rw [Lagrange.basisDivisor, ← mul_assoc, mul_comm p (C _), mul_assoc,
    coeff_C_mul, coeff_mul_X_sub_C, coeff_eq_zero_of_degree_lt hp]
  simp [div_eq_mul_inv, mul_comm]

/-- Endpoint deletion gives the coefficient recurrence without requiring that
any interpolant have its maximal possible degree. -/
private theorem interpolant_coeff_recurrence (s : Finset (K × K))
    (hx : Set.InjOn (Prod.fst : K × K → K) s) (a b : K × K) (ha : a ∈ s) (hb : b ∈ s)
    (hab : a ≠ b) (n : ℕ) (hc : s.card = n + 2) :
    (interpolant s Prod.fst Prod.snd).coeff (n + 1) =
      ((interpolant (s.erase a) Prod.fst Prod.snd).coeff n -
        (interpolant (s.erase b) Prod.fst Prod.snd).coeff n) / (b.1 - a.1) := by
  change (Lagrange.interpolate s Prod.fst Prod.snd).coeff (n + 1) = _
  have hda : (Lagrange.interpolate (s.erase a) Prod.fst Prod.snd).degree <
      ((n + 1 : ℕ) : WithBot ℕ) := by
    simpa [hc] using Lagrange.degree_interpolate_erase_lt Prod.snd hx ha
  have hdb : (Lagrange.interpolate (s.erase b) Prod.fst Prod.snd).degree <
      ((n + 1 : ℕ) : WithBot ℕ) := by
    simpa [hc] using Lagrange.degree_interpolate_erase_lt Prod.snd hx hb
  rw [Lagrange.interpolate_eq_add_interpolate_erase Prod.snd hx ha hb hab,
    coeff_add, coeff_mul_basisDivisor _ _ _ n hdb, coeff_mul_basisDivisor _ _ _ n hda]
  change _ = ((Lagrange.interpolate (s.erase a) Prod.fst Prod.snd).coeff n -
    (Lagrange.interpolate (s.erase b) Prod.fst Prod.snd).coeff n) / (b.1 - a.1)
  rw [show a.1 - b.1 = -(b.1 - a.1) by ring, div_neg, sub_div]
  ring

private theorem listInterpolant_coeff_recurrence (a b : K × K) (l : List (K × K))
    (hx : ((a :: (l ++ [b])).map Prod.fst).Nodup) :
    (listInterpolant (a :: (l ++ [b]))).coeff (l.length + 1) =
      ((listInterpolant (l ++ [b])).coeff l.length -
        (listInterpolant (a :: l)).coeff l.length) / (b.1 - a.1) := by
  have hn : (a :: (l ++ [b])).Nodup := List.Nodup.of_map Prod.fst hx
  have ha : a ∉ l ++ [b] := (List.nodup_cons.mp hn).1
  have hb : b ∉ a :: l := by
    have hn' : ((a :: l) ++ [b]).Nodup := hn
    intro hm
    exact (List.nodup_append.mp hn').2.2 b hm b (by simp) rfl
  have hab : a ≠ b := by
    intro h
    apply ha
    simp [h]
  have hsa : (a :: (l ++ [b])).toFinset.erase a = (l ++ [b]).toFinset := by
    rw [List.toFinset_cons, Finset.erase_insert]
    exact fun h => ha (List.mem_toFinset.mp h)
  have hsb : (a :: (l ++ [b])).toFinset.erase b = (a :: l).toFinset := by
    change ((a :: l) ++ [b]).toFinset.erase b = _
    rw [List.toFinset_append, show [b].toFinset = {b} by simp,
      Finset.union_singleton, Finset.erase_insert]
    exact fun h => hb (List.mem_toFinset.mp h)
  have hc : (a :: (l ++ [b])).toFinset.card = l.length + 2 := by
    rw [List.toFinset_card_of_nodup hn]
    simp [Nat.add_comm, Nat.add_left_comm]
  have hr := interpolant_coeff_recurrence _ (nodes_injOn _ hx) a b
    (by simp) (by simp) hab l.length hc
  simpa only [hsa, hsb, listInterpolant_eq] using hr

theorem dividedDifference_eq_coeff (l : List (K × K)) (hne : l ≠ [])
    (hx : (l.map Prod.fst).Nodup) :
    dividedDifference l = (listInterpolant l).coeff (l.length - 1) := by
  induction l using WellFounded.induction (measure List.length).wf with
  | h l ih =>
    cases l with
    | nil => exact (hne rfl).elim
    | cons a l =>
      cases l using List.reverseRecOn with
      | nil =>
        simp [dividedDifference_singleton, listInterpolant_eq, interpolant,
          cardinal, Specs.NumAnalysis206.Approximation.cardinalValue]
      | append_singleton l b =>
        have ht : ((l ++ [b]).map Prod.fst).Nodup := by
          exact (List.nodup_cons.mp hx).2
        have hp : ((a :: l).map Prod.fst).Nodup := by
          have hx' : (((a :: l) ++ [b]).map Prod.fst).Nodup := hx
          exact (List.nodup_append.mp (by simpa only [List.map_append] using hx')).1
        rw [dividedDifference_recursion,
          ih (l ++ [b]) (by change (l ++ [b]).length < (a :: (l ++ [b])).length; simp) (by simp) ht,
          ih (a :: l) (by change (a :: l).length < (a :: (l ++ [b])).length; simp) (by simp) hp]
        simpa using
          (listInterpolant_coeff_recurrence a b l hx).symm

theorem dividedDifference_eq_zero_of_degree_lt (l : List (K × K)) (hne : l ≠ [])
    (hx : (l.map Prod.fst).Nodup)
    (hd : (listInterpolant l).degree < ((l.length - 1 : ℕ) : WithBot ℕ)) :
    dividedDifference l = 0 := by
  rw [dividedDifference_eq_coeff l hne hx]
  exact coeff_eq_zero_of_degree_lt hd

theorem dividedDifference_perm (l m : List (K × K)) (hne : l ≠ [])
    (hx : (l.map Prod.fst).Nodup) (hperm : l.Perm m) :
    dividedDifference l = dividedDifference m := by
  have hm : m ≠ [] := by
    intro hm
    apply hne
    apply List.eq_nil_of_length_eq_zero
    simpa only [hm, List.length_nil] using hperm.length_eq
  have hmx : (m.map Prod.fst).Nodup := (hperm.map Prod.fst).nodup_iff.mp hx
  rw [dividedDifference_eq_coeff l hne hx, dividedDifference_eq_coeff m hm hmx,
    hperm.length_eq]
  congr 1
  simp only [listInterpolant_eq]
  have hs : l.toFinset = m.toFinset := by
    ext a
    simp only [List.mem_toFinset]
    exact hperm.mem_iff
  rw [hs]

end NumAnalysis206.Approximation
