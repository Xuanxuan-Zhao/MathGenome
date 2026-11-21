import MathGenome.Internal.ExtremalOptimization.Specs.P205.Extremal.CliqueDensity
import MathGenome.Internal.ExtremalOptimization.P205.Extremal.Turan
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push

namespace P205.Extremal
open SimpleGraph Finset

/-- Interchanging the two finite incidence counts. -/
lemma sum_card_filter_swap {A B : Type*} (s : Finset A) (t : Finset B)
    (R : A → B → Prop) [DecidableRel R] :
    ∑ a ∈ s, (t.filter (R a)).card = ∑ b ∈ t, (s.filter (fun a => R a b)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]

/-- Each fixed `k`-set is contained in exactly `choose (n-k) (m-k)` samples. -/
lemma sum_subsets_in_samples {V : Type*} [Fintype V] [DecidableEq V]
    (F : Finset (Finset V)) (k m : ℕ) (hF : ∀ s ∈ F, s.card = k) (hkm : k ≤ m) :
    ∑ s ∈ (univ : Finset V).powersetCard m, (F.filter (· ⊆ s)).card =
      F.card * (Fintype.card V - k).choose (m - k) := by
  rw [sum_card_filter_swap]
  have h : ∀ t ∈ F,
      (((univ : Finset V).powersetCard m).filter (t ⊆ ·)).card =
        (Fintype.card V - k).choose (m - k) := by
    intro t ht
    rw [card_filter_powersetCard_subset t univ m (subset_univ _) (hF t ht ▸ hkm),
      card_univ, hF t ht]
  simp only [sum_congr rfl h, sum_const, nsmul_eq_mul, Nat.cast_id]

/-- The exact fixed-size sampling identity for edges. -/
lemma sum_edges_in_samples {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (m : ℕ) (hm : 2 ≤ m) :
    ∑ s ∈ (univ : Finset V).powersetCard m,
      (G.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card =
        G.edgeFinset.card * (Fintype.card V - 2).choose (m - 2) := by
  rw [sum_card_filter_swap]
  have h : ∀ e ∈ G.edgeFinset,
      (((univ : Finset V).powersetCard m).filter (e.toFinset ⊆ ·)).card =
        (Fintype.card V - 2).choose (m - 2) := by
    intro e he
    have hec : e.toFinset.card = 2 := G.card_toFinset_mem_edgeFinset ⟨e, he⟩
    rw [card_filter_powersetCard_subset e.toFinset univ m (subset_univ _) (hec ▸ hm),
      card_univ, hec]
  simp only [sum_congr rfl h, sum_const, nsmul_eq_mul, Nat.cast_id]

/-- A sample with no ambient `r`-clique is `r`-clique-free as an induced graph. -/
lemma cliqueFree_induce_of_no_clique {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V) (r : ℕ)
    (h : (G.cliqueFinset r).filter (· ⊆ s) = ∅) :
    (G.induce (s : Set V)).CliqueFree r := by
  rw [cliqueFree_induce_iff]
  intro t hts ht
  have : t ∈ (G.cliqueFinset r).filter (· ⊆ s) :=
    mem_filter.mpr ⟨mem_cliqueFinset_iff.mpr ht, hts⟩
  simp [h] at this

/-- Turán's bound, with a clique count paying for samples which contain a clique. -/
lemma edges_in_sample_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (s : Finset V)
    (r m : ℕ) (hr : 2 ≤ r) (hs : s.card = m) :
    ((G.edgeFinset.filter (fun e => e.toFinset ⊆ s)).card : ℝ) ≤
      (turanNumber m (r - 1) : ℝ) +
        (m.choose 2 : ℝ) * ((G.cliqueFinset r).filter (· ⊆ s)).card := by
  rw [card_filter_edgeFinset_toFinset_subset]
  have hcard : Fintype.card (s : Set V) = m := by simpa using hs
  by_cases h : (G.cliqueFinset r).filter (· ⊆ s) = ∅
  · simp only [h, card_empty, Nat.cast_zero, mul_zero, add_zero]
    have hc := cliqueFree_induce_of_no_clique G s r h
    rw [show r = (r - 1) + 1 by omega] at hc
    exact_mod_cast (hc.card_edgeFinset_le.trans_eq (by rw [hcard]))
  · have hk : (1 : ℝ) ≤ ((G.cliqueFinset r).filter (· ⊆ s)).card := by
      exact_mod_cast card_pos.mpr (nonempty_iff_ne_empty.mpr h)
    have he := (G.induce (s : Set V)).card_edgeFinset_le_card_choose_two
    rw [hcard] at he
    have hmul := mul_le_mul_of_nonneg_left hk (show (0 : ℝ) ≤ m.choose 2 by positivity)
    have ht : (0 : ℝ) ≤ turanNumber m (r - 1) := by positivity
    exact (by exact_mod_cast he : _ ≤ (m.choose 2 : ℝ)).trans (by nlinarith)

/-- Double-counted fixed-sample inequality, before dividing by binomial factors. -/
lemma clique_sampling_inequality {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r m : ℕ)
    (hr : 2 ≤ r) (hm : r ≤ m) :
    (G.edgeFinset.card : ℝ) * (Fintype.card V - 2).choose (m - 2) ≤
      (turanNumber m (r - 1) : ℝ) * (Fintype.card V).choose m +
        (m.choose 2 : ℝ) * (G.cliqueFinset r).card *
          (Fintype.card V - r).choose (m - r) := by
  have he := congrArg (fun a : ℕ => (a : ℝ))
    (sum_edges_in_samples G m (hr.trans hm))
  have hk := congrArg (fun a : ℕ => (a : ℝ))
    (sum_subsets_in_samples (G.cliqueFinset r) r m
      (fun t ht => (mem_cliqueFinset_iff.mp ht).card_eq) hm)
  push_cast at he hk
  have hsum := sum_le_sum (fun s (hs : s ∈ (univ : Finset V).powersetCard m) =>
    edges_in_sample_le G s r m hr (mem_powersetCard.mp hs).2)
  rw [sum_add_distrib, sum_const, nsmul_eq_mul, card_powersetCard, card_univ,
    ← mul_sum, he, hk] at hsum
  nlinarith only [hsum]

/-- A fixed sample size whose Turán number is below the density with half the margin. -/
lemma exists_clique_sample_size (r : ℕ) (hr : 2 ≤ r) (ε : ℝ) (hε : 0 < ε) :
    ∃ m : ℕ, r ≤ m ∧
      (turanNumber m (r - 1) : ℝ) ≤
        (1 - 1 / ((r : ℝ) - 1) + ε / 2) * (m.choose 2 : ℝ) := by
  obtain ⟨a, ha⟩ := exists_nat_ge (2 / ε + 1)
  let m := max r a
  have hrm : r ≤ m := le_max_left _ _
  have ham : a ≤ m := le_max_right _ _
  have hm : (2 : ℝ) ≤ m := by exact_mod_cast hr.trans hrm
  have hlarge : 2 / ε + 1 ≤ (m : ℝ) := ha.trans (by exact_mod_cast ham)
  have hprod : 2 ≤ ε * ((m : ℝ) - 1) := by
    have := (div_le_iff₀ hε).mp (show 2 / ε ≤ (m : ℝ) - 1 by linarith)
    nlinarith
  have hr' : (1 : ℝ) ≤ (r - 1 : ℕ) := by exact_mod_cast (show 1 ≤ r - 1 by omega)
  have hcast : (r - 1 : ℕ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  have ht := mul_turanNumber_le (n := m) (r := r - 1)
  have ht' : 2 * ((r : ℝ) - 1) * (turanNumber m (r - 1) : ℝ) ≤
      (((r : ℝ) - 1) - 1) * (m : ℝ) ^ 2 := by
    have hh : (r - 1 - 1 : ℕ) = ((r : ℝ) - 1) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ r - 1), hcast, Nat.cast_one]
    have htR : (2 : ℝ) * (r - 1 : ℕ) * (turanNumber m (r - 1) : ℝ) ≤
        (r - 1 - 1 : ℕ) * (m : ℝ) ^ 2 := by exact_mod_cast ht
    rwa [hcast, hh] at htR
  have hd : 0 ≤ 1 - 1 / ((r : ℝ) - 1) := by
    have hpos : (0 : ℝ) < (r : ℝ) - 1 := by linarith [hcast]
    exact sub_nonneg.mpr ((div_le_one hpos).mpr (by linarith [hcast]))
  have hd' : 1 - 1 / ((r : ℝ) - 1) ≤ 1 := by
    have hpos : (0 : ℝ) < (r : ℝ) - 1 := by linarith [hcast]
    exact sub_le_self _ (by positivity)
  have hident : ((r : ℝ) - 1) * (1 - 1 / ((r : ℝ) - 1)) = (r : ℝ) - 1 - 1 := by
    field_simp [show (r : ℝ) - 1 ≠ 0 by linarith [hcast]]
  have hbase : (turanNumber m (r - 1) : ℝ) ≤
      (1 - 1 / ((r : ℝ) - 1)) * (m : ℝ) ^ 2 / 2 := by
    nlinarith [hident, mul_pos (show (0 : ℝ) < (r : ℝ) - 1 by linarith [hcast])
      (show (0 : ℝ) < 1 by norm_num)]
  refine ⟨m, hrm, hbase.trans ?_⟩
  rw [Nat.cast_choose_two]
  have hsmall : 2 * (1 - 1 / ((r : ℝ) - 1)) ≤ ε * ((m : ℝ) - 1) := by linarith
  have := mul_le_mul_of_nonneg_left hsmall (show (0 : ℝ) ≤ m by positivity)
  nlinarith

/-- Quantitative supersaturation for any sample size with the required Turán bound. -/
lemma clique_count_from_sample {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r m : ℕ) (ε : ℝ)
    (hr : 2 ≤ r) (hrm : r ≤ m) (hmn : m ≤ Fintype.card V)
    (ht : (turanNumber m (r - 1) : ℝ) ≤
      (1 - 1 / ((r : ℝ) - 1) + ε / 2) * (m.choose 2 : ℝ))
    (he : (1 - 1 / ((r : ℝ) - 1) + ε) * ((Fintype.card V).choose 2 : ℝ) ≤
      (G.edgeFinset.card : ℝ)) :
    (ε / 2) * ((Fintype.card V).choose r : ℝ) ≤
      (m.choose r : ℝ) * (G.cliqueFinset r).card := by
  let n := Fintype.card V
  let d : ℝ := 1 - 1 / ((r : ℝ) - 1)
  have hC : (0 : ℝ) < m.choose 2 := by exact_mod_cast Nat.choose_pos (hr.trans hrm)
  have hA : (0 : ℝ) ≤ (n - 2).choose (m - 2) := by positivity
  have hS : (0 : ℝ) ≤ n.choose m := by positivity
  have hD : (0 : ℝ) < (n - r).choose (m - r) := by
    exact_mod_cast Nat.choose_pos (Nat.sub_le_sub_right hmn r)
  have hchoose : (n.choose m : ℝ) * m.choose 2 =
      (n.choose 2 : ℝ) * (n - 2).choose (m - 2) := by
    exact_mod_cast (Nat.choose_mul (n := n) (hr.trans hrm))
  have hchooseR : (n.choose m : ℝ) * m.choose r =
      (n.choose r : ℝ) * (n - r).choose (m - r) := by
    exact_mod_cast (Nat.choose_mul (n := n) hrm)
  have hsample := clique_sampling_inequality G r m hr hrm
  have hlow := mul_le_mul_of_nonneg_right he hA
  have hupp := mul_le_mul_of_nonneg_right ht hS
  change (d + ε) * (n.choose 2 : ℝ) * (n - 2).choose (m - 2) ≤ _ at hlow
  change _ ≤ (d + ε / 2) * (m.choose 2 : ℝ) * n.choose m at hupp
  change (G.edgeFinset.card : ℝ) * (n - 2).choose (m - 2) ≤
    (turanNumber m (r - 1) : ℝ) * n.choose m +
      (m.choose 2 : ℝ) * (G.cliqueFinset r).card * (n - r).choose (m - r) at hsample
  have hmain : (d + ε) * ((n.choose m : ℝ) * m.choose 2) ≤
      (d + ε / 2) * (m.choose 2 : ℝ) * n.choose m +
        (m.choose 2 : ℝ) * (G.cliqueFinset r).card * (n - r).choose (m - r) := by
    rw [hchoose]
    nlinarith only [hlow, hupp, hsample]
  have hpay : (ε / 2) * (n.choose m : ℝ) ≤
      (G.cliqueFinset r).card * (n - r).choose (m - r) := by
    apply (mul_le_mul_iff_right₀ hC).mp
    nlinarith only [hmain]
  have hpayR := mul_le_mul_of_nonneg_right hpay
    (show (0 : ℝ) ≤ m.choose r by positivity)
  apply (mul_le_mul_iff_left₀ hD).mp
  calc
    (ε / 2) * (n.choose r : ℝ) * (n - r).choose (m - r) =
        (ε / 2) * ((n.choose m : ℝ) * m.choose r) := by rw [hchooseR]; ring
    _ ≤ (m.choose r : ℝ) * (G.cliqueFinset r).card * (n - r).choose (m - r) := by
      nlinarith only [hpayR]

/-- A convenient uniform lower bound for binomial coefficients once `n ≥ 2r`. -/
lemma pow_le_factor_mul_choose (r n : ℕ) (hn : 2 * r ≤ n) :
    (n : ℝ) ^ r ≤ (2 : ℝ) ^ r * (r.factorial : ℝ) * (n.choose r : ℝ) := by
  have hnat : n ≤ 2 * (n + 1 - r) := by omega
  have hhalf : (n : ℝ) / 2 ≤ (n + 1 - r : ℕ) := by
    have h : (n : ℝ) ≤ 2 * (n + 1 - r : ℕ) := by exact_mod_cast hnat
    linarith
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) / 2) hhalf r
  rw [div_pow] at hpow
  have hpow' := (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ r)).mp hpow
  have hchoose : (n + 1 - r : ℕ) ^ r ≤ (n.choose r : ℝ) * (r.factorial : ℝ) :=
    (div_le_iff₀ (by exact_mod_cast Nat.factorial_pos r)).mp (Nat.pow_le_choose r n)
  have hmul := mul_le_mul_of_nonneg_right hchoose
    (show (0 : ℝ) ≤ (2 : ℝ) ^ r by positivity)
  nlinarith only [hpow', hmul]

/-- The fixed-sample clique supersaturation conclusion of W03, before tuple extraction. -/
theorem clique_supersaturation : CliqueDensitySpecs.supersaturationStatement := by
  intro r hr ε hε
  obtain ⟨m, hrm, ht⟩ := exists_clique_sample_size r hr ε hε
  let L : ℝ := (2 : ℝ) ^ r * (r.factorial : ℝ)
  let M : ℝ := m.choose r
  have hL : 0 < L := by dsimp [L]; positivity
  have hM : 0 < M := by
    dsimp [M]
    exact_mod_cast Nat.choose_pos hrm
  let c : ℝ := (ε / 2) / (M * L)
  refine ⟨c, by dsimp [c]; positivity, max m (2 * r), ?_⟩
  intro V _ _ G _ hn he
  have hmn : m ≤ Fintype.card V := (le_max_left _ _).trans hn
  have hnr : 2 * r ≤ Fintype.card V := (le_max_right _ _).trans hn
  have hcount := clique_count_from_sample G r m ε hr hrm hmn ht he
  have hbin := pow_le_factor_mul_choose r (Fintype.card V) hnr
  change (Fintype.card V : ℝ) ^ r ≤ L * ((Fintype.card V).choose r : ℝ) at hbin
  change (ε / 2) * ((Fintype.card V).choose r : ℝ) ≤ M * (G.cliqueFinset r).card at hcount
  have h1 := mul_le_mul_of_nonneg_left hbin (show (0 : ℝ) ≤ ε / 2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hcount (le_of_lt hL)
  dsimp [c]
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (mul_pos hM hL)).mpr
  nlinarith only [h1, h2]

end P205.Extremal
