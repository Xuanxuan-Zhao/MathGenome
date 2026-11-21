import MathGenome.Internal.ExtremalOptimization.Specs.P205.Extremal.TransversalDensity
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

universe u
open scoped BigOperators
open Finset
namespace P205.Extremal

/-- At least a `c/2` fraction of the possible prefixes have large neighborhoods. -/
lemma many_large_values {α : Type*} (A : Finset α) (f : α → ℝ)
    {m n c : ℝ} (hm : (A.card : ℝ) ≤ m) (hn : 0 < n) (hc : 0 ≤ c)
    (hf : ∀ a ∈ A, f a ≤ n) (hs : c * m * n ≤ ∑ a ∈ A, f a) :
    c * m / 2 ≤ ((A.filter fun a => c * n / 2 ≤ f a).card : ℝ) := by
  classical
  have hp : ∀ a ∈ A,
      f a ≤ (if c * n / 2 ≤ f a then n else 0) + c * n / 2 := by
    intro a ha
    split_ifs with h
    · linarith [hf a ha, mul_nonneg hc hn.le]
    · linarith
  have hsum := Finset.sum_le_sum hp
  simp only [Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_const_zero,
    add_zero, Finset.sum_const, nsmul_eq_mul] at hsum
  have hmul := mul_le_mul_of_nonneg_right hm (show 0 ≤ c * n / 2 by positivity)
  nlinarith

/-- Double counting pairs of a prefix and a `t`-subset of its neighborhood. -/
lemma count_common_subsets {α β : Type*} [DecidableEq β]
    (A : Finset α) (B : Finset β) (F : α → Finset β) (t : ℕ)
    (hF : ∀ a ∈ A, F a ⊆ B) :
    ∑ a ∈ A, ((F a).card.choose t : ℝ) =
      ∑ T ∈ B.powersetCard t, ((A.filter fun a => T ⊆ F a).card : ℝ) := by
  classical
  have h a (ha : a ∈ A) :
      (F a).powersetCard t = (B.powersetCard t).filter (fun T => T ⊆ F a) := by
    ext T
    simp only [mem_powersetCard, mem_filter]
    exact ⟨fun h => ⟨⟨h.1.trans (hF a ha), h.2⟩, h.1⟩,
      fun h => ⟨h.2, h.1.2⟩⟩
  calc
    _ = ∑ a ∈ A, (((F a).powersetCard t).card : ℝ) := by simp
    _ = ∑ a ∈ A, ∑ T ∈ B.powersetCard t, if T ⊆ F a then (1 : ℝ) else 0 := by
      apply sum_congr rfl
      intro a ha
      rw [h a ha]
      simp
    _ = _ := by
      rw [sum_comm]
      simp

/-- A real lower bound for the number of subsets in a large neighborhood. -/
lemma choose_lower_bound (d t : ℕ) {z : ℝ} (hz : 0 ≤ z)
    (ht : (t : ℝ) ≤ z) (hd : 2 * z ≤ (d : ℝ)) :
    z ^ t / (t.factorial : ℝ) ≤ (d.choose t : ℝ) := by
  have htd : t ≤ d + 1 := by exact_mod_cast (show (t : ℝ) ≤ d + 1 by linarith)
  have hsub : z ≤ ((d + 1 - t : ℕ) : ℝ) := by
    rw [Nat.cast_sub htd]
    push_cast
    linarith
  exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ hz hsub t)
    (Nat.cast_nonneg _)).trans (Nat.pow_le_choose t d)

/-- One last-part subset has a dense family of common prefixes. The intentionally
non-optimal positive constant suffices for induction. -/
lemma extract_common_subset {α β : Type*} [DecidableEq β]
    (A : Finset α) (B : Finset β) (F : α → Finset β) (t n : ℕ)
    {m c : ℝ} (hm0 : 0 < m) (hn0 : 0 < n) (hc : 0 < c)
    (hA : (A.card : ℝ) ≤ m) (hB : B.card ≤ n)
    (hF : ∀ a ∈ A, F a ⊆ B)
    (hs : c * m * n ≤ ∑ a ∈ A, ((F a).card : ℝ))
    (ht : (t : ℝ) ≤ c * n / 4) :
    ∃ T ∈ B.powersetCard t,
      (c / 2 * (c / 4) ^ t / (t.factorial : ℝ)) * m ≤
        ((A.filter fun a => T ⊆ F a).card : ℝ) := by
  classical
  let G := A.filter fun a => c * n / 2 ≤ ((F a).card : ℝ)
  let L : ℝ := (c * n / 4) ^ t / (t.factorial : ℝ)
  let d : ℝ := c / 2 * (c / 4) ^ t / (t.factorial : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hL : 0 < L := by dsimp [L]; positivity
  have hd : 0 < d := by dsimp [d]; positivity
  have hG : c * m / 2 ≤ (G.card : ℝ) :=
    many_large_values A (fun a => ((F a).card : ℝ)) hA hnR hc.le
      (fun a ha => by exact_mod_cast (card_le_card (hF a ha)).trans hB) hs
  have hlow : ∀ a ∈ G, L ≤ ((F a).card.choose t : ℝ) := by
    intro a ha
    have ha' := (mem_filter.mp ha).2
    exact choose_lower_bound (F a).card t (by positivity) ht (by linarith)
  have hcount := count_common_subsets G B F t
    (fun a ha => hF a (mem_filter.mp ha).1)
  have hpair : d * m * (n : ℝ) ^ t ≤
      ∑ T ∈ B.powersetCard t, ((G.filter fun a => T ⊆ F a).card : ℝ) := by
    calc
      _ = (c * m / 2) * L := by
        dsimp [d, L]
        rw [show c * (n : ℝ) / 4 = (c / 4) * n by ring, mul_pow]
        ring
      _ ≤ (G.card : ℝ) * L := mul_le_mul_of_nonneg_right hG hL.le
      _ = ∑ _a ∈ G, L := by simp
      _ ≤ ∑ a ∈ G, ((F a).card.choose t : ℝ) := sum_le_sum hlow
      _ = _ := hcount
  have hne : (B.powersetCard t).Nonempty := by
    by_contra he
    have he' : B.powersetCard t = ∅ := not_nonempty_iff_eq_empty.mp he
    rw [he', sum_empty] at hpair
    have : 0 < d * m * (n : ℝ) ^ t := by positivity
    linarith
  have hupper : ((B.powersetCard t).card : ℝ) ≤ (n : ℝ) ^ t := by
    rw [card_powersetCard]
    exact_mod_cast (Nat.choose_le_pow B.card t).trans (Nat.pow_le_pow_left hB t)
  have havg : ∑ _T ∈ B.powersetCard t, d * m ≤
      ∑ T ∈ B.powersetCard t, ((G.filter fun a => T ⊆ F a).card : ℝ) := by
    simp only [sum_const, nsmul_eq_mul]
    calc
      _ ≤ (n : ℝ) ^ t * (d * m) := mul_le_mul_of_nonneg_right hupper (by positivity)
      _ = d * m * (n : ℝ) ^ t := by ring
      _ ≤ _ := hpair
  obtain ⟨T, hT, hcommon⟩ := Finset.exists_le_of_sum_le hne havg
  refine ⟨T, hT, hcommon.trans ?_⟩
  exact_mod_cast card_le_card (show (G.filter fun a => T ⊆ F a) ⊆
    (A.filter fun a => T ⊆ F a) from
      fun a ha => mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp ha).1).1,
        (mem_filter.mp ha).2⟩)

/-- Decomposing the tuple relation by its tail counts exactly all its tuples. -/
lemma sum_neighborhood_card {α : Type*} [DecidableEq α] {r : ℕ}
    (V : Fin (r + 1) → Finset α) (E : Finset (Fin (r + 1) → α))
    (hE : ∀ x ∈ E, ∀ i, x i ∈ V i) :
    ∑ u ∈ Fintype.piFinset (fun i : Fin r => V i.succ),
      (((V 0).filter fun a => Fin.cons a u ∈ E).card : ℝ) = (E.card : ℝ) := by
  classical
  have hmap : ∀ x ∈ E,
      Fin.tail x ∈ Fintype.piFinset (fun i : Fin r => V i.succ) := by
    intro x hx
    exact Fintype.mem_piFinset.mpr (fun i => hE x hx i.succ)
  have hfiber (u : Fin r → α) :
      ((V 0).filter fun a => Fin.cons a u ∈ E).card =
        (E.filter fun x => Fin.tail x = u).card := by
    apply Finset.card_bij (fun (a : α) _ => (Fin.cons a u : Fin (r + 1) → α))
    · intro a ha
      exact mem_filter.mpr ⟨(mem_filter.mp ha).2, by simp⟩
    · intro a ha b hb hab
      exact congrFun hab 0
    · intro x hx
      have hxE := (mem_filter.mp hx).1
      have hxt := (mem_filter.mp hx).2
      refine ⟨x 0, mem_filter.mpr ⟨hE x hxE 0, ?_⟩, ?_⟩
      · simpa only [← hxt, Fin.cons_self_tail] using hxE
      · simpa only [← hxt] using Fin.cons_self_tail x
  have hcard : E.card = ∑ u ∈ Fintype.piFinset (fun i : Fin r => V i.succ),
      ((V 0).filter fun a => Fin.cons a u ∈ E).card := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    exact sum_congr rfl (fun u _ => (hfiber u).symm)
  exact_mod_cast hcard.symm

/-- A slightly stronger induction statement also allows zero parts and `t = 0`. -/
lemma transversal_density_all (r t : ℕ) :
    ∀ c : ℝ, 0 < c → c ≤ 1 →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (α : Type u) [DecidableEq α]
        (V : Fin r → Finset α) (E : Finset (Fin r → α)),
        (∀ i, (V i).card ≤ n) →
        (∀ x ∈ E, ∀ i, x i ∈ V i) →
        c * (n : ℝ) ^ r ≤ (E.card : ℝ) →
        ∃ T : Fin r → Finset α,
          (∀ i, T i ⊆ V i ∧ (T i).card = t) ∧
          ∀ x : Fin r → α, (∀ i, x i ∈ T i) → x ∈ E := by
  classical
  induction r with
  | zero =>
    intro c hc hc1
    refine ⟨1, ?_⟩
    intro n hn α inst V E hV hE hdens
    have hpos : 0 < E.card := by
      have hcardlower : c ≤ (E.card : ℝ) := by simpa using hdens
      have : (0 : ℝ) < E.card := hc.trans_le hcardlower
      exact_mod_cast this
    obtain ⟨x, hx⟩ := card_pos.mp hpos
    refine ⟨fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    intro y hy
    have hxy : x = y := Subsingleton.elim _ _
    simpa only [← hxy] using hx
  | succ r ih =>
    intro c hc hc1
    let d : ℝ := c / 2 * (c / 4) ^ t / (t.factorial : ℝ)
    have hd0 : 0 < d := by dsimp [d]; positivity
    have hd1 : d ≤ 1 := by
      have hpow : (c / 4) ^ t ≤ (1 : ℝ) :=
        pow_le_one₀ (by positivity) (by linarith)
      have hfact : (1 : ℝ) ≤ t.factorial := by exact_mod_cast t.factorial_pos
      have hmul : c / 2 * (c / 4) ^ t ≤ 1 := by
        calc
          _ ≤ c / 2 * 1 := mul_le_mul_of_nonneg_left hpow (by positivity)
          _ ≤ 1 := by linarith
      exact (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    obtain ⟨N, hN⟩ := ih d hd0 hd1
    obtain ⟨M, hM⟩ := exists_nat_ge (4 * (t : ℝ) / c)
    refine ⟨max N (max M 1), ?_⟩
    intro n hn α inst V E hV hE hdens
    have hnN : N ≤ n := (le_max_left _ _).trans hn
    have hnM : M ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    have hn1 : 1 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    have hn0 : 0 < n := by omega
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have htlarge : (t : ℝ) ≤ c * n / 4 := by
      have hnM' : (M : ℝ) ≤ n := by exact_mod_cast hnM
      have : 4 * (t : ℝ) / c ≤ n := hM.trans hnM'
      have := (div_le_iff₀ hc).mp this
      nlinarith
    let W : Fin r → Finset α := fun i => V i.succ
    let A := Fintype.piFinset W
    let F : (Fin r → α) → Finset α := fun u => (V 0).filter fun a => Fin.cons a u ∈ E
    have hA : (A.card : ℝ) ≤ (n : ℝ) ^ r := by
      have hAn : A.card ≤ n ^ r := by
        dsimp [A]
        rw [Fintype.card_piFinset]
        calc
          _ ≤ ∏ _i : Fin r, n := Finset.prod_le_prod (fun i _ => hV i.succ)
          _ = n ^ r := by simp
      exact_mod_cast hAn
    have hsum : c * (n : ℝ) ^ r * n ≤ ∑ u ∈ A, ((F u).card : ℝ) := by
      have hcount := sum_neighborhood_card V E hE
      change c * (n : ℝ) ^ r * n ≤ ∑ u ∈ Fintype.piFinset W,
        (((V 0).filter fun a => Fin.cons a u ∈ E).card : ℝ)
      rw [hcount]
      simpa only [pow_succ, mul_assoc] using hdens
    obtain ⟨S, hS, hcommon⟩ := extract_common_subset A (V 0) F t n
      (by positivity : 0 < (n : ℝ) ^ r) hn0 hc hA (hV 0)
      (fun _ _ => filter_subset _ _) hsum htlarge
    let E' := A.filter fun u => S ⊆ F u
    obtain ⟨T, hT, hprod⟩ := hN n hnN α W E'
      (fun i => hV i.succ)
      (fun u hu => Fintype.mem_piFinset.mp (mem_filter.mp hu).1)
      hcommon
    refine ⟨Fin.cons S T, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact mem_powersetCard.mp hS
      · exact hT j
    · intro x hx
      have htail : Fin.tail x ∈ E' := hprod (Fin.tail x) (fun i => hx i.succ)
      have hsub : S ⊆ F (Fin.tail x) := (mem_filter.mp htail).2
      have hx0 : x 0 ∈ S := hx 0
      have hxF := (mem_filter.mp (hsub hx0)).2
      simpa only [Fin.cons_self_tail] using hxF

/-- Lemma 1.3: dense families of transversal tuples contain a complete product. -/
theorem transversal_density : Specs.P205.Extremal.TransversalDensityStatement.{u} := by
  intro r t hr ht c hc hc1
  exact transversal_density_all r t c hc hc1

end P205.Extremal
