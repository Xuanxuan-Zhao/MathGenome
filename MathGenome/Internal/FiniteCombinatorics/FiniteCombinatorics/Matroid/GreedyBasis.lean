import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.GreedyPrefix
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GreedyBasis
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic.Ring

/-! Maximum weight of the greedy basis, paper.tex W79.
The comparison uses nonnegative prefix surpluses and equal total cardinalities.
No assumption is made on the sign of the weights. -/
namespace FiniteCombinatorics.Matroid
open Set
open scoped Classical
universe u v
variable {α : Type u} {E : Set α}

/-- A finite summation-by-parts inequality, with an arbitrary signed lower weight.
The prefix sums of `d` must be nonnegative, but its individual values need not be. -/
theorem list_weighted_prefix_lower_bound {β : Type v} (l : List β)
    (w d : β → ℝ) (a : ℝ)
    (hs : l.Pairwise (fun x y => w y ≤ w x))
    (ha : ∀ x ∈ l, a ≤ w x)
    (hp : ∀ k ≤ l.length, 0 ≤ ((l.take k).map d).sum) :
    a * (l.map d).sum ≤ (l.map (fun x => w x * d x)).sum := by
  induction l using List.reverseRecOn generalizing a with
  | nil => simp
  | append_singleton l e ih =>
    have hs' := List.pairwise_append.mp hs
    have hp' : ∀ k ≤ l.length, 0 ≤ ((l.take k).map d).sum := by
      intro k hk
      have h := hp k (by simpa using hk.trans (Nat.le_succ l.length))
      simpa only [List.take_append_of_le_length hk] using h
    have hprev := ih (w e) hs'.1
      (fun x hx => hs'.2.2 x hx e (by simp)) hp'
    have htotal := hp (l ++ [e]).length le_rfl
    simp only [List.take_length, List.map_append, List.map_singleton,
      List.sum_append, List.sum_singleton] at htotal ⊢
    have hlast := ha e (by simp)
    nlinarith [mul_nonneg (sub_nonneg.mpr hlast) htotal]

private theorem list_sum_sub {β : Type v} (l : List β) (f g : β → ℝ) :
    (l.map (fun x => f x - g x)).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons e l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

/-- Indicators summed along a list without repetitions count its ambient subset. -/
private theorem list_indicator_sum (l : List E) (hn : l.Nodup) (B : Set α) :
    (l.map (fun (e : E) => if (e : α) ∈ B then (1 : ℝ) else 0)).sum =
      ({x | x ∈ B ∧ ∃ e ∈ l, (e : α) = x}.ncard : ℝ) := by
  classical
  let F := l.toFinset.filter (fun (e : E) => (e : α) ∈ B)
  have hset : {x | x ∈ B ∧ ∃ e ∈ l, (e : α) = x} =
      Subtype.val '' (F : Set E) := by
    ext x
    simp only [mem_ofPred_eq, mem_image, Finset.mem_coe, F,
      Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨hx, e, he, rfl⟩
      exact ⟨e, ⟨he, hx⟩, rfl⟩
    · rintro ⟨e, ⟨he, hx⟩, rfl⟩
      exact ⟨hx, e, he, rfl⟩
  rw [hset, ncard_image_of_injective _ Subtype.val_injective, ncard_coe_finset,
    ← List.sum_toFinset _ hn]
  simp [F, Finset.sum_ite]

private theorem enumeration_subsetWeight (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (B : Set α) :
    ((greedyEnumeration S w tie).map
      (fun (e : E) => if (e : α) ∈ B then w e else 0)).sum = subsetWeight S w B := by
  classical
  let := S.finite_ground.fintype
  have h : (greedyEnumeration S w tie).toFinset = Finset.univ := by
    ext e
    simp [greedyEnumeration_mem S w tie e]
  unfold subsetWeight
  rw [← List.sum_toFinset _ (greedyEnumeration_nodup S w tie), h]

private theorem enumeration_indicator_sum (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (B : Set α) (hB : B ⊆ E) :
    ((greedyEnumeration S w tie).map
      (fun (e : E) => if (e : α) ∈ B then (1 : ℝ) else 0)).sum = (B.ncard : ℝ) := by
  rw [list_indicator_sum _ (greedyEnumeration_nodup S w tie)]
  congr 1
  congr 1
  ext x
  constructor
  · exact And.left
  · intro hx
    exact ⟨hx, ⟨x, hB hx⟩, greedyEnumeration_mem S w tie _, rfl⟩

/-- Equal total sums remove the signed boundary term in summation by parts. -/
theorem list_weighted_prefix_nonneg {β : Type v} (l : List β) (w d : β → ℝ)
    (hs : l.Pairwise (fun x y => w y ≤ w x))
    (hp : ∀ k ≤ l.length, 0 ≤ ((l.take k).map d).sum)
    (ht : (l.map d).sum = 0) :
    0 ≤ (l.map (fun x => w x * d x)).sum := by
  cases l using List.reverseRecOn with
  | nil => simp
  | append_singleton l e =>
    have ha : ∀ x ∈ l ++ [e], w e ≤ w x := by
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact (List.pairwise_append.mp hs).2.2 x hx e (by simp)
      · have he : x = e := List.mem_singleton.mp hx
        rw [he]
    simpa only [ht, mul_zero] using
      list_weighted_prefix_lower_bound (l ++ [e]) w d (w e) hs ha hp

/-- With arbitrary real weights and any tie order, greedy returns a maximum-weight basis. -/
theorem greedyBasisOptimal (M : _root_.Matroid α) [M.Finite]
    (w : M.E → ℝ) (tie : LinearOrder M.E) :
    M.IsBase (greedyOutput (fromMatroid M) w tie) ∧
      ∀ B, M.IsBase B →
        subsetWeight (fromMatroid M) w B ≤
          subsetWeight (fromMatroid M) w (greedyOutput (fromMatroid M) w tie) := by
  classical
  let S := fromMatroid M
  let G := greedyOutput S w tie
  let l := greedyEnumeration S w tie
  have hG : M.IsBase G := greedyOutput_isBase M w tie
  refine ⟨hG, ?_⟩
  intro B hB
  let d : M.E → ℝ := fun e =>
    (if (e : α) ∈ G then 1 else 0) - (if (e : α) ∈ B then 1 else 0)
  have hprefix (k : ℕ) :
      (B ∩ greedyPrefix S w tie k).ncard ≤ (G ∩ greedyPrefix S w tie k).ncard := by
    have hP : greedyPrefix S w tie k ⊆ M.E := by
      rintro x ⟨e, _, rfl⟩
      exact e.property
    obtain ⟨C, hC, hBC⟩ := basisExtension M (B ∩ greedyPrefix S w tie k)
      (greedyPrefix S w tie k) (hB.indep.subset inter_subset_left)
      inter_subset_right hP
    have hcard : C.ncard = (greedyState S w tie k).ncard :=
      congrArg ENat.toNat (hC.encard_eq_encard (greedyPrefix_isBasis M w tie k))
    have hle := ncard_le_ncard hBC (M.ground_finite.subset hC.indep.subset_ground)
    rw [hcard, ← greedyOutput_inter_prefix S w tie k] at hle
    exact hle
  have hp : ∀ k ≤ l.length, 0 ≤ ((l.take k).map d).sum := by
    intro k _
    dsimp only [d]
    rw [list_sum_sub, list_indicator_sum _ ((greedyEnumeration_nodup S w tie).take),
      list_indicator_sum _ ((greedyEnumeration_nodup S w tie).take)]
    change 0 ≤ ((G ∩ greedyPrefix S w tie k).ncard : ℝ) -
      ((B ∩ greedyPrefix S w tie k).ncard : ℝ)
    exact sub_nonneg.mpr (Nat.cast_le.mpr (hprefix k))
  have ht : (l.map d).sum = 0 := by
    dsimp only [d, l]
    rw [list_sum_sub, enumeration_indicator_sum S w tie G hG.subset_ground,
      enumeration_indicator_sum S w tie B hB.subset_ground]
    have hc : G.ncard = B.ncard :=
      congrArg ENat.toNat (hG.encard_eq_encard_of_isBase hB)
    rw [hc, sub_self]
  have hs : l.Pairwise (fun x y => w y ≤ w x) :=
    (greedyEnumeration_pairwise S w tie).imp (by
      intro a b h
      rcases h with h | h
      · exact h.le
      · exact h.1.symm.le)
  have hnonneg := list_weighted_prefix_nonneg l w d hs hp ht
  have hw : (l.map (fun e => w e * d e)).sum =
      subsetWeight S w G - subsetWeight S w B := by
    have hf : (fun e => w e * d e) =
        (fun (e : M.E) => (if (e : α) ∈ G then w e else 0) -
          (if (e : α) ∈ B then w e else 0)) := by
      funext e
      dsimp only [d]
      split_ifs <;> ring
    rw [hf, list_sum_sub, enumeration_subsetWeight S w tie G,
      enumeration_subsetWeight S w tie B]
  rw [hw] at hnonneg
  exact sub_nonneg.mp hnonneg

end FiniteCombinatorics.Matroid
