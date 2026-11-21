import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.TutteDefinition
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.MinorRank
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Cocircuits
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.TutteRecurrence
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

namespace FiniteCombinatorics.Matroid
open Set
open scoped _root_.Matroid
universe u
variable {α : Type u}

private noncomputable def term (M : _root_.Matroid α) [M.Finite]
    (A : Set α) : TuttePolynomial :=
  (MvPolynomial.X 0 - 1) ^ rankDeficit M A *
    (MvPolynomial.X 1 - 1) ^ rankNullity M A

/-- Partition the subsets according to whether they contain the chosen element. -/
private theorem tutte_pairs (M : _root_.Matroid α) [M.Finite] (e : α) (he : e ∈ M.E) :
    tutte M = ∑ A ∈ (M.ground_finite.sdiff (t := {e})).toFinset.powerset,
      (term M (A : Set α) + term M (insert e (A : Set α))) := by
  classical
  have hins : M.ground_finite.toFinset =
      insert e (M.ground_finite.sdiff (t := {e})).toFinset := by
    ext x
    simp only [Finite.mem_toFinset, Finset.mem_insert, mem_sdiff, mem_singleton_iff]
    constructor
    · intro hx
      by_cases h : x = e
      · exact Or.inl h
      · exact Or.inr ⟨hx, h⟩
    · rintro (rfl | ⟨hx, _⟩)
      · exact he
      · exact hx
  have hnot : e ∉ (M.ground_finite.sdiff (t := {e})).toFinset := by simp
  change (∑ A ∈ M.ground_finite.toFinset.powerset, term M (A : Set α)) = _
  rw [hins, Finset.sum_powerset_insert hnot, ← Finset.sum_add_distrib]
  simp only [Finset.coe_insert]

private theorem tutte_sum_ground (M : _root_.Matroid α) [M.Finite]
    (E : Set α) (hE : M.E = E) (hfin : E.Finite) :
    tutte M = ∑ A ∈ hfin.toFinset.powerset, term M (A : Set α) := by
  classical
  have h : M.ground_finite.toFinset = hfin.toFinset := by ext; simp [hE]
  change (∑ A ∈ M.ground_finite.toFinset.powerset, term M (A : Set α)) = _
  rw [h]

private theorem rank_insert_loop (M : _root_.Matroid α) [M.Finite]
    (e : α) (h : M.IsLoop e) (A : Set α) :
    rank M (insert e A) = rank M A := by
  have hc := M.closure_insert_eq_of_mem_closure (h.mem_closure A)
  have hr : M.eRk (insert e A) = M.eRk A := by
    rw [← M.eRk_closure_eq (insert e A), hc, M.eRk_closure_eq]
  simp only [rank, hr]

private theorem rank_insert_not_closure (M : _root_.Matroid α) [M.Finite]
    (e : α) (he : e ∈ M.E) (A : Set α) (ha : e ∉ M.closure A) :
    rank M (insert e A) = rank M A + 1 := by
  have h := M.eRk_insert_eq_add_one ⟨he, ha⟩
  unfold rank
  rw [h, ENat.toNat_add (M.isRkFinite_set A).eRk_lt_top.ne (by simp)]
  simp

private theorem rank_insert_coloop (M : _root_.Matroid α) [M.Finite]
    (e : α) (h : M.IsColoop e) (A : Set α) (ha : e ∉ A) :
    rank M (insert e A) = rank M A + 1 :=
  rank_insert_not_closure M e h.mem_ground A (h.notMem_closure_of_notMem ha)

private theorem insert_compl_singleton (M : _root_.Matroid α) (e : α) (he : e ∈ M.E) :
    insert e (M.E \ {e}) = M.E := by
  ext x
  simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff]
  constructor
  · rintro (rfl | ⟨hx, _⟩)
    · exact he
    · exact hx
  · intro hx
    by_cases h : x = e
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩

private theorem subset_retained {M : _root_.Matroid α} [M.Finite] {e : α}
    {A : Finset α} (hA : A ∈ (M.ground_finite.sdiff (t := {e})).toFinset.powerset) :
    (A : Set α) ⊆ M.E \ {e} := by
  classical
  intro x hx
  simpa only [Finite.mem_toFinset] using (Finset.mem_powerset.mp hA hx)

/-- Transfer an integer rank/cardinality calculation to the natural exponents.
The shifts are nonnegative; the upstream cast bridges justify every subtraction. -/
private theorem term_shift (M N : _root_.Matroid α) [M.Finite] [N.Finite]
    (A B : Set α) (hA : A ⊆ M.E) (hB : B ⊆ N.E) (dx dy : ℕ)
    (hd : rank M M.E - rank M A = rank N N.E - rank N B + (dx : ℤ))
    (hn : (A.ncard : ℤ) - rank M A = (B.ncard : ℤ) - rank N B + (dy : ℤ)) :
    term M A = (MvPolynomial.X 0 - 1) ^ dx *
      (MvPolynomial.X 1 - 1) ^ dy * term N B := by
  have hdM := rankDeficitCast M A hA
  have hdN := rankDeficitCast N B hB
  have hnM := rankNullityCast M A hA
  have hnN := rankNullityCast N B hB
  have hd' : rankDeficit M A = rankDeficit N B + dx := by omega
  have hn' : rankNullity M A = rankNullity N B + dy := by omega
  simp only [term, hd', hn', pow_add]
  ring

private theorem term_eq (M N : _root_.Matroid α) [M.Finite] [N.Finite]
    (A B : Set α) (hA : A ⊆ M.E) (hB : B ⊆ N.E)
    (hd : rank M M.E - rank M A = rank N N.E - rank N B)
    (hn : (A.ncard : ℤ) - rank M A = (B.ncard : ℤ) - rank N B) :
    term M A = term N B := by
  simpa using term_shift M N A B hA hB 0 0 (by simpa using hd) (by simpa using hn)

private theorem rank_delete_singleton (M : _root_.Matroid α) [M.Finite]
    (e : α) (he : e ∈ M.E) (A : Set α) (hA : A ⊆ M.E \ {e}) :
    rank (M ＼ {e}) A = rank M A :=
  deletionRank M {e} A (singleton_subset_iff.mpr he) hA

private theorem rank_contract_singleton (M : _root_.Matroid α) [M.Finite]
    (e : α) (he : e ∈ M.E) (A : Set α) (hA : A ⊆ M.E \ {e}) :
    rank (M ／ {e}) A = rank M (insert e A) - rank M {e} := by
  simpa only [union_singleton] using
    contractionRank M {e} A (singleton_subset_iff.mpr he) hA

private theorem retained_card_insert (M : _root_.Matroid α) [M.Finite]
    (e : α) (A : Set α) (hA : A ⊆ M.E \ {e}) :
    ((insert e A).ncard : ℤ) = (A.ncard : ℤ) + 1 := by
  have hn : e ∉ A := fun heA => (hA heA).2 (mem_singleton e)
  rw [ncard_insert_of_notMem hn (M.ground_finite.subset (hA.trans sdiff_subset)),
    Nat.cast_add, Nat.cast_one]

private theorem loop_pair (M : _root_.Matroid α) [M.Finite]
    (e : α) (he : e ∈ M.E) (hl : M.IsLoop e) (A : Set α)
    (hA : A ⊆ M.E \ {e}) :
    term M A + term M (insert e A) = MvPolynomial.X 1 * term (M ＼ {e}) A := by
  have hAE := hA.trans sdiff_subset
  have hAi := insert_subset he hAE
  have hAD : A ⊆ (M ＼ {e}).E := hA
  have hdel := rank_delete_singleton M e he A hA
  have hloop := rank_insert_loop M e hl A
  have htotal : rank (M ＼ {e}) (M ＼ {e}).E = rank M M.E := by
    change rank (M ＼ {e}) (M.E \ {e}) = _
    rw [rank_delete_singleton M e he _ Subset.rfl]
    have h := rank_insert_loop M e hl (M.E \ {e})
    rw [insert_compl_singleton M e he] at h
    exact h.symm
  have hcard := retained_card_insert M e A hA
  have habs : term M A = term (M ＼ {e}) A :=
    term_eq M (M ＼ {e}) A A hAE hAD (by linarith) (by linarith)
  have hpres : term M (insert e A) =
      (MvPolynomial.X 1 - 1) * term (M ＼ {e}) A := by
    simpa using term_shift M (M ＼ {e}) (insert e A) A hAi hAD 0 1
      (by push_cast; linarith) (by push_cast; linarith)
  rw [habs, hpres]
  ring

/-- W77, loop branch, including a one-element loop and its empty deletion. -/
theorem tutteLoop (M : _root_.Matroid α) [M.Finite] (e : α)
    (he : e ∈ M.E) (hl : Loop M e) :
    tutte M = MvPolynomial.X 1 * tutte (M ＼ {e}) := by
  classical
  rw [tutte_pairs M e he,
    tutte_sum_ground (M ＼ {e}) (M.E \ {e}) rfl M.ground_finite.sdiff,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  exact loop_pair M e he ((loopIffIsLoop M e).mp hl) A (subset_retained hA)

private theorem coloop_pair (M : _root_.Matroid α) [M.Finite]
    (e : α) (he : e ∈ M.E) (hc : M.IsColoop e) (A : Set α)
    (hA : A ⊆ M.E \ {e}) :
    term M A + term M (insert e A) = MvPolynomial.X 0 * term (M ／ {e}) A := by
  have hAE := hA.trans sdiff_subset
  have hAi := insert_subset he hAE
  have hAC : A ⊆ (M ／ {e}).E := hA
  have hnot : e ∉ A := fun ha => (hA ha).2 (mem_singleton e)
  have hinc := rank_insert_coloop M e hc A hnot
  have hsingle : rank M {e} = 1 := by
    simpa only [insert_empty_eq, rankEmpty, zero_add] using
      rank_insert_coloop M e hc ∅ (notMem_empty e)
  have hcon := rank_contract_singleton M e he A hA
  have htotal : rank (M ／ {e}) (M ／ {e}).E = rank M M.E - 1 := by
    change rank (M ／ {e}) (M.E \ {e}) = _
    rw [rank_contract_singleton M e he _ Subset.rfl, insert_compl_singleton M e he,
      hsingle]
  have hcard := retained_card_insert M e A hA
  have habs : term M A = (MvPolynomial.X 0 - 1) * term (M ／ {e}) A := by
    simpa using term_shift M (M ／ {e}) A A hAE hAC 1 0
      (by push_cast; linarith) (by push_cast; linarith)
  have hpres : term M (insert e A) = term (M ／ {e}) A :=
    term_eq M (M ／ {e}) (insert e A) A hAi hAC (by linarith) (by linarith)
  rw [habs, hpres]
  ring

/-- W77, coloop branch; the contraction ground is allowed to be empty. -/
theorem tutteColoop (M : _root_.Matroid α) [M.Finite] (e : α)
    (he : e ∈ M.E) (hc : Coloop M e) :
    tutte M = MvPolynomial.X 0 * tutte (M ／ {e}) := by
  classical
  rw [tutte_pairs M e he,
    tutte_sum_ground (M ／ {e}) (M.E \ {e}) rfl M.ground_finite.sdiff,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  exact coloop_pair M e he ((coloopIffIsColoop M e).mp hc) A (subset_retained hA)

private theorem regular_pair (M : _root_.Matroid α) [M.Finite]
    (e : α) (he : e ∈ M.E) (hl : ¬ M.IsLoop e) (hc : ¬ M.IsColoop e)
    (A : Set α) (hA : A ⊆ M.E \ {e}) :
    term M A + term M (insert e A) = term (M ＼ {e}) A + term (M ／ {e}) A := by
  classical
  have hAE := hA.trans sdiff_subset
  have hAi := insert_subset he hAE
  have hAD : A ⊆ (M ＼ {e}).E := hA
  have hAC : A ⊆ (M ／ {e}).E := hA
  have hcl : e ∈ M.closure (M.E \ {e}) := by
    by_contra h
    exact hc ((_root_.Matroid.isColoop_iff_notMem_closure_compl he).mpr h)
  have hfull := (closureRank M (M.E \ {e}) sdiff_subset e he).mp hcl
  rw [insert_compl_singleton M e he] at hfull
  have hdel := rank_delete_singleton M e he A hA
  have hdtotal : rank (M ＼ {e}) (M ＼ {e}).E = rank M M.E := by
    change rank (M ＼ {e}) (M.E \ {e}) = _
    rw [rank_delete_singleton M e he _ Subset.rfl]
    exact hfull.symm
  have hsingle : rank M {e} = 1 := by
    have h := (M.isNonloop_of_not_isLoop he hl).eRk_eq
    simp only [rank, h, ENat.toNat_one, Nat.cast_one]
  have hcon := rank_contract_singleton M e he A hA
  have hctotal : rank (M ／ {e}) (M ／ {e}).E = rank M M.E - 1 := by
    change rank (M ／ {e}) (M.E \ {e}) = _
    rw [rank_contract_singleton M e he _ Subset.rfl, insert_compl_singleton M e he,
      hsingle]
  have hcard := retained_card_insert M e A hA
  have habs : term M A = term (M ＼ {e}) A :=
    term_eq M (M ＼ {e}) A A hAE hAD (by linarith) (by linarith)
  have hpres : term M (insert e A) = term (M ／ {e}) A :=
    term_eq M (M ／ {e}) (insert e A) A hAi hAC (by linarith) (by linarith)
  rw [habs, hpres]

/-- W77, deletion–contraction for an element that is neither loop nor coloop. -/
theorem tutteDeletionContraction (M : _root_.Matroid α) [M.Finite] (e : α)
    (he : e ∈ M.E) (hl : ¬ Loop M e) (hc : ¬ Coloop M e) :
    tutte M = tutte (M ＼ {e}) + tutte (M ／ {e}) := by
  classical
  rw [tutte_pairs M e he,
    tutte_sum_ground (M ＼ {e}) (M.E \ {e}) rfl M.ground_finite.sdiff,
    tutte_sum_ground (M ／ {e}) (M.E \ {e}) rfl M.ground_finite.sdiff,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A hA
  exact regular_pair M e he (fun h => hl ((loopIffIsLoop M e).mpr h))
    (fun h => hc ((coloopIffIsColoop M e).mpr h)) A (subset_retained hA)

end FiniteCombinatorics.Matroid
