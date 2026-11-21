import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.TutteDefinition
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.TutteProductEvaluation
import Mathlib.Data.Finset.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

namespace FiniteCombinatorics.Matroid
open Set
open scoped Classical
universe u v
variable {α : Type u} {β : Type v}

/-- Both subset exponents vanish exactly for bases, including in rank zero. -/
theorem exponentsZeroIffBase (M : _root_.Matroid α) [M.Finite]
    (A : Set α) (hA : A ⊆ M.E) :
    rankDeficit M A = 0 ∧ rankNullity M A = 0 ↔ M.IsBase A := by
  have hd := rankDeficitCast M A hA
  have hn := rankNullityCast M A hA
  constructor
  · rintro ⟨hx, hy⟩
    have hr : rank M A = rank M M.E := by rw [hx] at hd; norm_num at hd; omega
    have hi : M.Indep A := (rankRecovery M A).mp ⟨hA, by
      rw [hy] at hn; norm_num at hn; omega⟩
    apply hi.isBase_of_eRk_ge hi.finite
    rw [← M.eRk_ground, ← finiteRankBridge M A, ← finiteRankBridge M M.E]
    have he : (M.eRk M.E).toNat = (M.eRk A).toNat := by
      unfold rank at hr
      exact_mod_cast hr.symm
    exact_mod_cast he.le
  · intro hB
    have hi := (rankRecovery M A).mpr hB.indep
    have hr := basisCardinality M A M.E hB.isBasis_ground
    constructor
    · apply Int.natCast_inj.mp
      rw [hd, ← hr, hi.2, sub_self, Nat.cast_zero]
    · apply Int.natCast_inj.mp
      rw [hn, hi.2, sub_self, Nat.cast_zero]

/-- Evaluation handles zero exponents with the usual convention `0^0 = 1`. -/
theorem tutteOneOne (M : _root_.Matroid α) [M.Finite] :
    tutteEvaluate M 1 1 =
      ((M.ground_finite.toFinset.powerset.filter
        (fun (A : Finset α) => M.IsBase (A : Set α))).card : ℤ) := by
  classical
  rw [tutteEvaluate, tutteSubstituteSum]
  simp only [sub_self]
  calc
    _ = ∑ A ∈ M.ground_finite.toFinset.powerset,
        (if M.IsBase (A : Set α) then (1 : ℤ) else 0) := by
      apply Finset.sum_congr rfl
      intro A hA
      have ha : (A : Set α) ⊆ M.E := by
        simpa using (Finset.mem_powerset.mp hA)
      have hh := exponentsZeroIffBase M (A : Set α) ha
      by_cases hx : rankDeficit M (A : Set α) = 0 <;>
        by_cases hy : rankNullity M (A : Set α) = 0 <;>
        simp_all
    _ = _ := by simp

private theorem groundFinsetSum (M : _root_.Matroid α) (N : _root_.Matroid β)
    [M.Finite] [N.Finite] :
    (directSum M N).ground_finite.toFinset =
      M.ground_finite.toFinset.disjSum N.ground_finite.toFinset := by
  ext x
  cases x <;> simp [directSumGround]

@[simp] private theorem preimageInlDisjSum (s : Finset α) (t : Finset β) :
    Sum.inl ⁻¹' (s.disjSum t : Set (α ⊕ β)) = (s : Set α) := by
  ext x
  simp

@[simp] private theorem preimageInrDisjSum (s : Finset α) (t : Finset β) :
    Sum.inr ⁻¹' (s.disjSum t : Set (α ⊕ β)) = (t : Set β) := by
  ext x
  simp

/-- The two exponents add on a disjoint union. The casts prevent truncated
subtraction from losing information. -/
theorem exponentsDirectSum (M : _root_.Matroid α) (N : _root_.Matroid β)
    [M.Finite] [N.Finite] (s : Finset α) (t : Finset β)
    (hs : (s : Set α) ⊆ M.E) (ht : (t : Set β) ⊆ N.E) :
    rankDeficit (directSum M N) (s.disjSum t : Set (α ⊕ β)) =
      rankDeficit M (s : Set α) + rankDeficit N (t : Set β) ∧
    rankNullity (directSum M N) (s.disjSum t : Set (α ⊕ β)) =
      rankNullity M (s : Set α) + rankNullity N (t : Set β) := by
  have hst : (s.disjSum t : Set (α ⊕ β)) ⊆ (directSum M N).E := by
    intro x hx
    cases x with
    | inl a =>
      have ha : a ∈ s := by simpa using hx
      rw [directSumGround]
      exact Or.inl ⟨a, hs ha, rfl⟩
    | inr b =>
      have hb : b ∈ t := by simpa using hx
      rw [directSumGround]
      exact Or.inr ⟨b, ht hb, rfl⟩
  have hr := directSumRank M N (s.disjSum t : Set (α ⊕ β)) hst
  simp only [preimageInlDisjSum, preimageInrDisjSum] at hr
  have he : rank (directSum M N) (directSum M N).E =
      rank M M.E + rank N N.E := by
    simpa [directSumGround, Set.preimage_image_eq _ Sum.inl_injective,
      Set.preimage_image_eq _ Sum.inr_injective] using
      directSumRank M N (directSum M N).E Subset.rfl
  constructor
  · apply Int.natCast_inj.mp
    rw [rankDeficitCast _ _ hst, Nat.cast_add,
      rankDeficitCast _ _ hs, rankDeficitCast _ _ ht, hr, he]
    ring
  · apply Int.natCast_inj.mp
    rw [rankNullityCast _ _ hst, Nat.cast_add,
      rankNullityCast _ _ hs, rankNullityCast _ _ ht, hr]
    simp only [Set.ncard_coe_finset, Finset.card_disjSum, Nat.cast_add]
    ring

/-- W77: splitting subsets into their left and right components factors the sum. -/
theorem tutteDirectSum (M : _root_.Matroid α) (N : _root_.Matroid β)
    [M.Finite] [N.Finite] :
    tutte (directSum M N) = tutte M * tutte N := by
  classical
  symm
  unfold tutte
  rw [Finset.sum_mul_sum]
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => p.1.disjSum p.2) ?_ ?_ ?_ ?_
  · intro p hp
    rw [groundFinsetSum, Finset.mem_powerset]
    exact Finset.disjSum_mono
      (Finset.mem_powerset.mp (Finset.mem_product.mp hp).1)
      (Finset.mem_powerset.mp (Finset.mem_product.mp hp).2)
  · intro p hp q hq he
    exact Prod.ext (Finset.disjSum_inj.mp he).1 (Finset.disjSum_inj.mp he).2
  · intro A hA
    rw [groundFinsetSum, Finset.mem_powerset, Finset.subset_disjSum] at hA
    exact ⟨(A.toLeft, A.toRight),
      Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hA.1,
        Finset.mem_powerset.mpr hA.2⟩, Finset.toLeft_disjSum_toRight⟩
  · intro p hp
    have hs : (p.1 : Set α) ⊆ M.E := by
      simpa using Finset.mem_powerset.mp (Finset.mem_product.mp hp).1
    have ht : (p.2 : Set β) ⊆ N.E := by
      simpa using Finset.mem_powerset.mp (Finset.mem_product.mp hp).2
    obtain ⟨hd, hn⟩ := exponentsDirectSum M N p.1 p.2 hs ht
    rw [hd, hn, pow_add, pow_add]
    ring

end FiniteCombinatorics.Matroid
