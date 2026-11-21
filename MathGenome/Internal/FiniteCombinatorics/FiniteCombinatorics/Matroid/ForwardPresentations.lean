import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.Foundation
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.ForwardPresentations
import Mathlib.Tactic.Linarith

/-! Forward presentations of finite matroids (W64–W66).
The ambient type is unrestricted; only the specified ground is finite.
The extended-rank library lemmas are transferred to the canonical integer rank,
so every subtraction below is in ℤ. -/
namespace FiniteCombinatorics.Matroid
open Set
universe u
variable {α : Type u}

theorem basisExtension :
  ∀ (M : _root_.Matroid α) [M.Finite] (I A : Set α),
    M.Indep I → I ⊆ A → A ⊆ M.E → ∃ B, M.IsBasis B A ∧ I ⊆ B := by
  intro M _ I A hI hIA hA
  exact hI.subset_isBasis_of_subset hIA hA

theorem basisCardinality :
  ∀ (M : _root_.Matroid α) [M.Finite] (B A : Set α),
    M.IsBasis B A → (B.ncard : ℤ) = rank M A := by
  intro M _ B A hB
  have h := congrArg ENat.toNat hB.encard_eq_eRk
  change B.ncard = (M.eRk A).toNat at h
  unfold rank
  exact_mod_cast h

theorem basesPresentation :
  ∀ (M : _root_.Matroid α) [M.Finite],
    BasisPresentation M.E {B | M.IsBase B} := by
  intro M _
  exact ⟨M.exists_isBase, fun _ hB => hB.subset_ground,
    fun _ hB _ hD _ he => hB.exchange hD he⟩

theorem rankEmpty :
  ∀ (M : _root_.Matroid α) [M.Finite], rank M ∅ = 0 := by
  intro M _
  simp [rank, M.eRk_empty]

theorem rankBounds :
  ∀ (M : _root_.Matroid α) [M.Finite] (A : Set α),
    A ⊆ M.E → 0 ≤ rank M A ∧ rank M A ≤ (A.ncard : ℤ) := by
  intro M _ A hA
  have h := M.eRk_le_encard A
  rw [← (M.ground_finite.subset hA).cast_ncard_eq] at h
  have hn := ENat.toNat_le_of_le_natCast h
  exact ⟨Int.natCast_nonneg _, by unfold rank; exact_mod_cast hn⟩

theorem rankMonotone :
  ∀ (M : _root_.Matroid α) [M.Finite] (A B : Set α),
    A ⊆ B → B ⊆ M.E → rank M A ≤ rank M B := by
  intro M _ A B hAB _
  have h := ENat.toNat_le_toNat (M.eRk_mono hAB) (M.isRkFinite_set B).eRk_lt_top.ne
  unfold rank
  exact_mod_cast h

theorem rankIncrements :
  ∀ (M : _root_.Matroid α) [M.Finite] (A : Set α),
    A ⊆ M.E → ∀ e ∈ M.E,
      0 ≤ rank M (insert e A) - rank M A ∧ rank M (insert e A) - rank M A ≤ 1 := by
  intro M _ A hA e he
  have hlo := rankMonotone M A (insert e A) (subset_insert _ _) (insert_subset he hA)
  have hn := ENat.toNat_le_toNat (M.eRk_insert_le_add_one e A)
    (by simp [(M.isRkFinite_set A).eRk_lt_top.ne])
  rw [ENat.toNat_add (M.isRkFinite_set A).eRk_lt_top.ne (by simp)] at hn
  have hhi : rank M (insert e A) ≤ rank M A + 1 := by
    simpa only [rank, ENat.toNat_one, Nat.cast_add, Nat.cast_one] using
      (Int.ofNat_le.mpr hn)
  constructor <;> linarith

theorem rankSubmodular :
  ∀ (M : _root_.Matroid α) [M.Finite] (A B : Set α),
    A ⊆ M.E → B ⊆ M.E →
      rank M (A ∪ B) + rank M (A ∩ B) ≤ rank M A + rank M B := by
  intro M _ A B _ _
  have h := ENat.toNat_le_toNat (M.eRk_inter_add_eRk_union_le A B)
    (by simp [(M.isRkFinite_set A).eRk_lt_top.ne, (M.isRkFinite_set B).eRk_lt_top.ne])
  rw [ENat.toNat_add (M.isRkFinite_set (A ∩ B)).eRk_lt_top.ne
    (M.isRkFinite_set (A ∪ B)).eRk_lt_top.ne,
    ENat.toNat_add (M.isRkFinite_set A).eRk_lt_top.ne
    (M.isRkFinite_set B).eRk_lt_top.ne] at h
  have hi : rank M (A ∩ B) + rank M (A ∪ B) ≤ rank M A + rank M B := by
    unfold rank
    exact_mod_cast h
  linarith

theorem rankDiminishing :
  ∀ (M : _root_.Matroid α) [M.Finite] (A B : Set α),
    A ⊆ B → B ⊆ M.E → ∀ e ∈ M.E,
      rank M (insert e B) - rank M B ≤ rank M (insert e A) - rank M A := by
  intro M _ A B hAB hB e he
  by_cases heB : e ∈ B
  · rw [insert_eq_of_mem heB]
    have h := (rankIncrements M A (hAB.trans hB) e he).1
    linarith
  have hu : insert e A ∪ B = insert e B := by
    ext x
    simp only [mem_union, mem_insert_iff]
    constructor
    · rintro ((rfl | hx) | hx)
      · exact Or.inl rfl
      · exact Or.inr (hAB hx)
      · exact Or.inr hx
    · rintro (rfl | hx)
      · exact Or.inl (Or.inl rfl)
      · exact Or.inr hx
  have hi : insert e A ∩ B = A := by
    ext x
    constructor
    · rintro ⟨rfl | hx, hxB⟩
      · exact (heB hxB).elim
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, hAB hx⟩
  have h := rankSubmodular M (insert e A) B (insert_subset he (hAB.trans hB)) hB
  rw [hu, hi] at h
  linarith

theorem rankNoIncrement :
  ∀ (M : _root_.Matroid α) [M.Finite] (A B : Set α),
    A ⊆ B → B ⊆ M.E → ∀ e ∈ M.E,
      rank M (insert e A) = rank M A → rank M (insert e B) = rank M B := by
  intro M _ A B hAB hB e he h
  have hd := rankDiminishing M A B hAB hB e he
  have hn := (rankIncrements M B hB e he).1
  linarith

theorem rankPresentation :
  ∀ (M : _root_.Matroid α) [M.Finite], RankPresentation M.E (rank M) := by
  intro M _
  exact ⟨rankEmpty M, rankIncrements M,
    fun A hA B hB => rankSubmodular M A B hA hB⟩

theorem circuitMinimal :
  ∀ (M : _root_.Matroid α) [M.Finite] (C : Set α),
    M.IsCircuit C ↔ C ⊆ M.E ∧ ¬ M.Indep C ∧
      ∀ D, D ⊂ C → M.Indep D := by
  intro M _ C
  rw [_root_.Matroid.isCircuit_iff_forall_ssubset]
  constructor
  · rintro ⟨hC, hmin⟩
    exact ⟨hC.subset_ground, hC.not_indep, fun D hD => hmin hD⟩
  · rintro ⟨hC, hdep, hmin⟩
    exact ⟨⟨hdep, hC⟩, fun {_} hD => hmin _ hD⟩

theorem circuitsPresentation :
  ∀ (M : _root_.Matroid α) [M.Finite],
    CircuitPresentation M.E {C | M.IsCircuit C} := by
  intro M _
  refine ⟨fun C hC => ⟨hC.subset_ground, hC.nonempty⟩,
    fun C hC D hD hCD => hC.eq_of_subset_isCircuit hD hCD, ?_⟩
  intro C hC D hD hne e _
  obtain ⟨K, hKsub, hK⟩ := hC.elimination hD hne e
  exact ⟨K, hK, hKsub⟩

theorem closurePresentation :
  ∀ (M : _root_.Matroid α) [M.Finite],
    ClosurePresentation M.E M.closure := by
  intro M _
  exact ⟨fun A _ => M.closure_subset_ground A,
    fun A hA => M.subset_closure A hA,
    fun _ _ _ _ hAB => M.closure_subset_closure hAB,
    fun A _ => M.closure_closure A,
    fun _ _ _ _ _ _ h => (M.closure_exchange h).1⟩

theorem closureRank :
  ∀ (M : _root_.Matroid α) [M.Finite] (A : Set α),
    A ⊆ M.E → ∀ e ∈ M.E,
      e ∈ M.closure A ↔ rank M (insert e A) = rank M A := by
  intro M _ A _ e he
  constructor
  · intro hc
    have hcl := M.closure_insert_eq_of_mem_closure hc
    have hr : M.eRk (insert e A) = M.eRk A := by
      rw [← M.eRk_closure_eq (insert e A), hcl, M.eRk_closure_eq]
    simp only [rank, hr]
  · intro hr
    have hn : (M.eRk (insert e A)).toNat = (M.eRk A).toNat := by
      unfold rank at hr
      exact_mod_cast hr
    have hr' : M.eRk (insert e A) = M.eRk A := by
      rw [← finiteRankBridge M (insert e A), ← finiteRankBridge M A, hn]
    have hcl := (M.isRkFinite_set A).closure_eq_closure_of_subset_of_eRk_ge_eRk
      (subset_insert e A) hr'.le
    rw [hcl]
    exact M.mem_closure_of_mem' (mem_insert e A) he

theorem basisRecovery :
  ∀ (M : _root_.Matroid α) [M.Finite] (I : Set α),
    BasisIndependent M.E {B | M.IsBase B} I ↔ M.Indep I := by
  intro M _ I
  constructor
  · rintro ⟨_, B, hB, hIB⟩
    exact hB.indep.subset hIB
  · intro hI
    exact ⟨hI.subset_ground, hI.exists_isBase_superset⟩

theorem rankRecovery :
  ∀ (M : _root_.Matroid α) [M.Finite] (I : Set α),
    RankIndependent M.E (rank M) I ↔ M.Indep I := by
  intro M _ I
  constructor
  · rintro ⟨hI, hr⟩
    apply (_root_.Matroid.indep_iff_eRk_eq_encard_of_finite (M.ground_finite.subset hI)).mpr
    have hn : (M.eRk I).toNat = I.ncard := by
      unfold rank at hr
      exact_mod_cast hr
    rw [← finiteRankBridge M I, hn, (M.ground_finite.subset hI).cast_ncard_eq]
  · intro hI
    refine ⟨hI.subset_ground, ?_⟩
    have h := congrArg ENat.toNat hI.eRk_eq_encard
    change (M.eRk I).toNat = I.ncard at h
    unfold rank
    exact_mod_cast h

theorem circuitRecovery :
  ∀ (M : _root_.Matroid α) [M.Finite] (I : Set α),
    CircuitIndependent M.E {C | M.IsCircuit C} I ↔ M.Indep I := by
  intro M _ I
  constructor
  · rintro ⟨hI, hc⟩
    apply (_root_.Matroid.indep_iff_forall_subset_not_isCircuit hI).mpr
    intro C hCI hC
    exact hc C hC hCI
  · intro hI
    refine ⟨hI.subset_ground, ?_⟩
    intro C hC hCI
    exact hC.not_indep (hI.subset hCI)

theorem closureRecovery :
  ∀ (M : _root_.Matroid α) [M.Finite] (I : Set α),
    ClosureIndependent M.E M.closure I ↔ M.Indep I := by
  intro M _ I
  exact _root_.Matroid.indep_iff_forall_notMem_closure_sdiff'.symm

end FiniteCombinatorics.Matroid
