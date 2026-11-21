import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.GreedyIndependent
import MathGenome.Internal.FiniteCombinatorics.Specs.FiniteCombinatorics.Matroid.GreedyCharacterization
import Mathlib.Order.Preorder.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset
import Batteries.Tactic.OpenPrivate
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Greedy optimality characterizes augmentation (W80). -/
namespace FiniteCombinatorics.Matroid
open Set
open scoped Classical
universe u
variable {α : Type u} {E : Set α}

open private greedyFold_extensive from MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.GreedyPrefix
open private enumeration_subsetWeight enumeration_indicator_sum from
  MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Matroid.GreedyBasis

theorem nonnegative_maximal_extension (S : IndependenceSystem E) (w : E → ℝ)
    (hw : ∀ e, 0 ≤ w e) (I : Set α) (hI : S.Indep I) :
    ∃ B, MaximalIndependent S B ∧ I ⊆ B ∧
      subsetWeight S w I ≤ subsetWeight S w B := by
  have hf : {B | S.Indep B ∧ I ⊆ B}.Finite :=
    S.finite_ground.finite_subsets.subset (fun _ h => S.subset_ground h.1)
  obtain ⟨B, ⟨hB, hIB⟩, hmax⟩ := hf.exists_maximal ⟨I, hI, Subset.rfl⟩
  refine ⟨B, ⟨S.subset_ground hB, hB, ?_⟩, hIB, subsetWeight_mono S w hw hIB⟩
  intro J _ hJ hBJ
  exact (hmax ⟨hJ, hIB.trans hBJ⟩ hBJ).antisymm hBJ

theorem greedy_objectives_iff (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (hw : ∀ e, 0 ≤ w e) :
    BasisOptimal S w (greedyOutput S w tie) ↔
      IndependentOptimal S w (greedyOutput S w tie) := by
  constructor
  · rintro ⟨hG, hbest⟩
    refine ⟨hG.2.1, ?_⟩
    intro I hI
    obtain ⟨B, hB, _, hle⟩ := nonnegative_maximal_extension S w hw I hI
    exact hle.trans (hbest B hB)
  · rintro ⟨_, hbest⟩
    exact ⟨greedyOutput_maximal S w tie, fun B hB => hbest B hB.2.1⟩

/-- A strictly higher weighted independent set is selected completely, regardless
of the tie order. The auxiliary state K already consists of elements of I. -/
private theorem greedyFold_contains_priority (S : IndependenceSystem E) (w : E → ℝ)
    (I : Set α) (hI : S.Indep I)
    (hpriority : ∀ a b : E, (a : α) ∈ I → (b : α) ∉ I → w b < w a)
    (l : List E) (hs : l.Pairwise (fun a b => w b ≤ w a))
    (K : Set α) (hK : K ⊆ I)
    (hcover : ∀ x ∈ I, x ∈ K ∨ ∃ e ∈ l, (e : α) = x) :
    I ⊆ l.foldl (greedyStep S) K := by
  classical
  induction l generalizing K with
  | nil =>
    intro x hx
    rcases hcover x hx with hx | ⟨e, he, _⟩
    · exact hx
    · simp at he
  | cons e l ih =>
    obtain ⟨heorder, hlorder⟩ := List.pairwise_cons.mp hs
    by_cases he : (e : α) ∈ I
    · have hstep := greedyStep_accept S K e (S.hereditary hI (insert_subset he hK))
      simp only [List.foldl_cons, hstep]
      apply ih hlorder (insert (e : α) K) (insert_subset he hK)
      intro x hx
      rcases hcover x hx with hxK | ⟨a, ha, rfl⟩
      · exact Or.inl (Or.inr hxK)
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact Or.inl (Or.inl rfl)
        · exact Or.inr ⟨a, ha, rfl⟩
    · apply Subset.trans ?_ (greedyFold_extensive S (e :: l) K)
      intro x hx
      rcases hcover x hx with hxK | ⟨a, ha, rfl⟩
      · exact hxK
      · rcases List.mem_cons.mp ha with rfl | ha
        · exact (he hx).elim
        · exact (not_lt_of_ge (heorder a ha) (hpriority a e hx he)).elim

theorem greedyOutput_contains_priority (S : IndependenceSystem E) (w : E → ℝ)
    (tie : LinearOrder E) (I : Set α) (hI : S.Indep I)
    (hpriority : ∀ a b : E, (a : α) ∈ I → (b : α) ∉ I → w b < w a) :
    I ⊆ greedyOutput S w tie := by
  unfold greedyOutput greedyState
  rw [List.take_length]
  apply greedyFold_contains_priority S w I hI hpriority (greedyEnumeration S w tie)
  · apply (greedyEnumeration_pairwise S w tie).imp
    intro a b hab
    exact hab.elim le_of_lt (fun h => le_of_eq h.1.symm)
  · exact empty_subset I
  · intro x hx
    exact Or.inr ⟨⟨x, S.subset_ground hI hx⟩, greedyEnumeration_mem S w tie _, rfl⟩

private theorem subsetWeight_indicator (S : IndependenceSystem E) (tie : LinearOrder E)
    (I : Set α) (hI : I ⊆ E) :
    subsetWeight S (fun e => if (e : α) ∈ I then 1 else 0) E = (I.ncard : ℝ) := by
  classical
  let w : E → ℝ := fun e => if (e : α) ∈ I then 1 else 0
  rw [← enumeration_subsetWeight S w tie E]
  simpa only [w, Subtype.coe_prop, ite_true] using
    enumeration_indicator_sum S w tie I hI

/-- A failed augmenting pair defeats greedy for every tie order. -/
theorem failed_augmentation_suboptimal (S : IndependenceSystem E) (tie : LinearOrder E)
    (I J : Set α) (hI : S.Indep I) (hJ : S.Indep J) (hcard : I.ncard < J.ncard)
    (hfail : ∀ e ∈ J \ I, ¬ S.Indep (insert e I)) :
    ∃ w : E → ℝ, (∀ e, 0 ≤ w e) ∧
      subsetWeight S w (greedyOutput S w tie) < subsetWeight S w J := by
  classical
  let ε : ℝ := 1 / ((I.ncard : ℝ) + 1)
  have hn : (0 : ℝ) ≤ I.ncard := Nat.cast_nonneg _
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεeq : ε * ((I.ncard : ℝ) + 1) = 1 := by
    dsimp [ε]
    field_simp
  let w : E → ℝ := fun e => if (e : α) ∈ I then 1 + ε
    else if (e : α) ∈ J then 1 else 0
  have hw : ∀ e, 0 ≤ w e := by
    intro e
    dsimp [w]
    split_ifs <;> linarith
  let G := greedyOutput S w tie
  have hIG : I ⊆ G := by
    apply greedyOutput_contains_priority S w tie I hI
    intro a b ha hb
    dsimp [w]
    simp only [ite_eq_left ha, ite_eq_right hb]
    split_ifs <;> linarith
  have hG : S.Indep G := (greedyOutput_maximal S w tie).2.1
  have havoid : ∀ e ∈ J \ I, e ∉ G := by
    intro e he heG
    exact hfail e he (S.hereditary hG (insert_subset heG hIG))
  have hweight : subsetWeight S w G = (1 + ε) * (I.ncard : ℝ) := by
    rw [← subsetWeight_indicator S tie I (S.subset_ground hI)]
    let := S.finite_ground.fintype
    unfold subsetWeight
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hi : (e : α) ∈ I
    · simp [hi, hIG hi, w]
    · by_cases hj : (e : α) ∈ J
      · simp [hi, havoid e ⟨hj, hi⟩, w]
      · simp [hi, hj, w]
  have hJweight : (J.ncard : ℝ) ≤ subsetWeight S w J := by
    rw [← subsetWeight_indicator S tie J (S.subset_ground hJ)]
    let := S.finite_ground.fintype
    unfold subsetWeight
    apply Finset.sum_le_sum
    intro e _
    by_cases hj : (e : α) ∈ J
    · simp only [Subtype.coe_prop, ite_true, hj]
      dsimp [w]
      split_ifs <;> linarith
    · simp [hj]
  have hlt : (1 + ε) * (I.ncard : ℝ) < (I.ncard : ℝ) + 1 := by
    nlinarith
  have hcards : (I.ncard : ℝ) + 1 ≤ (J.ncard : ℝ) := by
    exact_mod_cast hcard
  refine ⟨w, hw, ?_⟩
  change subsetWeight S w G < _
  rw [hweight]
  exact (hlt.trans_le hcards).trans_le hJweight

private theorem augmentation_of_greedy_independent (S : IndependenceSystem E)
    (tie : LinearOrder E)
    (hopt : ∀ w : E → ℝ, (∀ e, 0 ≤ w e) →
      IndependentOptimal S w (greedyOutput S w tie)) : Augmentation S := by
  intro I J hI hJ hcard
  by_contra hno
  have hfail : ∀ e ∈ J \ I, ¬ S.Indep (insert e I) := by
    simpa only [not_exists, not_and] using hno
  obtain ⟨w, hw, hbad⟩ := failed_augmentation_suboptimal S tie I J hI hJ hcard hfail
  exact (not_lt_of_ge ((hopt w hw).2 J hJ)) hbad

private theorem greedy_independent_of_augmentation (S : IndependenceSystem E)
    (h : Augmentation S) (w : E → ℝ) (tie : LinearOrder E) (hw : ∀ e, 0 ≤ w e) :
    IndependentOptimal S w (greedyOutput S w tie) := by
  have heq : fromMatroid (ofAugmentation S h) = S := by cases S; rfl
  have hopt := greedyIndependentOptimal (ofAugmentation S h) w tie hw
  change IndependentOptimal (fromMatroid (ofAugmentation S h)) w
    (greedyOutput (fromMatroid (ofAugmentation S h)) w tie) at hopt
  rw [heq] at hopt
  exact hopt

theorem greedy_characterization_fixed (S : IndependenceSystem E) (tie : LinearOrder E) :
    (Augmentation S ↔ ∀ w : E → ℝ, (∀ e, 0 ≤ w e) →
      BasisOptimal S w (greedyOutput S w tie)) ∧
    (Augmentation S ↔ ∀ w : E → ℝ, (∀ e, 0 ≤ w e) →
      IndependentOptimal S w (greedyOutput S w tie)) := by
  have hi : Augmentation S ↔ ∀ w : E → ℝ, (∀ e, 0 ≤ w e) →
      IndependentOptimal S w (greedyOutput S w tie) :=
    ⟨fun h w hw => greedy_independent_of_augmentation S h w tie hw,
      augmentation_of_greedy_independent S tie⟩
  refine ⟨?_, hi⟩
  constructor
  · intro h w hw
    exact (greedy_objectives_iff S w tie hw).mpr (hi.mp h w hw)
  · intro h
    apply hi.mpr
    intro w hw
    exact (greedy_objectives_iff S w tie hw).mp (h w hw)

theorem greedy_characterization_all (S : IndependenceSystem E) :
    (Augmentation S ↔ ∀ (w : E → ℝ) (tie : LinearOrder E), (∀ e, 0 ≤ w e) →
      BasisOptimal S w (greedyOutput S w tie)) ∧
    (Augmentation S ↔ ∀ (w : E → ℝ) (tie : LinearOrder E), (∀ e, 0 ≤ w e) →
      IndependentOptimal S w (greedyOutput S w tie)) := by
  classical
  let := S.finite_ground.fintype
  let tie₀ : LinearOrder E := LinearOrder.lift' (Fintype.equivFin E) (Fintype.equivFin E).injective
  constructor
  · constructor
    · intro h w tie hw
      exact (greedy_characterization_fixed S tie).1.mp h w hw
    · intro h
      exact (greedy_characterization_fixed S tie₀).1.mpr (fun w hw => h w tie₀ hw)
  · constructor
    · intro h w tie hw
      exact (greedy_characterization_fixed S tie).2.mp h w hw
    · intro h
      exact (greedy_characterization_fixed S tie₀).2.mpr (fun w hw => h w tie₀ hw)

end FiniteCombinatorics.Matroid
