import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.Hungarian
import MathGenome.Internal.ExtremalOptimization.P205.Matching.HungarianStep
import MathGenome.Internal.ExtremalOptimization.P205.Matching.PerfectAssignment
import Batteries.Tactic.OpenPrivate
import Mathlib.Order.WellFounded

set_option linter.unusedSectionVars false
universe u v
noncomputable section
namespace P205.Matching.Hungarian.Algorithm
open Specs.P205.Matching
open Specs.P205.Matching.Hungarian
open Specs.P205.Matching.Hungarian.Algorithm
open private search_edge_tight from MathGenome.Internal.ExtremalOptimization.P205.Matching.HungarianStep

variable {L : Type u} {R : Type v} [Fintype L] [Fintype R]
  {G : BipartiteGraph L R} {w : Edge G → ℝ}

/-- Both endpoint projections are injective on a matching. -/
lemma left_injective {M : Set (Edge G)} (hM : IsMatching M) :
    Function.Injective (fun e : M => e.val.val.1) := by
  intro e f hef
  exact Subtype.ext (hM.1 e.val e.property f.val f.property hef)

lemma right_injective {M : Set (Edge G)} (hM : IsMatching M) :
    Function.Injective (fun e : M => e.val.val.2) := by
  intro e f hef
  exact Subtype.ext (hM.2 e.val e.property f.val f.property hef)

lemma matching_card_le {M : Set (Edge G)} (hM : IsMatching M) : Nat.card M ≤ Nat.card L :=
  Nat.card_le_card_of_injective _ (left_injective hM)

lemma side_card_eq (hP : ∃ P : Set (Edge G), IsPerfectMatching P) :
    Nat.card L = Nat.card R := by
  obtain ⟨P, hP⟩ := hP
  have hl : Function.Surjective (fun e : P => e.val.val.1) := by
    intro i
    obtain ⟨e, he, hei⟩ := hP.2 (.inl i)
    exact ⟨⟨e, he⟩, hei.symm⟩
  have hr : Function.Surjective (fun e : P => e.val.val.2) := by
    intro j
    obtain ⟨e, he, hej⟩ := hP.2 (.inr j)
    exact ⟨⟨e, he⟩, hej.symm⟩
  exact (Nat.card_eq_of_bijective _ ⟨left_injective hP.1, hl⟩).symm.trans
    (Nat.card_eq_of_bijective _ ⟨right_injective hP.1, hr⟩)

lemma perfect_of_left_covered (hP : ∃ P : Set (Edge G), IsPerfectMatching P)
    {M : Set (Edge G)} (hM : IsMatching M) (hl : ∀ i, Covered M (.inl i)) :
    IsPerfectMatching M := by
  have hsurj : Function.Surjective (fun e : M => e.val.val.1) := by
    intro i
    obtain ⟨e, he, hei⟩ := hl i
    exact ⟨⟨e, he⟩, hei.symm⟩
  have hc : Nat.card M = Nat.card R :=
    (Nat.card_eq_of_bijective _ ⟨left_injective hM, hsurj⟩).trans (side_card_eq hP)
  have hr := ((Nat.bijective_iff_injective_and_card
    (fun e : M => e.val.val.2)).mpr ⟨right_injective hM, hc⟩).2
  refine ⟨hM, ?_⟩
  intro z
  cases z with
  | inl i => exact hl i
  | inr j =>
    obtain ⟨e, he⟩ := hr j
    exact ⟨e.val, e.property, he.symm⟩

theorem initialization : Specs.P205.Matching.Hungarian.Algorithm.initializationType.{u,v} := by
  intro L R _ _ G w hP
  exact ⟨(P205.Matching.Hungarian.initialization w hP).1, by simp [initial]⟩

theorem update_progress : updateProgressType.{u,v} := by
  intro L R _ _ G w M i p q hP h
  rcases h with ⟨h, hi, hs, rfl⟩
  have hu := potential_update w p.1 p.2 M i hP h hi hs
  exact ⟨hu.1, hu.2.2.2⟩

lemma reach_card_le (w : Edge G → ℝ) (a : L → ℝ) (b : R → ℝ)
    (M : Set (Edge G)) (i : L) : Nat.card (rightReach w a b M i) ≤ Nat.card R :=
  Nat.card_le_card_of_injective Subtype.val Subtype.val_injective

theorem update_bound : updateBoundType.{u,v} := by
  intro L R _ _ G w M i hP p n hp
  have hsum : ∀ m ≤ n,
      m + Nat.card (rightReach w (p 0).1 (p 0).2 M i) ≤
        Nat.card (rightReach w (p m).1 (p m).2 M i) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
      have hprev := ih (by omega)
      have hstrict := Set.ncard_lt_ncard (update_progress w M i _ _ hP (hp m (by omega))).2
      change Nat.card (rightReach w (p m).1 (p m).2 M i) <
        Nat.card (rightReach w (p (m + 1)).1 (p (m + 1)).2 M i) at hstrict
      omega
  exact (hsum n le_rfl).trans (reach_card_le w _ _ M i)

/-- Every permitted path flip preserves legality, rather than merely some
chosen augmentation. This is needed for arbitrary path/tie choices. -/
theorem augmentation_progress : augmentationProgressType.{u,v} := by
  intro L R _ _ G w a b M N i j h ha
  classical
  obtain ⟨p, hp, hdir, hN⟩ := ha
  have hflip := FiniteCombinatorics.Graph.Matching.flipAlong_isMatching hp
  have hmatch : IsMatching N := by
    apply (P205.Matching.matching_iff_mathGenome N).mpr
    change FiniteCombinatorics.Graph.Matching.IsMatching (Specs.P205.Matching.graph G)
      (Specs.P205.Matching.edgeSet N)
    rw [hN]
    exact hflip
  refine ⟨⟨h.1, hmatch, ?_⟩, ?_⟩
  · intro e he
    have hem : Specs.P205.Matching.edgePair e ∈ Specs.P205.Matching.edgeSet N := ⟨e, he, rfl⟩
    rw [hN] at hem
    rcases hem with hold | hnew
    · have heM : e ∈ edgePair ⁻¹' edgeSet M := hold.1
      rw [P205.Matching.preimage_edgeSet] at heM
      exact h.2.2 e heM
    · obtain ⟨d, hd, hde⟩ := List.mem_map.mp hnew.1
      obtain ⟨f, hf, ht⟩ := search_edge_tight h (hdir d hd)
      have hfe : f = e := P205.Matching.edgePair_injective (hf.trans hde)
      exact hfe ▸ ht
  · have hc := FiniteCombinatorics.Graph.Matching.flipAlong_card hp
    change Nat.card (FiniteCombinatorics.Graph.Matching.flipAlong (edgeSet M) p) =
      Nat.card (edgeSet M) + 1 at hc
    rw [← hN] at hc
    have hcard (X : Set (Edge G)) : Nat.card (edgeSet X) = Nat.card X :=
      Set.ncard_image_of_injective X P205.Matching.edgePair_injective
    simpa only [hcard] using hc

theorem preservation : preservationType.{u,v} := by
  intro L R _ _ G w hP s t hst
  cases hst with
  | choose a b M i h hi =>
    refine ⟨h, ?_⟩
    intro k hk
    have hik : i = k := Option.some.inj hk
    exact hik ▸ hi
  | update M i p q hp =>
    refine ⟨(update_progress w M i p q hP hp).1, ?_⟩
    intro k hk
    have hik : i = k := Option.some.inj hk
    exact hik ▸ hp.2.1
  | augment a b M N i j h hi hj hf ha =>
    exact ⟨(augmentation_progress w a b M N i j h ha).1, by simp⟩

theorem progress : progressType.{u,v} := by
  intro L R _ _ G w hP s hs hn
  classical
  rcases s with ⟨a, b, M, r⟩
  cases r with
  | none =>
    have hfree : ∃ i, ¬ Covered M (.inl i) := by
      by_contra h
      push Not at h
      exact hn (perfect_of_left_covered hP hs.1.2.1 h)
    obtain ⟨i, hi⟩ := hfree
    exact ⟨_, .choose a b M i hs.1 hi⟩
  | some i =>
    have hi := hs.2 i rfl
    by_cases hstall : Stalled w a b M i
    · let p := (a, b)
      let q := (updateLeft a (leftReach w a b M i) (minimumSlack w a b M i),
        updateRight b (rightReach w a b M i) (minimumSlack w a b M i))
      exact ⟨_, .update M i p q ⟨hs.1, hi, hstall, rfl⟩⟩
    · change ¬ (∀ j ∈ rightReach w a b M i, Covered M (.inr j)) at hstall
      push Not at hstall
      obtain ⟨j, hj, hf⟩ := hstall
      obtain ⟨N, ha, _, _⟩ := augmentation w a b M i j hs.1 hi hj hf
      exact ⟨_, .augment a b M N i j hs.1 hi hj hf ha⟩

/-- Lexicographic progress: an augmentation decreases the first coordinate;
within a fixed root each update decreases the second coordinate. Root selection
uses the one extra unit reserved by `none`. -/
private def rank (w : Edge G → ℝ) (s : State G) : ℕ × ℕ :=
  (Nat.card L - Nat.card s.matching,
    match s.root with
    | none => Nat.card R + 1
    | some i => Nat.card R - Nat.card (rightReach w s.left s.right s.matching i))

lemma rank_decreases (hP : ∃ P : Set (Edge G), IsPerfectMatching P)
    {s t : State G} (h : Step w s t) :
    Prod.Lex (· < ·) (· < ·) (rank w t) (rank w s) := by
  cases h with
  | choose a b M i h hi =>
    apply Prod.Lex.right
    change Nat.card R - Nat.card (rightReach w a b M i) < Nat.card R + 1
    omega
  | update M i p q hp =>
    apply Prod.Lex.right
    have hg := Set.ncard_lt_ncard (update_progress w M i p q hP hp).2
    change Nat.card (rightReach w p.1 p.2 M i) <
      Nat.card (rightReach w q.1 q.2 M i) at hg
    have hb := reach_card_le w q.1 q.2 M i
    change Nat.card R - Nat.card (rightReach w q.1 q.2 M i) <
      Nat.card R - Nat.card (rightReach w p.1 p.2 M i)
    omega
  | augment a b M N i j h hi hj hf ha =>
    have hn := augmentation_progress w a b M N i j h ha
    have hb := matching_card_le hn.1.2.1
    apply Prod.Lex.left
    change Nat.card L - Nat.card N < Nat.card L - Nat.card M
    omega

theorem termination : terminationType.{u,v} := by
  intro L R _ _ G w hP
  exact Subrelation.wf (fun h => rank_decreases hP h)
    (InvImage.wf (rank w) (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf)

lemma reachable_valid (hP : ∃ P : Set (Edge G), IsPerfectMatching P)
    {s : State G} (h : Relation.ReflTransGen (Step w) (initial w) s) : Valid w s := by
  cases h with
  | refl => exact initialization w hP
  | tail _ hst => exact preservation w hP _ _ hst

lemma optimal_of_terminal (hP : ∃ P : Set (Edge G), IsPerfectMatching P)
    {s : State G} (hs : Valid w s) (ht : ¬ ∃ t, Step w s t) : Optimal w s := by
  have hm : IsPerfectMatching s.matching := by
    by_contra hn
    exact ht (progress w hP s hs hn)
  have heq := (PerfectAssignment.equality_iff_tight G w s.matching s.left s.right
    hm hs.1.1).mpr hs.1.2.2
  refine ⟨hm, hs.1.1, heq, ?_, ?_⟩
  · intro N hN
    rw [heq]
    exact PerfectAssignment.weak_duality G w N s.left s.right hN hs.1.1
  · intro a b hab
    rw [← heq]
    exact PerfectAssignment.weak_duality G w s.matching a b hm hab

theorem correctness : correctnessType.{u,v} := by
  intro L R _ _ G w hP s hs ht
  exact optimal_of_terminal hP (reachable_valid hP hs) ht

theorem completion : completionType.{u,v} := by
  intro L R _ _ G w hP s hs
  have hw := termination w hP
  have hex : ∀ x : State G, Valid w x →
      ∃ t, Relation.ReflTransGen (Step w) x t ∧ (¬ ∃ z, Step w t z) ∧ Optimal w t := by
    intro x
    induction x using hw.induction with
    | h x ih =>
      intro hx
      classical
      by_cases hnext : ∃ y, Step w x y
      · obtain ⟨y, hxy⟩ := hnext
        obtain ⟨t, hyt, ht, ho⟩ := ih y hxy (preservation w hP x y hxy)
        exact ⟨t, (Relation.ReflTransGen.single hxy).trans hyt, ht, ho⟩
      · exact ⟨x, .refl, hnext, optimal_of_terminal hP hx hnext⟩
  exact hex s (reachable_valid hP hs)

theorem execution_terminates : executionTerminatesType.{u,v} := by
  intro L R _ _ G w hP f hf
  classical
  have hreach : ∀ n, Relation.ReflTransGen (Step w) (initial w) (f n) := by
    intro n
    induction n with
    | zero => rw [hf.1]
    | succ n ih =>
      rcases hf.2 n with hstep | ⟨_, heq⟩
      · exact ih.tail hstep
      · rw [heq]; exact ih
  have hstop : ∃ n, ¬ ∃ t, Step w (f n) t := by
    by_contra h
    push Not at h
    have hchain : ∀ n, Step w (f n) (f (n + 1)) := by
      intro n
      rcases hf.2 n with hs | ⟨hn, _⟩
      · exact hs
      · exact (hn (h n)).elim
    exact (wellFounded_iff_isEmpty_descending_chain.mp (termination w hP)).false ⟨f, hchain⟩
  obtain ⟨n, hn⟩ := hstop
  refine ⟨n, hn, correctness w hP (f n) (hreach n) hn, ?_⟩
  have hstay : ∀ k, f (n + k) = f n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rcases hf.2 (n + k) with hstep | ⟨_, heq⟩
      · rw [ih] at hstep
        exact (hn ⟨_, hstep⟩).elim
      · exact heq.trans ih
  intro m hm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  exact hstay k

end P205.Matching.Hungarian.Algorithm
