import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.EdmondsKarp
import MathGenome.Internal.ExtremalOptimization.P205.Networks.ShortestPathBound
import MathGenome.Internal.ExtremalOptimization.P205.Networks.MaxFlowMinCut
import MathGenome.Internal.ExtremalOptimization.P205.Networks.ResidualBFSIteration

open scoped Classical
universe u v
namespace P205.Networks
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows

namespace EdmondsKarp
open EdmondsKarpSpec
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- A suffix beginning at any visited vertex has no greater length. -/
theorem suffix_at_vertex {G : Digraph V A} {s t : V} (p : Walk G s t)
    (x : V) (hx : x ∈ p.vertices) : ∃ q : Walk G x t, q.length ≤ p.length := by
  induction p with
  | nil s =>
    have h : x = s := by simpa using hx
    subst x
    exact ⟨.nil s, le_rfl⟩
  | @cons s y t a p ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst x
      exact ⟨.cons a p, le_rfl⟩
    · obtain ⟨q, hq⟩ := ih h
      exact ⟨q, by simp only [Walk.length_cons]; omega⟩

/-- A minimum-length walk has no repeated vertex, even with loops and
parallel/opposite labelled arcs. -/
theorem shortest_isPath {G : Digraph V A} {s t : V} (p : Walk G s t)
    (hp : DistanceSpec.IsShortest p) : p.IsPath := by
  induction p with
  | nil => exact Walk.nil_isPath _ _
  | @cons s y t a p ih =>
    have htail : DistanceSpec.IsShortest p := by
      intro q
      have h := hp (.cons a q)
      simpa only [Walk.length_cons, Nat.add_le_add_iff_right] using h
    have hnodup := ih htail
    apply List.nodup_cons.mpr
    refine ⟨?_, hnodup⟩
    intro hs
    obtain ⟨q, hq⟩ := suffix_at_vertex p s hs
    have h := hp q
    simp only [Walk.length_cons] at h
    omega

/-- Well ordering of the actual walk lengths gives a shortest path. This
existence lemma carries no runtime claim; BFS realization is separate. -/
theorem shortest_exists {G : Digraph V A} {s t : V}
    (h : Nonempty (Walk G s t)) :
    ∃ p : Walk G s t, p.IsPath ∧ DistanceSpec.IsShortest p := by
  classical
  let P : ℕ → Prop := fun n => ∃ p : Walk G s t, p.length = n
  have hP : ∃ n, P n := by obtain ⟨p⟩ := h; exact ⟨p.length, p, rfl⟩
  obtain ⟨p, hp⟩ := Nat.find_spec hP
  have hshort : DistanceSpec.IsShortest p := by
    intro q
    rw [hp]
    exact Nat.find_min' hP ⟨q, rfl⟩
  exact ⟨p, shortest_isPath p hshort, hshort⟩

theorem step_feasible {N : Network V A} {f g : A → ℝ}
    (hf : N.Feasible f) (S : ShortestBoundSpec.AugmentationStep N f g) :
    N.Feasible g := by
  obtain ⟨hb, hd⟩ := augment_path N.graph (fun _ => 0) N.capacity f S.path
    S.isPath hf.1 S.amount S.amount S.bottleneck S.bottleneck.1.le le_rfl
  rw [S.update]
  refine ⟨hb, ?_⟩
  intro x hs ht
  change N.graph.divergence (BoundedSpec.augment N.graph (fun _ => 0) N.capacity f S.path S.amount) x = 0
  rw [hd]
  have hz : N.graph.divergence f x = 0 := hf.2 x hs ht
  simp [hz, Ne.symm hs, Ne.symm ht]

theorem arcs_ne_nil_of_ne {G : Digraph V A} {x y : V} (hxy : x ≠ y)
    (p : Walk G x y) : p.arcs ≠ [] := by
  cases p with
  | nil => exact (hxy rfl).elim
  | cons a p => simp

/-- Every legal search outcome exists, including in a network with no arcs. -/
theorem search_exists : EdmondsKarpSpec.search_exists.{u,v} := by
  intro V A _ _ N f
  classical
  by_cases h : Nonempty (Walk (residual N f) N.source N.sink)
  · obtain ⟨p, hp, hs⟩ := shortest_exists h
    have hne := arcs_ne_nil_of_ne N.source_ne_sink p
    obtain ⟨δ, hδ⟩ := exists_bottleneck N.graph (fun _ => 0) N.capacity f p hne
    exact ⟨.found (BoundedSpec.augment N.graph (fun _ => 0) N.capacity f p δ)
      ⟨p, hp, hs, δ, hδ, rfl⟩⟩
  · exact ⟨.exhausted h⟩

noncomputable def defaultStrategy (N : Network V A) : Strategy N :=
  fun _ f => Classical.choice (search_exists N f)

theorem flow_feasible (N : Network V A) (choose : Strategy N) (i : ℕ) :
    N.Feasible (flow N choose i) := by
  induction i with
  | zero => exact N.zero_feasible
  | succ i ih =>
    change N.Feasible (advance (choose i (flow N choose i)))
    cases choose i (flow N choose i) with
    | found g S => exact step_feasible ih S
    | exhausted _ => exact ih

/-- No legal selector can augment after its residual graph is exhausted. -/
theorem advance_of_no_walk {N : Network V A} {f : A → ℝ}
    (h : ¬ Nonempty (Walk (residual N f) N.source N.sink)) (r : SearchResult N f) :
    advance r = f := by
  cases r with
  | exhausted _ => rfl
  | found g S => exact (h ⟨S.path⟩).elim

/-- Pad a stopped execution by holding its flow fixed. These padded positions
are never charged as augmentations. -/
theorem flow_stable (N : Network V A) (choose : Strategy N) (n : ℕ)
    (h : ¬ Nonempty (Walk (residual N (flow N choose n)) N.source N.sink)) :
    ∀ i : ℕ, n ≤ i → flow N choose i = flow N choose n := by
  intro i hi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  induction k with
  | zero => simp
  | succ k ih =>
    change advance (choose (n + k) (flow N choose (n + k))) = _
    rw [ih (by omega)]
    exact advance_of_no_walk h _

/-- If all earlier searches found a path, the actual iterates form precisely
a run to which the accepted real-capacity augmentation bound applies. -/
noncomputable def prefixRun (N : Network V A) (choose : Strategy N) (n : ℕ)
    (h : ∀ i : ℕ, i < n → Nonempty
      (Walk (residual N (flow N choose i)) N.source N.sink)) :
    ShortestBoundSpec.Run N n where
  flow := flow N choose
  initial_feasible := N.zero_feasible
  step i := by
    have hi := h i.val i.isLt
    have hex : Nonempty (ShortestBoundSpec.AugmentationStep N
        (flow N choose i.val) (flow N choose (i.val + 1))) := by
      generalize he : choose i.val (flow N choose i.val) = r
      cases r with
      | exhausted hn => exact (hn hi).elim
      | found g S =>
        have hnext : flow N choose (i.val + 1) = g := by
          change advance (choose i.val (flow N choose i.val)) = g
          rw [he]; rfl
        exact ⟨hnext.symm ▸ S⟩
    exact Classical.choice hex

/-- A residual walk cannot persist through the first B+1 searches: that
would give B+1 actual augmentations, contradicting the uniform prefix bound. -/
theorem exhaustion_exists (N : Network V A) (choose : Strategy N) :
    ∃ n : ℕ, n ≤ 2 * Fintype.card V * Fintype.card A ∧
      ¬ Nonempty (Walk (residual N (flow N choose n)) N.source N.sink) := by
  classical
  by_contra hn
  have h : ∀ i : ℕ, i < 2 * Fintype.card V * Fintype.card A + 1 →
      Nonempty (Walk (residual N (flow N choose i)) N.source N.sink) := by
    intro i hi
    by_contra hni
    exact hn ⟨i, by omega, hni⟩
  have hb := shortest_augmentation_bound N _ (prefixRun N choose _ h)
  omega

/-- Termination at the first failed search, for every permitted shortest-path
tie choice, with one final unsuccessful search and the reachable-cut certificate. -/
theorem termination : EdmondsKarpSpec.termination.{u,v} := by
  intro V A _ _ N choose
  classical
  let P : ℕ → Prop := fun n =>
    ¬ Nonempty (Walk (residual N (flow N choose n)) N.source N.sink)
  have hex : ∃ n, P n := by
    obtain ⟨n, hn, h⟩ := exhaustion_exists N choose
    exact ⟨n, h⟩
  let n := Nat.find hex
  have hstop : P n := Nat.find_spec hex
  have hb : n ≤ 2 * Fintype.card V * Fintype.card A := by
    obtain ⟨m, hm, h⟩ := exhaustion_exists N choose
    exact (Nat.find_min' hex h).trans hm
  have hf := flow_feasible N choose n
  have hc := residual_reachable_cut N (flow N choose n) hf hstop
  refine ⟨n, hb, ⟨hstop, hf, hc⟩, ?_, flow_stable N choose n hstop⟩
  intro i hi
  have hwalk : ¬ P i := Nat.find_min hex hi
  cases he : choose i (flow N choose i) with
  | exhausted hno => exact (hwalk hno).elim
  | found g S => exact ⟨g, S, rfl⟩

/-- Convert only the actual concrete output to a semantic step. The chosen
proof witness is erased and is never used to find or replace the BFS path. -/
theorem iteration_result (N : Network V A) (f : A → ℝ) (hf : N.Feasible f)
    (rows : BFSSpec.Rows V A) (hl : BFSSpec.LegalRows N.graph rows) :
    ∃ r : SearchResult N f,
      advance r = nextFlow f (IterationSpec.iteration N f rows).1 := by
  have hc := (ResidualBFSIteration.iteration_correct_and_linear N f hf rows hl).1
  cases he : (IterationSpec.iteration N f rows).1 with
  | none =>
    have hn : ¬ Nonempty (Walk (residual N f) N.source N.sink) := by
      simpa only [IterationSpec.Correct, he] using hc
    exact ⟨.exhausted hn, by simp [advance, nextFlow]⟩
  | some out =>
    simp only [IterationSpec.Correct, he] at hc
    obtain ⟨p, _, _, hp, hs, _, hb, hu, _⟩ := hc
    exact ⟨.found out.flow ⟨p, hp, hs, out.amount, hb, hu⟩,
      by simp [advance, nextFlow]⟩

theorem iteration_none_iff (N : Network V A) (f : A → ℝ) (hf : N.Feasible f)
    (rows : BFSSpec.Rows V A) (hl : BFSSpec.LegalRows N.graph rows) :
    (IterationSpec.iteration N f rows).1 = none ↔
      ¬ Nonempty (Walk (residual N f) N.source N.sink) := by
  have hc := (ResidualBFSIteration.iteration_correct_and_linear N f hf rows hl).1
  cases he : (IterationSpec.iteration N f rows).1 with
  | none => simpa only [IterationSpec.Correct, he, true_iff] using hc
  | some out =>
    simp only [IterationSpec.Correct, he] at hc
    obtain ⟨p, _⟩ := hc
    simp only [Option.some_ne_none, false_iff, not_not]
    exact ⟨p⟩

/-- Proof-only selector extending concrete outputs to the semantic interface.
The fallback is outside the feasible domain and is never run by the algorithm. -/
noncomputable def bfsStrategy (N : Network V A) (rows : BFSSpec.Rows V A)
    (hl : BFSSpec.LegalRows N.graph rows) : Strategy N :=
  fun _ f => if hf : N.Feasible f then Classical.choose (iteration_result N f hf rows hl)
    else defaultStrategy N 0 f

theorem bfs_flow_eq (N : Network V A) (rows : BFSSpec.Rows V A)
    (hl : BFSSpec.LegalRows N.graph rows) (i : ℕ) :
    bfsFlow N rows i = flow N (bfsStrategy N rows hl) i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    change nextFlow (bfsFlow N rows i)
      (IterationSpec.iteration N (bfsFlow N rows i) rows).1 =
        advance (bfsStrategy N rows hl i (flow N (bfsStrategy N rows hl) i))
    rw [ih]
    have hf := flow_feasible N (bfsStrategy N rows hl) i
    simpa only [bfsStrategy, dite_eq_left hf] using
      (Classical.choose_spec (iteration_result N _ hf rows hl)).symm

theorem bfs_refinement : EdmondsKarpSpec.bfs_refinement.{u,v} := by
  intro V A _ _ N rows hl
  exact ⟨bfsStrategy N rows hl, bfs_flow_eq N rows hl⟩

theorem bfs_flow_feasible (N : Network V A) (rows : BFSSpec.Rows V A)
    (hl : BFSSpec.LegalRows N.graph rows) (i : ℕ) : N.Feasible (bfsFlow N rows i) := by
  rw [bfs_flow_eq N rows hl]
  exact flow_feasible N _ i

theorem iteration_work_bound (N : Network V A) (f : A → ℝ) (hf : N.Feasible f)
    (rows : BFSSpec.Rows V A) (hl : BFSSpec.LegalRows N.graph rows) :
    (iterationWork N f rows).operations ≤ 310 * (Fintype.card V + Fintype.card A) ∧
    (iterationWork N f rows).inspections ≤ 310 * (Fintype.card V + Fintype.card A) := by
  have h := (ResidualBFSIteration.iteration_correct_and_linear N f hf rows hl).2
  have hv : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.source⟩
  simp only [iterationWork, BFSSpec.Work.plus, loopControl, BFSSpec.Work.events]
  constructor <;> simp_all <;> omega

theorem prefix_work_bound (N : Network V A) (rows : BFSSpec.Rows V A)
    (hl : BFSSpec.LegalRows N.graph rows) (k : ℕ) :
    (prefixWork N rows k).operations ≤ k * (310 * (Fintype.card V + Fintype.card A)) ∧
    (prefixWork N rows k).inspections ≤ k * (310 * (Fintype.card V + Fintype.card A)) := by
  induction k with
  | zero => simp [prefixWork]
  | succ k ih =>
    have h := iteration_work_bound N _ (bfs_flow_feasible N rows hl k) rows hl
    rw [prefixWork]
    simp only [BFSSpec.Work.plus]
    constructor <;> rw [Nat.succ_mul] <;> omega

theorem bfs_termination : EdmondsKarpSpec.bfs_termination.{u,v} := by
  intro V A _ _ N rows hl
  let choose := bfsStrategy N rows hl
  have heq : ∀ i, bfsFlow N rows i = flow N choose i := bfs_flow_eq N rows hl
  obtain ⟨n, hb, hc, hp, hs⟩ := termination N choose
  have hf : ∀ i, N.Feasible (bfsFlow N rows i) := bfs_flow_feasible N rows hl
  have hn : (IterationSpec.iteration N (bfsFlow N rows n) rows).1 = none := by
    apply (iteration_none_iff N _ (hf n) rows hl).mpr
    rw [heq]
    exact hc.1
  refine ⟨n, hb, ?_, hn, ?_, ?_, ?_, (prefix_work_bound N rows hl (n + 1)).1,
    (prefix_work_bound N rows hl (n + 1)).2⟩
  · rw [heq]; exact hc
  · intro i hi
    cases ho : (IterationSpec.iteration N (bfsFlow N rows i) rows).1 with
    | some out => exact ⟨out, rfl⟩
    | none =>
      have hno := (iteration_none_iff N _ (hf i) rows hl).mp ho
      obtain ⟨g, S, _⟩ := hp i hi
      rw [heq] at hno
      exact (hno ⟨S.path⟩).elim
  · intro i hi
    rw [heq, heq, hs i hi]
  · intro i
    exact ⟨hf i,
      (ResidualBFSIteration.iteration_correct_and_linear N _ (hf i) rows hl).1,
      iteration_work_bound N _ (hf i) rows hl⟩

/-- Unrolling stops at the first failed search, before fuel exhaustion.
The cost equality counts each preceding successful iteration and that one
failed iteration exactly once. -/
theorem execute_first_failure (N : Network V A) (rows : BFSSpec.Rows V A)
    (n : ℕ) (hn : (IterationSpec.iteration N (bfsFlow N rows n) rows).1 = none)
    (hp : ∀ i, i < n → ∃ out,
      (IterationSpec.iteration N (bfsFlow N rows i) rows).1 = some out)
    (k i : ℕ) (hi : i ≤ n) (hk : n - i < k) :
    let out := execute N rows k (bfsFlow N rows i)
    out.finished = true ∧ out.flow = bfsFlow N rows n ∧
    out.augmentations = n - i ∧ out.searches = n - i + 1 ∧
    (prefixWork N rows i).operations + out.work.operations =
      (prefixWork N rows (n + 1)).operations ∧
    (prefixWork N rows i).inspections + out.work.inspections =
      (prefixWork N rows (n + 1)).inspections := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
    by_cases hin : i = n
    · subst i
      simp only [execute, hn, Nat.sub_self, Nat.zero_add]
      exact ⟨trivial, trivial, trivial, trivial, rfl, rfl⟩
    · have hil : i < n := by omega
      obtain ⟨out, ho⟩ := hp i hil
      have hnext : bfsFlow N rows (i + 1) = out.flow := by
        simp only [bfsFlow, ho, nextFlow]
      obtain ⟨ht, hf, ha, hs, hops, hins⟩ := ih (i + 1) (by omega) (by omega)
      simp only [prefixWork, BFSSpec.Work.plus] at hops hins
      simp only [execute, ho]
      simp only [← hnext]
      refine ⟨ht, hf, ?_, ?_, ?_, ?_⟩
      · rw [ha]; omega
      · rw [hs]; omega
      · simp only [prefixWork, BFSSpec.Work.plus]; omega
      · simp only [prefixWork, BFSSpec.Work.plus]; omega

omit [Fintype A] in
@[simp] theorem zero_work_operations (as : List A) :
    (zeroWork as).operations = 5 * as.length + 1 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [zeroWork, BFSSpec.Work.events, BFSSpec.Work.plus, ih]; omega

omit [Fintype A] in
@[simp] theorem zero_work_inspections (as : List A) : (zeroWork as).inspections = 0 := by
  induction as with
  | nil => rfl
  | cons a as ih => simp [zeroWork, BFSSpec.Work.events, BFSSpec.Work.plus, ih]

theorem setup_work_bound (N : Network V A) (vs : List V) (as : List A)
    (hv : BFSSpec.Enumeration vs) (ha : BFSSpec.Enumeration as) :
    (setupWork vs as).operations ≤ 40 * (Fintype.card V + Fintype.card A) ∧
    (setupWork vs as).inspections = 0 := by
  have hp := (ResidualBFSIteration.setup_linear N vs as hv ha).2
  have hlen := ResidualBFSIteration.enumeration_length as ha
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.source⟩
  simp only [setupWork, BFSSpec.Work.plus, zero_work_operations, zero_work_inspections,
    hlen]
  constructor <;> omega

/-- Complete program correctness, including the actual bounded interpreter,
once-only setup, n successful updates and one unsuccessful search. -/
theorem algorithm_correct_and_linear : EdmondsKarpSpec.algorithm_correct_and_linear.{u,v} := by
  intro V A _ _ N vs as hv ha
  let rows := BFSSpec.prepareFromArcs N.graph as
  have hl : BFSSpec.LegalRows N.graph rows :=
    (ResidualBFSIteration.setup_linear N vs as hv ha).1
  obtain ⟨n, hb, hc⟩ := bfs_termination N rows hl
  obtain ⟨ht, hf, hau, hse, hops, hins⟩ := execute_first_failure N rows n hc.2.1 hc.2.2.1
    (2 * Fintype.card V * Fintype.card A + 1) 0 (by omega) (by omega)
  simp only [Nat.sub_zero, prefixWork, Nat.zero_add] at hau hse hops hins
  have hsetup := setup_work_bound N vs as hv ha
  let out := execute N rows (2 * Fintype.card V * Fintype.card A + 1) (fun _ => 0)
  change out.finished = true at ht
  change out.flow = bfsFlow N rows n at hf
  change out.augmentations = n at hau
  change out.searches = n + 1 at hse
  change out.work.operations = (prefixWork N rows (n + 1)).operations at hops
  change out.work.inspections = (prefixWork N rows (n + 1)).inspections at hins
  change out.finished = true ∧
    out.augmentations ≤ 2 * Fintype.card V * Fintype.card A ∧
    out.searches = out.augmentations + 1 ∧
    TerminalCertificate N out.flow ∧ BFSExecution N rows out.augmentations ∧
    out.flow = bfsFlow N rows out.augmentations ∧
    ((setupWork vs as).plus out.work).operations ≤
      (40 + 310 * out.searches) * (Fintype.card V + Fintype.card A) ∧
    ((setupWork vs as).plus out.work).inspections ≤
      310 * out.searches * (Fintype.card V + Fintype.card A) ∧
    ((setupWork vs as).plus out.work).operations ≤
      (40 + 310 * (2 * Fintype.card V * Fintype.card A + 1)) *
        (Fintype.card V + Fintype.card A)
  simp only [ht, hau, hse, hf]
  refine ⟨trivial, hb, trivial, hc.1, hc, trivial, ?_, ?_, ?_⟩
  · simp only [BFSSpec.Work.plus]
    rw [hops]
    have hcost := hc.2.2.2.2.2.1
    nlinarith [hsetup.1]
  · simp only [BFSSpec.Work.plus]
    rw [hins, hsetup.2]
    have hcost := hc.2.2.2.2.2.2
    nlinarith
  · simp only [BFSSpec.Work.plus]
    rw [hops]
    have hcost := hc.2.2.2.2.2.1
    have hmul : (n + 1) * (310 * (Fintype.card V + Fintype.card A)) ≤
        (2 * Fintype.card V * Fintype.card A + 1) *
          (310 * (Fintype.card V + Fintype.card A)) :=
      Nat.mul_le_mul_right _ (Nat.add_le_add_right hb 1)
    nlinarith [hsetup.1]

end EdmondsKarp

theorem edmonds_karp_search_exists : EdmondsKarpSpec.search_exists.{u,v} :=
  EdmondsKarp.search_exists

theorem edmonds_karp_prefix_feasible : EdmondsKarpSpec.prefix_feasible.{u,v} :=
  EdmondsKarp.flow_feasible

theorem edmonds_karp_termination : EdmondsKarpSpec.termination.{u,v} :=
  EdmondsKarp.termination

theorem edmonds_karp_bfs_refinement : EdmondsKarpSpec.bfs_refinement.{u,v} :=
  EdmondsKarp.bfs_refinement

theorem edmonds_karp_bfs_termination : EdmondsKarpSpec.bfs_termination.{u,v} :=
  EdmondsKarp.bfs_termination

theorem edmonds_karp_algorithm_correct_and_linear :
    EdmondsKarpSpec.algorithm_correct_and_linear.{u,v} :=
  EdmondsKarp.algorithm_correct_and_linear

end P205.Networks
