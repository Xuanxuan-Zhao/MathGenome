import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ResidualBFS
import Lean.Elab.Tactic.Omega

open scoped Classical BigOperators
universe u v
namespace P205.Networks.ResidualBFS
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows
open BFSSpec

variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-! The executable RAM definitions are canonical shared definitions in the
independent Spec. The lemmas here prove properties of their actual transitions.
No correctness fields are added to the operational states. -/

@[simp] theorem work_plus_operations (w z : Work) :
    (w.plus z).operations = w.operations + z.operations := rfl
@[simp] theorem work_plus_inspections (w z : Work) :
    (w.plus z).inspections = w.inspections + z.inspections := rfl

@[simp] theorem reverse_work_operations (xs : List α) :
    (reverseWork xs).operations = 5 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [reverseWork, Work.events, ih]; omega

@[simp] theorem reverse_work_inspections (xs : List α) :
    (reverseWork xs).inspections = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [reverseWork, Work.events, ih]

@[simp] theorem build_work_operations (rs : List (Label A)) :
    (buildWork rs).operations = 9 * rs.length + 1 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [buildWork, Work.events, ih]; omega

@[simp] theorem build_work_inspections (rs : List (Label A)) :
    (buildWork rs).inspections = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [buildWork, Work.events, ih]

/-- FIFO reversal does not change the represented queue. -/
theorem rotate_contents (q : Queue V) (h : q.front = []) :
    (Queue.mk q.rear.reverse []).contents = q.contents := by
  simp [Queue.contents, h]

/-- Enqueue uses one cons, while the ghost observation is right append. -/
theorem enqueue_contents (q : Queue V) (x : V) :
    ({ q with rear := x :: q.rear } : Queue V).contents = q.contents ++ [x] := by
  simp [Queue.contents, List.reverse_cons, List.append_assoc]

/-- Adjacency construction never changes membership at another tail. -/
theorem mem_build_rows (G : Digraph V A) (rs : List (Label A)) (rows : Rows V A)
    (x : V) (r : Label A) :
    r ∈ buildRows G rs rows x ↔ r ∈ rows x ∨ r ∈ rs ∧ (signedGraph G).tail r = x := by
  induction rs generalizing rows with
  | nil => simp [buildRows]
  | cons a rs ih =>
    rw [buildRows, ih]
    by_cases hx : (signedGraph G).tail a = x
    · subst x
      simp only [Function.update_self, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inr ⟨by simp [h], by simp [h]⟩
        · exact Or.inl h
        · exact Or.inr ⟨Or.inr h.1, h.2⟩
      · rintro (h | ⟨h, ht⟩)
        · exact Or.inl (Or.inr h)
        · rcases h with h | h
          · exact Or.inl (Or.inl h)
          · exact Or.inr ⟨h, ht⟩
    · rw [Function.update_of_ne (Ne.symm hx)]
      constructor
      · rintro (h | ⟨h, ht⟩)
        · exact Or.inl h
        · exact Or.inr ⟨List.mem_cons_of_mem _ h, ht⟩
      · rintro (h | ⟨h, ht⟩)
        · exact Or.inl h
        · rcases List.mem_cons.mp h with h | h
          · subst r; exact (hx ht).elim
          · exact Or.inr ⟨h, ht⟩

/-- Inserting a list of previously absent, distinct signed labels preserves
row uniqueness. This proves actual construction, rather than filtering labels
separately for every vertex. -/
theorem nodup_build_rows (G : Digraph V A) (rs : List (Label A)) (rows : Rows V A)
    (hrs : rs.Nodup) (hrows : ∀ x, (rows x).Nodup)
    (hdisj : ∀ r ∈ rs, ∀ x, r ∉ rows x) :
    ∀ x, (buildRows G rs rows x).Nodup := by
  induction rs generalizing rows with
  | nil => exact hrows
  | cons a rs ih =>
    obtain ⟨ha, hs⟩ := List.nodup_cons.mp hrs
    apply ih _ hs
    · intro x
      by_cases hx : x = (signedGraph G).tail a
      · subst x
        rw [Function.update_self]
        exact List.nodup_cons.mpr ⟨hdisj a (by simp) _, hrows _⟩
      · rw [Function.update_of_ne hx]
        exact hrows x
    · intro r hr x
      by_cases hx : x = (signedGraph G).tail a
      · subst x
        rw [Function.update_self, List.mem_cons]
        rintro (he | hm)
        · subst r; exact ha hr
        · exact hdisj r (List.mem_cons_of_mem _ hr) _ hm
      · rw [Function.update_of_ne hx]
        exact hdisj r (List.mem_cons_of_mem _ hr) x

theorem prepare_rows_correct : BFSSpec.prepare_rows_correct.{u,v} := by
  intro V A _ _ G rs hrs
  constructor
  · apply nodup_build_rows G rs (fun _ => []) hrs.1
    · simp
    · simp
  · intro x r
    rw [prepareRows, mem_build_rows]
    simp [hrs.2 r]

/-- A halted machine has precisely no active row and no queued vertex. -/
theorem step_eq_none_iff (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (σ : State V A) :
    BFSSpec.step N f rows σ = none ↔
      σ.active = none ∧ σ.queue.front = [] ∧ σ.queue.rear = [] := by
  cases ha : σ.active with
  | some a =>
    rcases a with ⟨x, rs⟩
    cases rs with
    | nil => simp [BFSSpec.step, ha]
    | cons r rs =>
      by_cases hp : 0 < BoundedSpec.capacity (fun _ => 0) N.capacity f r
      · cases hy : σ.seen ((signedGraph N.graph).head r) <;>
          simp [BFSSpec.step, ha, hp, hy]
      · simp [BFSSpec.step, ha, hp]
  | none =>
    cases hf : σ.queue.front with
    | cons x xs => simp [BFSSpec.step, ha, hf]
    | nil => cases hb : σ.queue.rear <;> simp [BFSSpec.step, ha, hf, hb]

/-- Marking a previously unseen vertex transfers exactly its reserved work
from the unseen sum to the rear queue. No queue invariant is needed for this
resource argument. -/
theorem unseen_sum_update (rows : Rows V A) (seen : V → Bool) (y : V)
    (hy : seen y = false) :
    (∑ x, if Function.update seen y true x then 0 else (rows x).length + 4) +
      ((rows y).length + 4) =
    ∑ x, if seen x then 0 else (rows x).length + 4 := by
  let w : V → ℕ := fun x => if seen x then 0 else (rows x).length + 4
  have he : (fun x => if Function.update seen y true x then 0 else (rows x).length + 4) =
      Function.update w y 0 := by
    funext x
    by_cases hx : x = y
    · subst x; simp
    · simp [Function.update_of_ne hx, w]
  rw [he, Finset.sum_update_of_mem (Finset.mem_univ y)]
  rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ y) w]
  simp only [zero_add, w, hy, Bool.false_eq_true, ↓reduceIte]
  omega

theorem queue_weights_le (rows : Rows V A) (xs : List V) :
    (xs.map (fun x => (rows x).length + 3)).sum ≤
      (xs.map (fun x => (rows x).length + 4)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons]; omega

/-- Every transition strictly lowers a finite potential, including the
otherwise easily overlooked queue-reversal transition. -/
theorem step_decreases : BFSSpec.step_decreases.{u,v} := by
  intro V A _ _ N f rows σ τ w hs
  cases ha : σ.active with
  | some a =>
    rcases a with ⟨x, rs⟩
    cases rs with
    | nil =>
      simp only [BFSSpec.step, ha, Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨rfl, rfl⟩
      simp [potential, ha]
    | cons r rs =>
      simp only [BFSSpec.step, ha] at hs
      by_cases hp : 0 < BoundedSpec.capacity (fun _ => 0) N.capacity f r
      · simp only [hp, ↓reduceIte] at hs
        cases hy : σ.seen ((signedGraph N.graph).head r)
        · simp only [hy, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at hs
          rcases hs with ⟨rfl, rfl⟩
          have hh := unseen_sum_update rows σ.seen ((signedGraph N.graph).head r) hy
          simp only [potential, ha, List.map_cons, List.sum_cons, List.length_cons]
          omega
        · simp only [hy, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hs
          rcases hs with ⟨rfl, rfl⟩
          simp [potential, ha]
      · simp only [hp, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl⟩
        simp [potential, ha]
  | none =>
    cases hf : σ.queue.front with
    | cons x xs =>
      simp only [BFSSpec.step, ha, hf, Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨rfl, rfl⟩
      simp [potential, ha, hf]
      omega
    | nil =>
      cases hb : σ.queue.rear with
      | nil => simp [BFSSpec.step, ha, hf, hb] at hs
      | cons y ys =>
        simp only [BFSSpec.step, ha, hf, hb, Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl⟩
        simp only [potential, ha, hf, hb, List.map_nil, List.sum_nil, zero_add,
          List.map_reverse, List.sum_reverse, List.map_cons, List.sum_cons]
        have hsum := queue_weights_le rows ys
        omega

theorem budget_rows_eq (rows : Rows V A) (xs : List V) :
    budgetRows rows xs = (xs.map (fun x => (rows x).length + 4)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [budgetRows, ih]

theorem budget_eq (rows : Rows V A) :
    budget rows = ∑ x, ((rows x).length + 4) := by
  rw [budget, budget_rows_eq]
  simp

/-- The charged budget-counting pass computes exactly one more than the
initial potential. Thus the bounded interpreter cannot stop prematurely. -/
theorem initial_potential (rows : Rows V A) (s : V) :
    potential rows (initial s) + 1 = budget rows := by
  have h := unseen_sum_update rows (fun _ => false) s rfl
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  rw [budget_eq]
  simp only [potential, initial, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  simpa [initial, Function.update_apply, Nat.add_assoc] using h

/-- Every bounded interpreter execution is an execution of the primitive
transition relation, even when its fuel is insufficient. -/
theorem execute_execution (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (k : ℕ) (σ : State V A) :
    Execution N f rows σ (execute N f rows k σ).1 (execute N f rows k σ).2 := by
  induction k generalizing σ with
  | zero => exact .refl σ
  | succ k ih =>
    cases hs : BFSSpec.step N f rows σ with
    | none => simpa [execute, hs] using Execution.refl (N := N) (f := f) (rows := rows) σ
    | some tw =>
      rcases tw with ⟨τ, w⟩
      simpa [execute, hs] using Execution.next hs (ih τ)

/-- Fuel greater than the current potential always reaches a genuine halted
state. In particular a fuel cutoff is never used to infer correctness. -/
theorem execute_terminal (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (k : ℕ) (σ : State V A) (hk : potential rows σ < k) :
    BFSSpec.step N f rows (execute N f rows k σ).1 = none := by
  induction k generalizing σ with
  | zero => omega
  | succ k ih =>
    cases hs : BFSSpec.step N f rows σ with
    | none => simpa [execute, hs] using hs
    | some tw =>
      rcases tw with ⟨τ, w⟩
      have hd := step_decreases N f rows σ τ w hs
      have ht : potential rows τ < k := by omega
      simpa [execute, hs] using ih τ ht

/-- Termination holds for arbitrary finite rows and all real arc vectors.
Legal-row and feasibility hypotheses are only needed for graph correctness. -/
theorem search_terminates : BFSSpec.search_terminates.{u,v} := by
  intro V A _ _ N f rows
  constructor
  · exact execute_execution N f rows (budget rows) (initial N.source)
  · exact execute_terminal N f rows (budget rows) (initial N.source)
      (by have h := initial_potential rows N.source; omega)

@[simp] theorem mem_signed_labels (as : List A) (r : Label A) :
    r ∈ signedLabels as ↔ r.1 ∈ as := by
  induction as with
  | nil => simp [signedLabels]
  | cons a as ih =>
    rcases r with ⟨r, b⟩
    cases b <;> simp [signedLabels, ih]

theorem nodup_signed_labels (as : List A) (ha : as.Nodup) :
    (signedLabels as).Nodup := by
  induction as with
  | nil => simp [signedLabels]
  | cons a as ih =>
    obtain ⟨hna, has⟩ := List.nodup_cons.mp ha
    simp [signedLabels, List.nodup_cons, mem_signed_labels, hna, ih has]

theorem prepare_from_arcs_correct : BFSSpec.prepare_from_arcs_correct.{u,v} := by
  intro V A _ _ G as has
  apply prepare_rows_correct G (signedLabels as)
  exact ⟨nodup_signed_labels as has.1, fun r => (mem_signed_labels as r).mpr (has.2 r.1)⟩

/-- Ghost assertion about pointers, proved from the machine, rather than stored
in its state. Every non-root pointer descends strictly in the depth array. -/
structure ParentInvariant (N : Network V A) (f : A → ℝ) (σ : State V A) : Prop where
  source_seen : σ.seen N.source = true
  source_depth : σ.depth N.source = 0
  source_pred : σ.pred N.source = none
  parent : ∀ x, σ.seen x = true → x ≠ N.source →
    ∃ r : Label A, σ.pred x = some r ∧
      0 < BoundedSpec.capacity (fun _ => 0) N.capacity f r ∧
      (signedGraph N.graph).head r = x ∧
      σ.seen ((signedGraph N.graph).tail r) = true ∧
      σ.depth x = σ.depth ((signedGraph N.graph).tail r) + 1

/-- Appending a single arc adds exactly its terminal vertex. -/
theorem vertices_snoc {B : Type*} [Fintype B] {G : Digraph V B}
    {s x y : V} (p : Walk G s x) (a : Arc G x y) :
    (p.append (.cons a (.nil y))).vertices = p.vertices ++ [y] := by
  induction p with
  | nil => rfl
  | cons b p ih => simp only [Walk.cons_append, Walk.vertices_cons, ih, List.cons_append]

/-- Descending actual pointers constructs a simple residual walk and gives the
exact accumulator result of the specified tracer for every sufficient fuel. -/
theorem parent_path (N : Network V A) (f : A → ℝ) (σ : State V A)
    (h : ParentInvariant N f σ) (x : V) (hx : σ.seen x = true) :
    ∃ p : Walk (residual N f) N.source x,
      p.IsPath ∧ p.length = σ.depth x ∧
      (∀ y ∈ p.vertices, σ.depth y ≤ σ.depth x) ∧
      ∀ k, σ.depth x < k → ∀ acc,
        (traceAux N.graph N.source σ.pred k x acc).1 =
          some (p.arcs.map Subtype.val ++ acc) := by
  classical
  generalize hd : σ.depth x = d
  induction d using Nat.strong_induction_on generalizing x with
  | h d ih =>
    by_cases hxs : x = N.source
    · subst x
      have hd0 : d = 0 := hd.symm.trans h.source_depth
      refine ⟨.nil _, Walk.nil_isPath _ _, (by simp only [Walk.length_nil]; exact hd0.symm), ?_, ?_⟩
      · intro y hy
        have : y = N.source := by simpa using hy
        subst y; omega
      · intro k hk acc
        cases k with
        | zero => omega
        | succ k =>
          simp only [traceAux, ↓reduceIte, Walk.arcs_nil]
          rfl
    · obtain ⟨r, hp, hr, hh, ht, he⟩ := h.parent x hx hxs
      obtain ⟨p, hpath, hlen, hverts, htrace⟩ :=
        ih (σ.depth ((signedGraph N.graph).tail r)) (by omega)
          ((signedGraph N.graph).tail r) ht rfl
      let a : Arc (residual N f) ((signedGraph N.graph).tail r) x :=
        ⟨⟨r, hr⟩, rfl, hh⟩
      let q := p.append (.cons a (.nil x))
      have hqv : q.vertices = p.vertices ++ [x] := vertices_snoc p a
      have hn : x ∉ p.vertices := by
        intro hm
        have := hverts x hm
        omega
      refine ⟨q, ?_, ?_, ?_, ?_⟩
      · change q.vertices.Nodup
        rw [hqv]
        exact List.nodup_append.mpr ⟨hpath, by simp, by intro z hz w hw hzw; have hwx : w = x := List.mem_singleton.mp hw; subst w; subst z; exact hn hz⟩
      · simp only [q, Walk.length_append, Walk.length_cons, Walk.length_nil]
        omega
      · intro y hy
        rw [hqv, List.mem_append, List.mem_singleton] at hy
        rcases hy with hy | rfl
        · have := hverts y hy; omega
        · omega
      · intro k hk acc
        cases k with
        | zero => omega
        | succ k =>
          simp only [traceAux, hxs, ↓reduceIte, hp]
          rw [htrace k (by omega)]
          simp only [q, Walk.arcs_append, Walk.arcs_cons, Walk.arcs_nil]
          have hm : (p.arcs ++ [a.val]).map Subtype.val =
              p.arcs.map Subtype.val ++ [r] := by
            exact List.map_append (f := fun z : BoundedSpec.ResidualArc
              (fun _ => 0) N.capacity f => z.val) (l₁ := p.arcs) (l₂ := [a.val])
          exact (congrArg some (List.append_assoc (p.arcs.map Subtype.val) [r] acc)).symm.trans
            (congrArg (fun zs => some (zs ++ acc)) hm.symm)


/-- The explicit trace bound is safe for every pointer chain satisfying the
invariant: the constructed walk has distinct vertices. -/
theorem parent_trace (N : Network V A) (f : A → ℝ) (σ : State V A)
    (h : ParentInvariant N f σ) (x : V) (hx : σ.seen x = true) :
    ∃ p : Walk (residual N f) N.source x,
      p.IsPath ∧ p.length = σ.depth x ∧
      (BFSSpec.trace N.graph N.source x σ.pred).1 = some (p.arcs.map Subtype.val) := by
  obtain ⟨p, hp, hl, _, ht⟩ := parent_path N f σ h x hx
  have hc := List.Nodup.length_le_card hp
  change p.vertices.length ≤ Fintype.card V at hc
  rw [Walk.length_vertices, hl] at hc
  exact ⟨p, hp, hl, by simpa [BFSSpec.trace] using
    (ht (Fintype.card V + 1) (by omega) [])⟩

/-- Frontier and level information used only in the proof. An edge is either
already justified by the depth inequality, or still awaits its real scan. -/
structure SearchInvariant (N : Network V A) (f : A → ℝ)
    (rows : Rows V A) (σ : State V A) extends ParentInvariant N f σ : Prop where
  queued : ∀ y ∈ σ.queue.contents, σ.seen y = true
  sorted : σ.queue.contents.Pairwise (fun x y => σ.depth x ≤ σ.depth y)
  spread : ∀ x, σ.seen x = true → ∀ y ∈ σ.queue.contents,
    σ.depth x ≤ σ.depth y + 1
  active_info : ∀ x rs, σ.active = some (x, rs) →
    σ.seen x = true ∧ (∀ r ∈ rs, (signedGraph N.graph).tail r = x) ∧
    (∀ y, σ.seen y = true → σ.depth y ≤ σ.depth x + 1) ∧
    ∀ y ∈ σ.queue.contents, σ.depth x ≤ σ.depth y
  edges : ∀ r, 0 < BoundedSpec.capacity (fun _ => 0) N.capacity f r →
    σ.seen ((signedGraph N.graph).tail r) = true →
    (σ.seen ((signedGraph N.graph).head r) = true ∧
      σ.depth ((signedGraph N.graph).head r) ≤ σ.depth ((signedGraph N.graph).tail r) + 1) ∨
    (signedGraph N.graph).tail r ∈ σ.queue.contents ∨
    ∃ rs, σ.active = some ((signedGraph N.graph).tail r, rs) ∧ r ∈ rs

theorem initial_invariant (N : Network V A) (f : A → ℝ) (rows : Rows V A) :
    SearchInvariant N f rows (initial N.source) := by
  classical
  have seen : ∀ x, (initial (A := A) N.source).seen x = true ↔ x = N.source := by
    intro x
    by_cases hx : x = N.source <;> simp [initial, Function.update_apply, hx]
  refine {
    source_seen := ?_
    source_depth := rfl
    source_pred := rfl
    parent := ?_
    queued := ?_
    sorted := ?_
    spread := ?_
    active_info := ?_
    edges := ?_ }
  · exact (seen _).mpr rfl
  · intro x hx hxs
    exact (hxs ((seen x).mp hx)).elim
  · intro y hy
    have : y = N.source := by simpa [initial, Queue.contents] using hy
    exact (seen _).mpr this
  · simp [initial, Queue.contents]
  · intro x hx y hy
    simp [initial]
  · intro x rs ha
    simp [initial] at ha
  · intro r hr ht
    exact Or.inr (Or.inl (by simpa [initial, Queue.contents] using (seen _).mp ht))

/-- Reversing the physical queue leaves all proof observations unchanged. -/
theorem invariant_rotate (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (σ : State V A) (h : SearchInvariant N f rows σ) (hf : σ.queue.front = []) :
    SearchInvariant N f rows { σ with queue := ⟨σ.queue.rear.reverse, []⟩ } := by
  have hc := rotate_contents σ.queue hf
  exact { h with
    queued := by simpa only [hc] using h.queued
    sorted := by simpa only [hc] using h.sorted
    spread := by simpa only [hc] using h.spread
    active_info := by simpa only [hc] using h.active_info
    edges := by simpa only [hc] using h.edges }

/-- Clearing a fully scanned row discharges its empty set of pending labels. -/
theorem invariant_close (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (σ : State V A) (h : SearchInvariant N f rows σ) (x : V)
    (ha : σ.active = some (x, [])) :
    SearchInvariant N f rows { σ with active := none } := by
  refine { h with active_info := ?_, edges := ?_ }
  · intro y rs hy; cases hy
  · intro r hr ht
    rcases h.edges r hr ht with he | he | ⟨rs, hs, hm⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · have heq := Option.some.inj (ha.symm.trans hs)
      have : rs = [] := (Prod.mk.inj heq).2.symm
      simp [this] at hm

/-- Scanning removes precisely one pending label; all other pending labels
remain in the suffix. The scanned edge has already been justified. -/
theorem invariant_advance (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (σ : State V A) (h : SearchInvariant N f rows σ) (x : V) (r : Label A)
    (rs : List (Label A)) (ha : σ.active = some (x, r :: rs))
    (done : 0 < BoundedSpec.capacity (fun _ => 0) N.capacity f r →
      σ.seen ((signedGraph N.graph).head r) = true ∧
      σ.depth ((signedGraph N.graph).head r) ≤ σ.depth x + 1) :
    SearchInvariant N f rows { σ with active := some (x, rs) } := by
  refine { h with active_info := ?_, edges := ?_ }
  · intro y ys hy
    have heq := Option.some.inj hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    obtain ⟨hx, hrow, hd, hq⟩ := h.active_info x (r :: rs) ha
    exact ⟨hx, fun a hm => hrow a (List.mem_cons_of_mem _ hm), hd, hq⟩
  · intro a hp ht
    rcases h.edges a hp ht with he | he | ⟨ys, hs, hm⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · obtain ⟨hxt, hys⟩ := Prod.mk.inj (Option.some.inj (ha.symm.trans hs))
      subst ys
      rcases List.mem_cons.mp hm with hr | hm
      · subst a
        have hd := done hp
        exact Or.inl ⟨hd.1, by simpa only [← hxt] using hd.2⟩
      · exact Or.inr (Or.inr ⟨rs, by simp only [hxt], hm⟩)

/-- FIFO dequeue transfers the first queued vertex to its complete static row. -/
theorem invariant_dequeue (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (legal : LegalRows N.graph rows) (σ : State V A)
    (h : SearchInvariant N f rows σ) (x : V) (xs : List V)
    (ha : σ.active = none) (hf : σ.queue.front = x :: xs) :
    SearchInvariant N f rows
      { σ with queue := { σ.queue with front := xs }, active := some (x, rows x) } := by
  let qs := xs ++ σ.queue.rear.reverse
  have hc : σ.queue.contents = x :: qs := by simp [Queue.contents, hf, qs]
  have hx : σ.seen x = true := h.queued x (by simp [hc])
  have hsort := List.pairwise_cons.mp (hc ▸ h.sorted)
  refine { h with
    queued := ?_
    sorted := hsort.2
    spread := ?_
    active_info := ?_
    edges := ?_ }
  · intro y hy
    exact h.queued y (by rw [hc]; exact List.mem_cons_of_mem _ hy)
  · intro y hy z hz
    exact h.spread y hy z (by rw [hc]; exact List.mem_cons_of_mem _ hz)
  · intro y rs hy
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hy)
    exact ⟨hx, fun r hr => (legal.2 x r).mp hr,
      fun y hy => h.spread y hy x (by simp [hc]), hsort.1⟩
  · intro r hp ht
    rcases h.edges r hp ht with he | he | ⟨rs, hs, hm⟩
    · exact Or.inl he
    · rw [hc, List.mem_cons] at he
      rcases he with he | he
      · exact Or.inr (Or.inr ⟨rows x, by rw [he], (legal.2 x r).mpr he⟩)
      · exact Or.inr (Or.inl he)
    · simp [ha] at hs

/-- Proof notation for the three indexed stores and one rear-list cons of a
fresh discovery. This is the same update performed by `step`. -/
noncomputable def discovered (σ : State V A) (x y : V) (r : Label A) : State V A :=
  { σ with
    seen := Function.update σ.seen y true
    pred := Function.update σ.pred y (some r)
    depth := Function.update σ.depth y (σ.depth x + 1)
    queue := { σ.queue with rear := y :: σ.queue.rear } }

/-- Discovering a fresh head preserves pointers and FIFO levels. Its outgoing
edges become pending in the newly enqueued entry, without scanning them. -/
theorem invariant_discover (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (σ : State V A) (h : SearchInvariant N f rows σ)
    (x y : V) (rs : List (Label A)) (ha : σ.active = some (x, rs))
    (r : Label A) (hr : 0 < BoundedSpec.capacity (fun _ => 0) N.capacity f r)
    (ht : (signedGraph N.graph).tail r = x)
    (hh : (signedGraph N.graph).head r = y) (hy : σ.seen y = false) :
    SearchInvariant N f rows (discovered σ x y r) := by
  classical
  let τ := discovered σ x y r
  obtain ⟨hx, hrow, hupper, hlower⟩ := h.active_info x rs ha
  have old_ne : ∀ z, σ.seen z = true → z ≠ y := by
    intro z hz he; subst z; simp [hy] at hz
  have stable : ∀ z, σ.seen z = true →
      τ.seen z = true ∧ τ.depth z = σ.depth z ∧ τ.pred z = σ.pred z := by
    intro z hz
    simp only [τ, discovered, Function.update_of_ne (old_ne z hz)]
    exact ⟨hz, trivial, trivial⟩
  have fresh : τ.seen y = true ∧ τ.depth y = σ.depth x + 1 ∧ τ.pred y = some r := by
    simp [τ, discovered]
  have seen_cases : ∀ z, τ.seen z = true → z = y ∨ σ.seen z = true := by
    intro z hz
    by_cases he : z = y
    · exact Or.inl he
    · exact Or.inr (by simpa only [τ, discovered, Function.update_of_ne he] using hz)
  have hc : τ.queue.contents = σ.queue.contents ++ [y] := enqueue_contents σ.queue y
  have dx : τ.depth x = σ.depth x := (stable x hx).2.1
  change SearchInvariant N f rows τ
  refine {
    source_seen := (stable N.source h.source_seen).1
    source_depth := (stable N.source h.source_seen).2.1.trans h.source_depth
    source_pred := (stable N.source h.source_seen).2.2.trans h.source_pred
    parent := ?_
    queued := ?_
    sorted := ?_
    spread := ?_
    active_info := ?_
    edges := ?_ }
  · intro z hz hzs
    rcases seen_cases z hz with he | hz
    · subst z
      exact ⟨r, fresh.2.2, hr, hh, by simpa only [ht] using (stable x hx).1,
        by rw [ht, dx]; exact fresh.2.1⟩
    · obtain ⟨a, hp, hpos, hhead, htail, hd⟩ := h.parent z hz hzs
      exact ⟨a, (stable z hz).2.2.trans hp, hpos, hhead,
        (stable _ htail).1, by rw [(stable z hz).2.1, (stable _ htail).2.1]; exact hd⟩
  · intro z hz
    rw [hc, List.mem_append, List.mem_singleton] at hz
    rcases hz with hz | he
    · exact (stable z (h.queued z hz)).1
    · subst z; exact fresh.1
  · rw [hc, List.pairwise_append]
    refine ⟨?_, by simp, ?_⟩
    · apply h.sorted.imp_of_mem
      intro a b ha hb hab
      rw [(stable a (h.queued a ha)).2.1, (stable b (h.queued b hb)).2.1]
      exact hab
    · intro a ha b hb
      have : b = y := List.mem_singleton.mp hb
      subst b
      rw [(stable a (h.queued a ha)).2.1, fresh.2.1]
      exact hupper a (h.queued a ha)
  · intro a ha b hb
    rw [hc, List.mem_append, List.mem_singleton] at hb
    rcases seen_cases a ha with he | ha
    · subst a
      rw [fresh.2.1]
      rcases hb with hb | he
      · rw [(stable b (h.queued b hb)).2.1]
        have := hlower b hb; omega
      · subst b; rw [fresh.2.1]; omega
    · rw [(stable a ha).2.1]
      rcases hb with hb | he
      · rw [(stable b (h.queued b hb)).2.1]
        exact h.spread a ha b hb
      · subst b; rw [fresh.2.1]
        have := hupper a ha; omega
  · intro a as has
    have heq : (x, rs) = (a, as) := Option.some.inj (ha.symm.trans has)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    refine ⟨(stable x hx).1, hrow, ?_, ?_⟩
    · intro b hb
      rcases seen_cases b hb with he | hb
      · subst b; rw [fresh.2.1, dx]
      · rw [(stable b hb).2.1, dx]
        exact hupper b hb
    · intro b hb
      rw [hc, List.mem_append, List.mem_singleton] at hb
      rcases hb with hb | he
      · rw [dx, (stable b (h.queued b hb)).2.1]
        exact hlower b hb
      · subst b; rw [dx, fresh.2.1]; omega
  · intro a hp htail
    rcases seen_cases _ htail with he | htail
    · exact Or.inr (Or.inl (by rw [hc, he]; simp))
    · rcases h.edges a hp htail with ⟨hs, hd⟩ | hq | ⟨as, has, hm⟩
      · exact Or.inl ⟨(stable _ hs).1, by
          rw [(stable _ hs).2.1, (stable _ htail).2.1]; exact hd⟩
      · exact Or.inr (Or.inl (by rw [hc]; exact List.mem_append_left _ hq))
      · exact Or.inr (Or.inr ⟨as, has, hm⟩)

/-- The invariant follows every actual primitive transition, including row
closure, physical queue rotation, failed capacity tests and fresh discoveries. -/
theorem step_invariant (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (legal : LegalRows N.graph rows) (σ τ : State V A) (w : Work)
    (h : SearchInvariant N f rows σ) (hs : BFSSpec.step N f rows σ = some (τ, w)) :
    SearchInvariant N f rows τ := by
  classical
  cases ha : σ.active with
  | some a =>
    rcases a with ⟨x, rs⟩
    cases rs with
    | nil =>
      simp only [BFSSpec.step, ha, Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨rfl, rfl⟩
      exact invariant_close N f rows σ h x ha
    | cons r rs =>
      have hi := h.active_info x (r :: rs) ha
      have ht : (signedGraph N.graph).tail r = x := hi.2.1 r (by simp)
      simp only [BFSSpec.step, ha] at hs
      by_cases hp : 0 < BoundedSpec.capacity (fun _ => 0) N.capacity f r
      · simp only [hp, ↓reduceIte] at hs
        cases hy : σ.seen ((signedGraph N.graph).head r)
        · simp only [hy, Bool.false_eq_true, ↓reduceIte, Option.some.injEq,
            Prod.mk.injEq] at hs
          rcases hs with ⟨rfl, rfl⟩
          let y := (signedGraph N.graph).head r
          have hd := invariant_discover N f rows σ h x y (r :: rs) ha r hp ht rfl hy
          have hxy : x ≠ y := by
            intro he
            have hyy : σ.seen y = false := hy
            rw [← he, hi.1] at hyy
            cases hyy
          have hadv := invariant_advance N f rows (discovered σ x y r) hd x r rs
            (by exact ha) (by
              intro _
              change Function.update σ.seen y true y = true ∧
                Function.update σ.depth y (σ.depth x + 1) y ≤
                  Function.update σ.depth y (σ.depth x + 1) x + 1
              simp [Function.update_of_ne hxy])
          simpa only [discovered] using hadv
        · simp only [hy, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hs
          rcases hs with ⟨rfl, rfl⟩
          exact invariant_advance N f rows σ h x r rs ha
            (fun _ => ⟨hy, hi.2.2.1 _ hy⟩)
      · simp only [hp, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl⟩
        exact invariant_advance N f rows σ h x r rs ha (fun he => (hp he).elim)
  | none =>
    cases hf : σ.queue.front with
    | cons x xs =>
      simp only [BFSSpec.step, ha, hf, Option.some.injEq, Prod.mk.injEq] at hs
      rcases hs with ⟨rfl, rfl⟩
      exact invariant_dequeue N f rows legal σ h x xs ha hf
    | nil =>
      cases hb : σ.queue.rear with
      | nil => simp [BFSSpec.step, ha, hf, hb] at hs
      | cons y ys =>
        simp only [BFSSpec.step, ha, hf, hb, Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl⟩
        simpa only [hb, ha] using invariant_rotate N f rows σ h hf

theorem execute_invariant (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (legal : LegalRows N.graph rows) (k : ℕ) (σ : State V A)
    (h : SearchInvariant N f rows σ) :
    SearchInvariant N f rows (BFSSpec.execute N f rows k σ).1 := by
  induction k generalizing σ with
  | zero => exact h
  | succ k ih =>
    cases hs : BFSSpec.step N f rows σ with
    | none => simpa only [BFSSpec.execute, hs] using h
    | some tw =>
      rcases tw with ⟨τ, w⟩
      simpa only [BFSSpec.execute, hs] using
        ih τ (step_invariant N f rows legal σ τ w h hs)

/-- When the frontier is exhausted, every residual edge out of a seen vertex
has a seen head and satisfies the unit depth inequality. -/
theorem terminal_edge (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (σ : State V A) (h : SearchInvariant N f rows σ)
    (halt : BFSSpec.step N f rows σ = none)
    (r : BoundedSpec.ResidualArc (fun _ => 0) N.capacity f)
    (ht : σ.seen ((residual N f).tail r) = true) :
    σ.seen ((residual N f).head r) = true ∧
      σ.depth ((residual N f).head r) ≤ σ.depth ((residual N f).tail r) + 1 := by
  obtain ⟨ha, hf, hb⟩ := (step_eq_none_iff N f rows σ).mp halt
  rcases h.edges r.val r.property ht with he | he | ⟨rs, hs, hm⟩
  · exact he
  · simp [Queue.contents, hf, hb] at he
  · simp [ha] at hs

/-- The terminal depths bound every residual walk, with no assumption that the
walk is simple or that its labels are distinct. -/
theorem terminal_walk (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (σ : State V A) (h : SearchInvariant N f rows σ)
    (halt : BFSSpec.step N f rows σ = none) {x y : V}
    (p : Walk (residual N f) x y) (hx : σ.seen x = true) :
    σ.seen y = true ∧ σ.depth y ≤ σ.depth x + p.length := by
  induction p with
  | nil => exact ⟨hx, by simp⟩
  | @cons x z y a p ih =>
    have he := terminal_edge N f rows σ h halt a.val
      (by simpa only [a.property.1] using hx)
    rw [a.property.1, a.property.2] at he
    obtain ⟨hy, hd⟩ := ih he.1
    exact ⟨hy, by simp only [Walk.length_cons]; omega⟩

/-- Correctness is derived from the machine's transitions and real terminal
state. Feasibility is unnecessary for BFS itself, so this proves a stronger
version than the requested feasible-flow specialization. -/
theorem search_correct_all (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (legal : LegalRows N.graph rows) : Correct N f rows := by
  classical
  let σ := (BFSSpec.run N f rows).1
  have hinv : SearchInvariant N f rows σ :=
    execute_invariant N f rows legal (budget rows) (initial N.source)
      (initial_invariant N f rows)
  have halt : BFSSpec.step N f rows σ = none := (search_terminates N f rows).2
  have reach : ∀ x, σ.seen x = true ↔ Nonempty (Walk (residual N f) N.source x) := by
    intro x
    constructor
    · intro hx
      obtain ⟨p, _⟩ := parent_path N f σ hinv.toParentInvariant x hx
      exact ⟨p⟩
    · rintro ⟨p⟩
      exact (terminal_walk N f rows σ hinv halt p hinv.source_seen).1
  refine ⟨halt, reach, ?_⟩
  by_cases hs : σ.seen N.sink = true
  · obtain ⟨p, hp, hl, ht⟩ := parent_trace N f σ hinv.toParentInvariant N.sink hs
    have hout : (BFSSpec.search N f rows).1 = some (p.arcs.map Subtype.val) := by
      simp only [BFSSpec.search, show (BFSSpec.run N f rows).1.seen N.sink = true from hs,
        ↓reduceIte]
      exact ht
    rw [hout]
    refine ⟨p, rfl, hp, ?_, ht⟩
    intro q
    have hb := (terminal_walk N f rows σ hinv halt q hinv.source_seen).2
    rw [hinv.source_depth, zero_add, ← hl] at hb
    exact hb
  · have hout : (BFSSpec.search N f rows).1 = none := by
      simp only [BFSSpec.search, show ¬ (BFSSpec.run N f rows).1.seen N.sink = true from hs,
        Bool.false_eq_true, ↓reduceIte]
    rw [hout]
    exact fun he => hs ((reach N.sink).mpr he)

theorem search_correct : BFSSpec.search_correct.{u,v} := by
  intro V A _ _ N f _ rows legal
  exact search_correct_all N f rows legal

theorem typed_search_result : BFSSpec.typed_search_result.{u,v} := by
  intro V A _ _ N f hf rows legal
  have hc := (search_correct N f hf rows legal).2.2
  cases hout : (BFSSpec.search N f rows).1 with
  | none => exact Or.inl ⟨rfl, by simpa only [hout] using hc⟩
  | some rs =>
    obtain ⟨p, hp, hs, hshort, ht⟩ := (by simpa only [hout] using hc :
      ∃ p : Walk (residual N f) N.source N.sink,
        Represents N f rs p ∧ p.IsPath ∧ DistanceSpec.IsShortest p ∧
        (BFSSpec.trace N.graph N.source N.sink (BFSSpec.run N f rows).1.pred).1 = some rs)
    exact Or.inr ⟨rs, p, rfl, hp, hs, hshort, ht⟩

/-- Public implementation names are definitionally the independently specified
machine, interpreter, construction and tracer. -/
noncomputable def prepareRows := @BFSSpec.prepareRows
noncomputable def prepareFromArcs := @BFSSpec.prepareFromArcs
noncomputable def step := @BFSSpec.step
noncomputable def execute := @BFSSpec.execute
noncomputable def run := @BFSSpec.run
noncomputable def trace := @BFSSpec.trace
noncomputable def search := @BFSSpec.search

end P205.Networks.ResidualBFS
