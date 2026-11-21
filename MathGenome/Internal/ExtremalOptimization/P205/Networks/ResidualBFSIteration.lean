import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ResidualBFSIteration
import MathGenome.Internal.ExtremalOptimization.P205.Networks.ResidualFoundation
import MathGenome.Internal.ExtremalOptimization.P205.Networks.ResidualBFS

open scoped Classical BigOperators
universe u v
namespace P205.Networks.ResidualBFSIteration
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows
open BFSSpec IterationSpec
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- Sequential indexed stores implement the signed sum, including repeated labels. -/
theorem sparse_eq (d : ℝ) (rs : List (Label A)) (f : A → ℝ) :
    sparse d rs f = fun a => f a + BoundedSpec.adjustment d rs a := by
  classical
  induction rs generalizing f with
  | nil => funext a; simp [sparse, BoundedSpec.adjustment]
  | cons r rs ih =>
    rw [sparse, ih]
    funext a
    by_cases h : a = r.1
    · subst a
      cases hb : r.2 <;>
        simp [Function.update_self, BoundedSpec.adjustment, BoundedSpec.step,
          add_assoc, hb, sub_eq_add_neg]
    · simp [BoundedSpec.adjustment, BoundedSpec.step, h]

theorem minimumAux_le (c : Label A → ℝ) (d : ℝ) (rs : List (Label A)) :
    minimumAux c d rs ≤ d ∧ ∀ r ∈ rs, minimumAux c d rs ≤ c r := by
  induction rs generalizing d with
  | nil => simp [minimumAux]
  | cons r rs ih =>
    obtain ⟨h₁, h₂⟩ := ih (min d (c r))
    refine ⟨h₁.trans (min_le_left _ _), ?_⟩
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact h₁.trans (min_le_right _ _)
    · exact h₂ a ha

theorem minimumAux_attained (c : Label A → ℝ) (d : ℝ) (rs : List (Label A)) :
    minimumAux c d rs = d ∨ ∃ r ∈ rs, minimumAux c d rs = c r := by
  induction rs generalizing d with
  | nil => exact Or.inl rfl
  | cons r rs ih =>
    rcases ih (min d (c r)) with h | ⟨a, ha, h⟩
    · by_cases hc : d ≤ c r
      · exact Or.inl (h.trans (min_eq_left hc))
      · exact Or.inr ⟨r, List.mem_cons_self, h.trans (min_eq_right (le_of_not_ge hc))⟩
    · exact Or.inr ⟨a, List.mem_cons_of_mem r ha, h⟩

theorem minimum_spec (c : Label A → ℝ) (rs : List (Label A)) (hne : rs ≠ []) :
    ∃ d, minimum c rs = some d ∧ (∀ r ∈ rs, d ≤ c r) ∧ ∃ r ∈ rs, d = c r := by
  cases rs with
  | nil => exact (hne rfl).elim
  | cons r rs =>
    refine ⟨minimumAux c (c r) rs, rfl, ?_, ?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · subst a
        exact (minimumAux_le c (c r) rs).1
      · exact (minimumAux_le c (c r) rs).2 a ha
    · rcases minimumAux_attained c (c r) rs with h | ⟨a, ha, h⟩
      · exact ⟨r, List.mem_cons_self, h⟩
      · exact ⟨a, List.mem_cons_of_mem r ha, h⟩

theorem minimum_bottleneck (N : Network V A) (f : A → ℝ) {x y : V}
    (p : Walk (residual N f) x y) (rs : List (Label A))
    (hr : Represents N f rs p) (hne : rs ≠ []) :
    ∃ d, minimum (BoundedSpec.capacity (fun _ => 0) N.capacity f) rs = some d ∧
      BoundedSpec.Bottleneck N.graph (fun _ => 0) N.capacity f p d := by
  obtain ⟨d, hd, hl, r, hm, he⟩ := minimum_spec
    (BoundedSpec.capacity (fun _ => 0) N.capacity f) rs hne
  obtain ⟨a, ha, har⟩ := List.mem_map.mp (hr ▸ hm)
  refine ⟨d, hd, ?_, ?_, a, ha, he.trans (congrArg _ har).symm⟩
  · rw [he, ← har]
    exact a.property
  · intro a ha
    exact hl a.val (hr ▸ List.mem_map.mpr ⟨a, ha, rfl⟩)

@[simp] theorem minimumAuxWork_operations (rs : List (Label A)) :
    (minimumAuxWork rs).operations = 10 * rs.length + 2 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [minimumAuxWork, Work.plus, Work.events, ih]; omega

@[simp] theorem minimumAuxWork_inspections (rs : List (Label A)) :
    (minimumAuxWork rs).inspections = rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [minimumAuxWork, Work.plus, Work.events, ih]; omega

@[simp] theorem sparseWork_operations (rs : List (Label A)) :
    (sparseWork rs).operations = 7 * rs.length + 2 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [sparseWork, Work.plus, Work.events, ih]; omega

@[simp] theorem sparseWork_inspections (rs : List (Label A)) :
    (sparseWork rs).inspections = 0 := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [sparseWork, Work.plus, Work.events, ih]

theorem minimumWork_bound (rs : List (Label A)) :
    (minimumWork rs).operations ≤ 10 * rs.length + 2 ∧
    (minimumWork rs).inspections = rs.length := by
  cases rs <;> simp [minimumWork, Work.events, Work.plus] <;> omega

/-- Rear cells carry one extra resource unit, paying for their eventual reversal. -/
theorem reverse_potential (rs : List V) (rows : Rows V A) :
    (rs.reverse.map (fun x => (rows x).length + 3)).sum + rs.length =
      (rs.map (fun x => (rows x).length + 4)).sum := by
  rw [List.map_reverse, List.sum_reverse]
  induction rs with
  | nil => rfl
  | cons r rs ih => simp only [List.map_cons, List.sum_cons, List.length_cons]; omega

/-- A weighted one-step bound directly from the operational rules. -/
theorem step_work_bound (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (σ τ : State V A) (w : Work) (h : BFSSpec.step N f rows σ = some (τ, w)) :
    w.operations + 30 * potential rows τ ≤ 30 * potential rows σ ∧
      w.inspections ≤ w.operations := by
  classical
  rcases σ with ⟨seen, pred, depth, ⟨front, rear⟩, active⟩
  cases active with
  | some a =>
    rcases a with ⟨x, rs⟩
    cases rs with
    | nil =>
      simp only [BFSSpec.step] at h
      cases h
      simp [potential, transitionWork, Work.plus, Work.events]
      omega
    | cons r rs =>
      by_cases hp : 0 < BoundedSpec.capacity (fun _ => 0) N.capacity f r
      · cases hs : seen ((signedGraph N.graph).head r) with
        | true =>
          simp only [BFSSpec.step, hp, ↓reduceIte, hs] at h
          cases h
          simp [potential, transitionWork, scanWork, Work.events, Work.plus]
          omega
        | false =>
          simp only [BFSSpec.step, hp, ↓reduceIte, hs, Bool.false_eq_true] at h
          cases h
          have hu := ResidualBFS.unseen_sum_update rows seen ((signedGraph N.graph).head r) hs
          simp [potential, transitionWork, scanWork, Work.events, Work.plus]
          omega
      · simp only [BFSSpec.step, hp, ↓reduceIte] at h
        cases h
        simp [potential, transitionWork, scanWork, Work.events, Work.plus]
        omega
  | none =>
    cases front with
    | cons x xs =>
      simp only [BFSSpec.step] at h
      cases h
      simp [potential, transitionWork, Work.plus, Work.events]
      omega
    | nil =>
      cases rear with
      | nil => simp [BFSSpec.step] at h
      | cons y ys =>
        simp only [BFSSpec.step] at h
        cases h
        have hr := reverse_potential (y :: ys) rows
        simp only [List.length_cons] at hr
        simp only [potential, List.map_nil, List.sum_nil, Nat.zero_add, add_zero]
        simp only [transitionWork, Work.plus, Work.events, List.length_cons, List.length_nil,
          ResidualBFS.reverse_work_operations, ResidualBFS.reverse_work_inspections]
        constructor
        · omega
        · simp

/-- Work telescopes along any operational execution, without an assumed
correctness invariant and without requiring the execution to have halted. -/
theorem execution_potential (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    {σ τ : State V A} {w : Work} (h : Execution N f rows σ τ w) :
    w.operations + 30 * potential rows τ ≤ 30 * potential rows σ ∧
      w.inspections ≤ w.operations := by
  induction h with
  | refl => simp
  | @next σ τ υ w z hstep hex ih =>
    obtain ⟨h₁, h₂⟩ := step_work_bound N f rows σ τ w hstep
    simp only [Work.plus]
    constructor <;> omega

theorem legal_rows_total (G : Digraph V A) (rows : Rows V A) (h : LegalRows G rows) :
    (∑ x, (rows x).length) = 2 * Fintype.card A := by
  classical
  have hf (x : V) : (rows x).length =
      ((Finset.univ : Finset (Label A)).filter (fun r => (signedGraph G).tail r = x)).card := by
    rw [← List.toFinset_card_of_nodup (h.1 x)]
    congr 1
    ext r
    simp [h.2 x r]
  simp_rw [hf]
  have hh := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Label A)) (Finset.univ : Finset V) (signedGraph G).tail
  simpa [Label, Fintype.card_prod, Nat.mul_comm] using hh

theorem initial_potential (rows : Rows V A) (s : V) :
    potential rows (initial s) + 1 = (∑ x, (rows x).length) + 4 * Fintype.card V := by
  classical
  have hu := ResidualBFS.unseen_sum_update rows (fun _ => false) s rfl
  simp only [Bool.false_eq_true, ↓reduceIte, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, smul_eq_mul] at hu
  dsimp [potential, initial]
  simpa only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, Nat.add_assoc, Nat.mul_comm, show 3 + 1 = 4 from rfl] using hu

theorem execution_bound (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (hl : LegalRows N.graph rows) (σ : State V A) (w : Work)
    (he : Execution N f rows (initial N.source) σ w) :
    w.operations ≤ 120 * Fintype.card V + 60 * Fintype.card A ∧
      w.inspections ≤ w.operations := by
  have h := execution_potential N f rows he
  have hp := initial_potential rows N.source
  rw [legal_rows_total N.graph rows hl] at hp
  constructor <;> omega

@[simp] theorem rowsInitWork_operations (vs : List V) :
    (rowsInitWork vs).operations = 5 * vs.length + 1 := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [rowsInitWork, Work.plus, Work.events, ih]; omega

@[simp] theorem rowsInitWork_inspections (vs : List V) :
    (rowsInitWork vs).inspections = 0 := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [rowsInitWork, Work.plus, Work.events, ih]

@[simp] theorem signedLabels_length (as : List A) :
    (signedLabels as).length = 2 * as.length := by
  induction as with
  | nil => rfl
  | cons x xs ih => simp [signedLabels, ih]; omega

@[simp] theorem signedLabelsWork_operations (as : List A) :
    (signedLabelsWork as).operations = 7 * as.length + 1 := by
  induction as with
  | nil => rfl
  | cons x xs ih => simp [signedLabelsWork, Work.plus, Work.events, ih]; omega

@[simp] theorem signedLabelsWork_inspections (as : List A) :
    (signedLabelsWork as).inspections = 0 := by
  induction as with
  | nil => rfl
  | cons x xs ih => simp [signedLabelsWork, Work.plus, Work.events, ih]

theorem enumeration_length {α : Type*} [Fintype α] (xs : List α) (he : Enumeration xs) :
    xs.length = Fintype.card α := by
  classical
  rw [← List.toFinset_card_of_nodup he.1]
  have hh : xs.toFinset = Finset.univ := by ext x; simp [he.2 x]
  rw [hh, Finset.card_univ]

@[simp] theorem initializeWork_operations (vs : List V) :
    (initializeWork vs).operations = 9 * vs.length + 7 := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [initializeWork, Work.plus, Work.events, ih]; omega

@[simp] theorem initializeWork_inspections (vs : List V) :
    (initializeWork vs).inspections = 0 := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [initializeWork, Work.plus, Work.events, ih]

@[simp] theorem lengthWork_operations (xs : List α) :
    (lengthWork xs).operations = 4 * xs.length + 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [lengthWork, Work.plus, Work.events, ih]; omega

@[simp] theorem lengthWork_inspections (xs : List α) :
    (lengthWork xs).inspections = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [lengthWork, Work.plus, Work.events, ih]

@[simp] theorem budgetWork_operations (rows : Rows V A) (vs : List V) :
    (budgetWork rows vs).operations =
      7 * vs.length + 4 * (vs.map (fun x => (rows x).length)).sum + 1 := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [budgetWork, Work.plus, Work.events, ih]; omega

@[simp] theorem budgetWork_inspections (rows : Rows V A) (vs : List V) :
    (budgetWork rows vs).inspections = 0 := by
  induction vs with
  | nil => rfl
  | cons x xs ih => simp [budgetWork, Work.plus, Work.events, ih]

theorem traceAux_bound (G : Digraph V A) (s : V) (pred : V → Option (Label A))
    (k : ℕ) (x : V) (acc : List (Label A)) :
    (traceAux G s pred k x acc).2.operations ≤ 11 * k + 6 ∧
    (traceAux G s pred k x acc).2.inspections = 0 := by
  classical
  induction k generalizing x acc with
  | zero => simp [traceAux, Work.events]
  | succ k ih =>
    by_cases hx : x = s
    · simp [traceAux, hx, Work.events]
    · cases hp : pred x with
      | none => simp [traceAux, hx, hp, Work.events]
      | some r =>
        have hh := ih ((signedGraph G).tail r) (r :: acc)
        simp [traceAux, hx, hp, Work.plus, Work.events]
        constructor <;> omega

theorem trace_bound (G : Digraph V A) (s t : V) (pred : V → Option (Label A)) :
    (trace G s t pred).2.operations ≤ 11 * Fintype.card V + 18 ∧
    (trace G s t pred).2.inspections = 0 := by
  have h := traceAux_bound G s pred (Fintype.card V + 1) t []
  simp only [trace, Work.plus, Work.events, List.length_cons, List.length_nil]
  constructor <;> simp_all <;> omega

/-- Full search accounting from an actual execution of the bounded interpreter. -/
theorem search_bound (ht : BFSSpec.search_terminates.{u,v})
    (N : Network V A) (f : A → ℝ) (rows : Rows V A) (hl : LegalRows N.graph rows) :
    (search N f rows).2.operations ≤ 200 * (Fintype.card V + Fintype.card A) ∧
      (search N f rows).2.inspections ≤ 200 * (Fintype.card V + Fintype.card A) := by
  classical
  have he := execution_bound N f rows hl (run N f rows).1 (run N f rows).2
    (ht N f rows).1
  have htr := trace_bound N.graph N.source N.sink (run N f rows).1.pred
  have hsum : (((Finset.univ : Finset V).toList).map
      (fun x => (rows x).length)).sum = 2 * Fintype.card A := by
    rw [Finset.sum_map_toList]
    exact legal_rows_total N.graph rows hl
  have hv : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.source⟩
  unfold search
  dsimp only
  split_ifs
  all_goals
    simp only [Work.plus, runWork, haltWork, Work.events,
      initializeWork_operations, initializeWork_inspections, budgetWork_operations,
      budgetWork_inspections, hsum, Finset.length_toList, Finset.card_univ]
    constructor <;> simp_all <;> omega

theorem walk_labels_nonempty {G : Digraph V A} {x y : V} (h : x ≠ y)
    (p : Walk G x y) : p.arcs ≠ [] := by
  cases p with
  | nil => exact (h rfl).elim
  | cons a p => simp

theorem represented_path_length (N : Network V A) (f : A → ℝ)
    (rs : List (Label A)) (p : Walk (residual N f) N.source N.sink)
    (hr : Represents N f rs p) (hp : p.IsPath) : rs.length < Fintype.card V := by
  have hn := List.Nodup.length_le_card hp
  change p.vertices.length ≤ Fintype.card V at hn
  rw [Walk.length_vertices] at hn
  have he : p.length = rs.length := by
    exact (List.length_map (as := p.arcs)
      (fun r : BoundedSpec.ResidualArc (fun _ => 0) N.capacity f => r.val)).symm.trans
        (congrArg List.length hr)
  omega

theorem updated_feasible (N : Network V A) (f : A → ℝ) (hf : N.Feasible f)
    (p : Walk (residual N f) N.source N.sink) (hp : p.IsPath) (d : ℝ)
    (hd : BoundedSpec.Bottleneck N.graph (fun _ => 0) N.capacity f p d) :
    N.Feasible (BoundedSpec.augment N.graph (fun _ => 0) N.capacity f p d) := by
  obtain ⟨hb, hv⟩ := P205.Networks.augment_path N.graph (fun _ => 0) N.capacity f p hp
    hf.1 d d hd hd.1.le le_rfl
  refine ⟨hb, ?_⟩
  intro z hs ht
  change N.graph.divergence (BoundedSpec.augment N.graph (fun _ => 0) N.capacity f p d) z = 0
  rw [hv]
  have hz : N.graph.divergence f z = 0 := hf.2 z hs ht
  simp [hz, Ne.symm hs, Ne.symm ht]

/-- The semantic refinement uses only the supplied full typed-search premise.
The amount and updated flow still come from the two actual list passes. -/
theorem iteration_refinement (hc : BFSSpec.typed_search_result.{u,v})
    (N : Network V A) (f : A → ℝ) (hf : N.Feasible f)
    (rows : Rows V A) (hl : LegalRows N.graph rows) : IterationSpec.Correct N f rows := by
  classical
  rcases hc N f hf rows hl with ⟨hs, hn⟩ | ⟨rs, p, hs, hr, hp, hshort, htrace⟩
  · simpa [IterationSpec.Correct, iteration, hs] using hn
  · have hne : rs ≠ [] := by
      intro he
      have hh : p.arcs = [] := List.map_eq_nil_iff.mp (hr.trans he)
      exact walk_labels_nonempty N.source_ne_sink p hh
    obtain ⟨d, hd, hb⟩ := minimum_bottleneck N f p rs hr hne
    have he : sparse d rs f = BoundedSpec.augment N.graph (fun _ => 0) N.capacity f p d := by
      rw [sparse_eq, ← hr]
      rfl
    simp only [IterationSpec.Correct, iteration, hs, hd]
    exact ⟨p, trivial, hr, hp, hshort, htrace, hb, he,
      he ▸ updated_feasible N f hf p hp d hb⟩

theorem full_iteration_bound (ht : BFSSpec.search_terminates.{u,v})
    (hc : BFSSpec.typed_search_result.{u,v})
    (N : Network V A) (f : A → ℝ) (hf : N.Feasible f)
    (rows : Rows V A) (hl : LegalRows N.graph rows) :
    (iteration N f rows).2.operations ≤ 300 * (Fintype.card V + Fintype.card A) ∧
    (iteration N f rows).2.inspections ≤ 300 * (Fintype.card V + Fintype.card A) := by
  classical
  have hb := search_bound ht N f rows hl
  have hv : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.source⟩
  rcases hc N f hf rows hl with ⟨hs, hn⟩ | ⟨rs, p, hs, hr, hp, hshort, htrace⟩
  · simp [iteration, hs, Work.plus, Work.events]
    constructor <;> omega
  · have hlen := represented_path_length N f rs p hr hp
    have hm := minimumWork_bound rs
    unfold iteration
    dsimp only
    rw [hs]
    dsimp only
    split
    all_goals
      simp only [Work.plus, Work.events, sparseWork_operations, sparseWork_inspections]
      constructor <;> simp_all <;> omega

/-- Uniform bound for every finite primitive execution, including prefixes. -/
theorem execution_linear : IterationSpec.execution_linear.{u,v} := by
  intro V A _ _ N f rows hl σ w he
  obtain ⟨hops, hins⟩ := execution_bound N f rows hl σ w he
  constructor <;> omega

/-- Construction uses one pass over vertices and one over original arcs. -/
theorem setup_linear : IterationSpec.setup_linear.{u,v} := by
  intro V A _ _ N vs as hv ha
  have hvs := enumeration_length vs hv
  have has := enumeration_length as ha
  have hn : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨N.source⟩
  refine ⟨ResidualBFS.prepare_from_arcs_correct N.graph as ha, ?_⟩
  simp [prepareFromArcsWork, prepareWork, Work.plus, hvs, has]
  omega

theorem search_linear : IterationSpec.search_linear.{u,v} := by
  intro V A _ _ N f rows hl
  exact search_bound ResidualBFS.search_terminates N f rows hl

theorem iteration_correct_and_linear : IterationSpec.iteration_correct_and_linear.{u,v} := by
  intro V A _ _ N f hf rows hl
  exact ⟨iteration_refinement ResidualBFS.typed_search_result N f hf rows hl,
    full_iteration_bound ResidualBFS.search_terminates ResidualBFS.typed_search_result N f hf rows hl⟩

end P205.Networks.ResidualBFSIteration
