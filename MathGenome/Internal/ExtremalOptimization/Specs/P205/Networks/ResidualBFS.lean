import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ShortestPathDistances
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.Nodup

/-!
An independent RAM operational specification for W37 (paper.tex 1730–1772).

The finite tables below are indexed RAM arrays, represented extensionally by
functions on the finite vertex type. An indexing `V ≃ Fin (card V)` realizes
these tables as consecutive RAM cells. A table update is a RAM store; it is
not an implementation by chains of functional closures. Array initialization
is charged once per cell. Labels and vertex indices occupy single RAM cells;
real subtraction and comparison are exact unit operations. Vertex/arc indices,
their enumerations and cardinalities belong to the indexed graph input.
State pointers and the active vertex are held in registers between transitions.

Only the transition function performs the search. No shortest-path, reachability
or correctness certificate is stored in a state. The two queue lists share tails;
enqueue conses onto the rear list. Reversal traverses and copies every rear cell
and is explicitly charged. `contents` is a ghost observation, never evaluated by
search. Likewise costs and execution histories are ghost instrumentation, not
lists constructed by the RAM program. There is no path copying during search.

Every legal ordering of each static adjacency row is allowed. FIFO order then
resolves the usual BFS ties. Search exhausts the queue even if the sink was
already discovered, so one execution also computes the complete reachable set.
-/
open scoped Classical BigOperators
universe u v
namespace P205.Networks.BFSSpec
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

abbrev Label (A : Type v) := A × Bool

def signedGraph (G : Digraph V A) : Digraph V (Label A) where
  tail r := if r.2 then G.tail r.1 else G.head r.1
  head r := if r.2 then G.head r.1 else G.tail r.1

abbrev residual (N : Network V A) (f : A → ℝ) :=
  BoundedSpec.graph N.graph (fun _ => 0) N.capacity f

abbrev Rows (V : Type u) (A : Type v) := V → List (Label A)

/-- Each signed label occurs exactly once, in its own tail's row. -/
def LegalRows (G : Digraph V A) (rows : Rows V A) : Prop :=
  (∀ x, (rows x).Nodup) ∧
  ∀ x r, r ∈ rows x ↔ (signedGraph G).tail r = x

/-- Enumeration choices also describe arbitrary orders for preprocessing. -/
def Enumeration {α : Type*} (xs : List α) : Prop := xs.Nodup ∧ ∀ x, x ∈ xs

/-- These are unit RAM events. `inspect` counts one residual-copy inspection
in addition to its unit elementary operation. No bulk list operation is a unit
event. Allocation counts one cell; table initialization writes every cell. -/
inductive Primitive where
  | read | write | allocate | listTest | listRead | cons
  | endpoint | subtract | compare | branch | increment | inspect
  deriving DecidableEq, Repr

structure Work where
  operations : ℕ := 0
  inspections : ℕ := 0
  deriving DecidableEq, Repr

def Work.plus (a b : Work) : Work :=
  ⟨a.operations + b.operations, a.inspections + b.inspections⟩

def Work.events (es : List Primitive) : Work :=
  ⟨es.length, (es.filter (· == Primitive.inspect)).length⟩

/-- A reversal has one list-empty test at exit and, per cell, a list read,
cons allocation/write, and the recursive branch. -/
def reverseWork : List α → Work
  | [] => Work.events [.listTest]
  | _ :: xs => (Work.events [.listTest, .listRead, .allocate, .cons, .branch]).plus
      (reverseWork xs)

/-- One adjacency-array initialization per vertex; no filtering over labels. -/
def rowsInitWork : List V → Work
  | [] => Work.events [.listTest]
  | _ :: xs => (Work.events [.listTest, .listRead, .allocate, .write, .branch]).plus
      (rowsInitWork xs)

/-- Build adjacency lists by one pass over signed labels. Endpoint access,
indexed row read/write, and cons are recorded for each copy. -/
noncomputable def buildRows (G : Digraph V A) : List (Label A) → Rows V A → Rows V A
  | [], rows => rows
  | r :: rs, rows => buildRows G rs
      (Function.update rows ((signedGraph G).tail r) (r :: rows ((signedGraph G).tail r)))

def buildWork : List (Label A) → Work
  | [] => Work.events [.listTest]
  | _ :: rs => (Work.events [.listTest, .listRead, .branch, .endpoint, .read,
      .allocate, .cons, .write, .branch]).plus (buildWork rs)

noncomputable def prepareRows (G : Digraph V A) (rs : List (Label A)) : Rows V A :=
  buildRows G rs (fun _ => [])

def prepareWork (vs : List V) (rs : List (Label A)) : Work :=
  (rowsInitWork vs).plus (buildWork rs)

/-- Generate both signed copies in a single pass over the original arc
array's enumeration. The input enumeration itself is part of the indexed graph
representation, not an oracle for adjacency or reachability. -/
def signedLabels : List A → List (Label A)
  | [] => []
  | a :: as => (a, true) :: (a, false) :: signedLabels as

def signedLabelsWork : List A → Work
  | [] => Work.events [.listTest]
  | _ :: as => (Work.events [.listTest, .listRead, .allocate, .cons,
      .allocate, .cons, .branch]).plus (signedLabelsWork as)

noncomputable def prepareFromArcs (G : Digraph V A) (as : List A) : Rows V A :=
  prepareRows G (signedLabels as)

def prepareFromArcsWork (vs : List V) (as : List A) : Work :=
  (signedLabelsWork as).plus (prepareWork vs (signedLabels as))

structure Queue (V : Type u) where
  front : List V := []
  rear : List V := []

/-- Ghost FIFO observation; not a search primitive. -/
def Queue.contents (q : Queue V) : List V := q.front ++ q.rear.reverse

structure State (V : Type u) (A : Type v) where
  seen : V → Bool
  pred : V → Option (Label A)
  depth : V → ℕ
  queue : Queue V
  active : Option (V × List (Label A))

noncomputable def initial (s : V) : State V A where
  seen := Function.update (fun _ => false) s true
  pred := fun _ => none
  depth := fun _ => 0
  queue := ⟨[s], []⟩
  active := none

/-- Three arrays are allocated and initialized, one cell at a time. At exit,
mark the source, construct its queue cell, and initialize front/rear/active. -/
def initializeWork : List V → Work
  | [] => Work.events [.listTest, .write, .allocate, .cons, .write, .write, .write]
  | _ :: vs => (Work.events [.listTest, .listRead,
      .allocate, .write, .allocate, .write, .allocate, .write, .branch]).plus
      (initializeWork vs)

/-- Scanning a copy selects its sign, fetches its capacity data, subtracts and
tests positivity. A target visited-cell is read only for a positive copy.
Signed endpoint access selects the appropriate original endpoint array first. -/
def scanWork (positive fresh : Bool) : Work :=
  (Work.events [.listTest, .listRead, .inspect, .branch, .read, .read,
    .subtract, .compare, .branch, .write]).plus
  (if positive then
    (Work.events [.branch, .endpoint, .read, .branch]).plus
    (if fresh then Work.events [.write, .write, .read, .increment, .write,
      .allocate, .cons, .write] else ⟨0, 0⟩)
   else ⟨0, 0⟩)

/-- Common control events for a successful interpreter transition: test fuel,
take its nonzero branch, decrement it, dispatch the transition result, and
dispatch the active-row option. Including them here leaves `execute` as a
simple sum of the actual transition costs. A fuel-exhausted prefix is only a
proof observation; the genuine run is proved to stop with positive fuel. -/
def transitionWork (w : Work) : Work :=
  (Work.events [.compare, .branch, .subtract, .branch, .branch]).plus w

/-- One machine transition. A row is scanned one label at a time. `none`
is returned exactly for an empty queue with no active row. -/
noncomputable def step (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (σ : State V A) : Option (State V A × Work) :=
  match σ.active with
  | some (x, r :: rs) =>
    let next := { σ with active := some (x, rs) }
    if 0 < BoundedSpec.capacity (fun _ => 0) N.capacity f r then
      let y := (signedGraph N.graph).head r
      if σ.seen y then some (next, transitionWork (scanWork true false))
      else some ({ next with
        seen := Function.update σ.seen y true
        pred := Function.update σ.pred y (some r)
        depth := Function.update σ.depth y (σ.depth x + 1)
        queue := { σ.queue with rear := y :: σ.queue.rear } }, transitionWork (scanWork true true))
    else some (next, transitionWork (scanWork false false))
  | some (_, []) =>
    some ({ σ with active := none }, transitionWork (Work.events [.listTest, .write, .branch]))
  | none =>
    match σ.queue.front with
    | x :: xs =>
      some ({ σ with queue := { σ.queue with front := xs }, active := some (x, rows x) },
        transitionWork (Work.events [.listTest, .listRead, .write, .read, .write, .branch]))
    | [] =>
      match σ.queue.rear with
      | [] => none
      | _ :: _ =>
        some ({ σ with queue := ⟨σ.queue.rear.reverse, []⟩ },
          transitionWork ((Work.events [.listTest, .listTest, .write, .write, .branch]).plus
            (reverseWork σ.queue.rear)))

/-- Independent finite operational execution, with exact summed primitive
work. The halt test is charged separately by `runWork`. -/
inductive Execution (N : Network V A) (f : A → ℝ) (rows : Rows V A) :
    State V A → State V A → Work → Prop where
  | refl (σ) : Execution N f rows σ σ ⟨0, 0⟩
  | next {σ τ υ : State V A} {w z : Work} :
      step N f rows σ = some (τ, w) → Execution N f rows τ υ z →
      Execution N f rows σ υ (w.plus z)

/-- Final positive-fuel test, active-option dispatch, empty-front/empty-rear
tests and halted-result dispatch. No decrement is needed on this return. -/
def haltWork : Work := Work.events [.compare, .branch, .branch, .listTest, .listTest, .branch]
def runWork (w : Work) : Work := w.plus haltWork

/-- A decreasing resource potential. This is ghost data and never computed
by a RAM transition. It will also give a finite recursion budget. -/
def potential (rows : Rows V A) (σ : State V A) : ℕ :=
  (∑ x, if σ.seen x then 0 else (rows x).length + 4) +
  ((σ.queue.front.map (fun x => (rows x).length + 3)).sum +
   (σ.queue.rear.map (fun x => (rows x).length + 4)).sum) +
  (match σ.active with | none => 0 | some (_, rs) => rs.length + 1)

/-- A bounded interpreter. The terminality theorem below, rather than the
fuel cutoff itself, certifies that no running transition has been discarded. -/
noncomputable def execute (N : Network V A) (f : A → ℝ) (rows : Rows V A) :
    ℕ → State V A → State V A × Work
  | 0, σ => (σ, ⟨0, 0⟩)
  | k + 1, σ => match step N f rows σ with
    | none => (σ, ⟨0, 0⟩)
    | some (τ, w) => let out := execute N f rows k τ
                     (out.1, w.plus out.2)

/-- The interpreter budget is computed by actually counting row cells.
This extra linear pass is exposed and charged; it is not a hidden evaluation
of the proof's potential or an uncharged full-arc filtering operation. -/
def lengthWork : List α → Work
  | [] => Work.events [.listTest]
  | _ :: xs => (Work.events [.listTest, .listRead, .increment, .branch]).plus
      (lengthWork xs)

def budgetRows (rows : Rows V A) : List V → ℕ
  | [] => 0
  | x :: xs => (rows x).length + 4 + budgetRows rows xs

def budgetWork (rows : Rows V A) : List V → Work
  | [] => Work.events [.listTest]
  | x :: xs => (Work.events [.listTest, .listRead, .read, .increment, .increment, .branch]).plus
      ((lengthWork (rows x)).plus (budgetWork rows xs))

noncomputable def budget (rows : Rows V A) : ℕ :=
  budgetRows rows ((Finset.univ : Finset V).toList)

noncomputable def run (N : Network V A) (f : A → ℝ) (rows : Rows V A) :=
  execute N f rows (budget rows) (initial N.source)

/-- Predecessor tracing reads one pointer per vertex. Labels are consed onto
an accumulator while moving backward; there is no queue append or path copy.
The safety of the explicit bound for the returned path is part of the
correctness obligation below, not an assumption supplied to the program. Failure is represented by `none`. -/
noncomputable def traceAux (G : Digraph V A) (s : V) (pred : V → Option (Label A)) :
    ℕ → V → List (Label A) → Option (List (Label A)) × Work
  | 0, _, _ => (none, Work.events [.compare, .branch])
  | k + 1, x, acc =>
    if x = s then (some acc, Work.events [.compare, .branch, .compare, .branch])
    else match pred x with
      | none => (none, Work.events [.compare, .branch, .compare, .branch, .read, .branch])
      | some r =>
        let out := traceAux G s pred k ((signedGraph G).tail r) (r :: acc)
        (out.1, (Work.events [.compare, .branch, .compare, .branch, .read, .branch,
          .subtract, .branch, .endpoint, .allocate, .cons]).plus out.2)

noncomputable def trace (G : Digraph V A) (s t : V) (pred : V → Option (Label A)) :=
  let out := traceAux G s pred (Fintype.card V + 1) t []
  (out.1, (Work.events [.increment]).plus out.2)

/-- A proof-only decoding relation. It reconstructs the canonical endpoint-
indexed residual Walk without a second RAM pass over the output. -/
def Represents (N : Network V A) (f : A → ℝ) {s t : V}
    (rs : List (Label A)) (p : Walk (residual N f) s t) : Prop :=
  p.arcs.map Subtype.val = rs

/-- Search/tracing output before its proof-only conversion to a typed Walk.
The raw trace is retained for the downstream sparse-update procedure. -/
noncomputable def search (N : Network V A) (f : A → ℝ) (rows : Rows V A) :
    Option (List (Label A)) × Work :=
  let out := run N f rows
  let init := initializeWork ((Finset.univ : Finset V).toList)
  if out.1.seen N.sink then
    let tr := trace N.graph N.source N.sink out.1.pred
    (tr.1, init.plus ((budgetWork rows ((Finset.univ : Finset V).toList)).plus ((runWork out.2).plus
      ((Work.events [.read, .branch]).plus tr.2))))
  else (none, init.plus ((budgetWork rows ((Finset.univ : Finset V).toList)).plus ((runWork out.2).plus (Work.events [.read, .branch]))))

/-- Full required outcome, including that the actual predecessor trace was
followed. This is a proposition to prove, never a field supplied to the search. -/
def Correct (N : Network V A) (f : A → ℝ) (rows : Rows V A) : Prop :=
  let out := run N f rows
  step N f rows out.1 = none ∧
  (∀ x, out.1.seen x = true ↔ Nonempty (Walk (residual N f) N.source x)) ∧
  match (search N f rows).1 with
  | none => ¬ Nonempty (Walk (residual N f) N.source N.sink)
  | some rs => ∃ p : Walk (residual N f) N.source N.sink,
      Represents N f rs p ∧ p.IsPath ∧ DistanceSpec.IsShortest p ∧
      (trace N.graph N.source N.sink out.1.pred).1 = some rs

section Expected
set_option linter.checkUnivs false

def prepareRowsType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  Digraph V A → List (Label A) → Rows V A

def prepareFromArcsType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  Digraph V A → List A → Rows V A

def stepType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  Network V A → (A → ℝ) → Rows V A → State V A → Option (State V A × Work)

def executeType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  Network V A → (A → ℝ) → Rows V A → ℕ → State V A → State V A × Work

def runType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  Network V A → (A → ℝ) → Rows V A → State V A × Work

def traceType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  Digraph V A → V → V → (V → Option (Label A)) → Option (List (Label A)) × Work

def searchType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A],
  Network V A → (A → ℝ) → Rows V A → Option (List (Label A)) × Work

def prepare_from_arcs_correct : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (as : List A), Enumeration as →
      LegalRows G (prepareFromArcs G as)

def prepare_rows_correct : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (rs : List (Label A)), Enumeration rs →
      LegalRows G (prepareRows G rs)

def step_decreases : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (rows : Rows V A)
    (σ τ : State V A) (w : Work), step N f rows σ = some (τ, w) →
      potential rows τ < potential rows σ

def search_terminates : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (rows : Rows V A),
      Execution N f rows (initial N.source) (run N f rows).1 (run N f rows).2 ∧
      step N f rows (run N f rows).1 = none

/-- Correctness is uniform over every legal adjacency ordering. It uses no
integrality or positivity assumptions on capacities beyond the Network type,
and in fact the BFS implementation also works at nonfeasible arc vectors. -/
def search_correct : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), N.Feasible f →
    ∀ rows : Rows V A, LegalRows N.graph rows → Correct N f rows

/-- Canonical typed success/failure refinement of the actual search output.
The success Walk must represent the returned list, with the stored pointers;
no independent path selector or oracle may replace that returned list. -/
def typed_search_result : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), N.Feasible f →
    ∀ rows : Rows V A, LegalRows N.graph rows →
      ((search N f rows).1 = none ∧
        ¬ Nonempty (Walk (residual N f) N.source N.sink)) ∨
      ∃ (rs : List (Label A)) (p : Walk (residual N f) N.source N.sink),
        (search N f rows).1 = some rs ∧ Represents N f rs p ∧
        p.IsPath ∧ DistanceSpec.IsShortest p ∧
        (trace N.graph N.source N.sink (run N f rows).1.pred).1 = some rs
end Expected
end P205.Networks.BFSSpec
