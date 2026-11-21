import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ShortestPathBound
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.MaxFlowMinCut
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ResidualBFSIteration

/-! W37: shortest augmentation, its concrete adjacency-list realization, and costs.
The semantic strategy allows every shortest-path/tie choice. The concrete program
uses the upstream FIFO BFS, predecessor trace, minimum pass and sparse update.
All tables and exact real arithmetic have the upstream indexed RAM semantics.
Work and execution counts are ghost instrumentation, not stored histories. -/
open scoped Classical
universe u v
namespace P205.Networks.EdmondsKarpSpec
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

abbrev residual (N : Network V A) (f : A → ℝ) :=
  BoundedSpec.graph N.graph (fun _ => 0) N.capacity f

/-- The two legal outcomes of a shortest-path search and bottleneck update. -/
inductive SearchResult (N : Network V A) (f : A → ℝ) : Type (max u v)
  | found (g : A → ℝ) (step : ShortestBoundSpec.AugmentationStep N f g)
  | exhausted (noWalk : ¬ Nonempty (Walk (residual N f) N.source N.sink))

/-- Every choice of shortest paths and ties is allowed, including choices
that vary with the iteration index. -/
abbrev Strategy (N : Network V A) := ℕ → ∀ f : A → ℝ, SearchResult N f

def advance {N : Network V A} {f : A → ℝ} : SearchResult N f → (A → ℝ)
  | .found g _ => g
  | .exhausted _ => f

/-- Repeated search and full-bottleneck update, starting from the zero flow.
After exhaustion the flow is held fixed. -/
def flow (N : Network V A) (choose : Strategy N) : ℕ → A → ℝ
  | 0 => fun _ => 0
  | n + 1 => advance (choose n (flow N choose n))

/-- The actual source-reachable cut is an equal-value optimality certificate,
with the original signed labels and real capacities. -/
def TerminalCertificate (N : Network V A) (f : A → ℝ) : Prop :=
  let S := FlowCutSpec.reachableSet N f
  (¬ Nonempty (Walk (residual N f) N.source N.sink)) ∧
    N.Feasible f ∧ N.IsCut S ∧
    (∀ a ∈ BoundedSpec.outgoing N.graph S, f a = N.capacity a) ∧
    (∀ a ∈ BoundedSpec.incoming N.graph S, f a = 0) ∧
    N.value f = BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph S) ∧
    N.IsMaximum f ∧ ∀ T : Set V, N.IsCut T →
      BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph S) ≤
      BoundedSpec.arcSum N.capacity (BoundedSpec.outgoing N.graph T)

/-- The concrete iteration's flow, held fixed on an unsuccessful search. -/
def nextFlow (f : A → ℝ) : Option (IterationSpec.Output A) → (A → ℝ)
  | none => f
  | some out => out.flow

/-- Actual BFS iterates from zero. No semantic path selector is evaluated. -/
noncomputable def bfsFlow (N : Network V A) (rows : BFSSpec.Rows V A) : ℕ → A → ℝ
  | 0 => fun _ => 0
  | i + 1 => nextFlow (bfsFlow N rows i)
      (IterationSpec.iteration N (bfsFlow N rows i) rows).1

/-- Outer loop: fuel test/branch/decrement, result dispatch and flow-pointer
load/store/branch. These are added to the complete BFS/tracing/update work.
The four extra register events conservatively include return/control overhead. -/
def loopControl : BFSSpec.Work := BFSSpec.Work.events
  [.compare, .branch, .subtract, .branch, .read, .write, .branch,
   .read, .write, .branch]

noncomputable def iterationWork (N : Network V A) (f : A → ℝ)
    (rows : BFSSpec.Rows V A) : BFSSpec.Work :=
  (IterationSpec.iteration N f rows).2.plus loopControl

/-- Cost of the first k searches; stopping after n augmentations uses k=n+1. -/
noncomputable def prefixWork (N : Network V A) (rows : BFSSpec.Rows V A) :
    ℕ → BFSSpec.Work
  | 0 => ⟨0, 0⟩
  | k + 1 => (prefixWork N rows k).plus (iterationWork N (bfsFlow N rows k) rows)

/-- Allocate and zero the original-arc flow array, once, cell by cell. -/
def zeroWork : List A → BFSSpec.Work
  | [] => BFSSpec.Work.events [.listTest]
  | _ :: as => (BFSSpec.Work.events
      [.listTest, .listRead, .allocate, .write, .branch]).plus (zeroWork as)

/-- Construct adjacency rows and initialize flow once. The final five unit
operations read the two input cardinalities and calculate 2*|V|*|E|+1
(two integer multiplications and one addition) for the safety budget. -/
def setupWork (vs : List V) (as : List A) : BFSSpec.Work :=
  (BFSSpec.prepareFromArcsWork vs as).plus ((zeroWork as).plus ⟨5, 0⟩)

/-- Counts and work are observations of the program; only the flow table and
loop registers are runtime data. `finished=false` records safety-fuel exhaustion,
which must be ruled out, rather than interpreted as successful termination. -/
structure LoopResult (A : Type v) where
  flow : A → ℝ
  augmentations : ℕ
  searches : ℕ
  finished : Bool
  work : BFSSpec.Work

/-- A bounded interpreter for the actual repeat-search/update program.
The program stops on the first `none`, and never searches again after it.
Tail calls reuse the flow array, with no all-arc copying. -/
noncomputable def execute (N : Network V A) (rows : BFSSpec.Rows V A) :
    ℕ → (A → ℝ) → LoopResult A
  | 0, f => ⟨f, 0, 0, false, BFSSpec.Work.events [.compare, .branch]⟩
  | k + 1, f =>
    match (IterationSpec.iteration N f rows).1 with
    | none => ⟨f, 0, 1, true, iterationWork N f rows⟩
    | some out =>
      let tail := execute N rows k out.flow
      ⟨tail.flow, tail.augmentations + 1, tail.searches + 1, tail.finished,
        (iterationWork N f rows).plus tail.work⟩

/-- A complete zero-start algorithm on indexed graph input. The arc enumeration
also selects the static adjacency order. The safety cutoff is never reached. -/
noncomputable def algorithm (N : Network V A) (vs : List V) (as : List A) : LoopResult A :=
  let rows := BFSSpec.prepareFromArcs N.graph as
  let out := execute N rows (2 * Fintype.card V * Fintype.card A + 1) (fun _ => 0)
  { out with work := (setupWork vs as).plus out.work }

/-- Full correctness and costs for a first failed BFS at index n. All earlier
successful outputs are the actual shortest-path/full-bottleneck updates, through
`IterationSpec.Correct`, including the returned labels and predecessor pointers. -/
def BFSExecution (N : Network V A) (rows : BFSSpec.Rows V A) (n : ℕ) : Prop :=
  TerminalCertificate N (bfsFlow N rows n) ∧
  (IterationSpec.iteration N (bfsFlow N rows n) rows).1 = none ∧
  (∀ i, i < n → ∃ out, (IterationSpec.iteration N (bfsFlow N rows i) rows).1 = some out) ∧
  (∀ i, n ≤ i → bfsFlow N rows i = bfsFlow N rows n) ∧
  (∀ i, N.Feasible (bfsFlow N rows i) ∧
    IterationSpec.Correct N (bfsFlow N rows i) rows ∧
    (iterationWork N (bfsFlow N rows i) rows).operations ≤
      310 * (Fintype.card V + Fintype.card A) ∧
    (iterationWork N (bfsFlow N rows i) rows).inspections ≤
      310 * (Fintype.card V + Fintype.card A)) ∧
  (prefixWork N rows (n + 1)).operations ≤
    (n + 1) * (310 * (Fintype.card V + Fintype.card A)) ∧
  (prefixWork N rows (n + 1)).inspections ≤
    (n + 1) * (310 * (Fintype.card V + Fintype.card A))

section Expected
set_option linter.checkUnivs false

def search_exists : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), Nonempty (SearchResult N f)

/-- This is uniform over every legal shortest-path choice, rather than an
existence assertion about a single favorable sequence of augmentations. -/
def termination : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (choose : Strategy N),
    ∃ n : ℕ, n ≤ 2 * Fintype.card V * Fintype.card A ∧
      TerminalCertificate N (flow N choose n) ∧
      (∀ i : ℕ, i < n → ∃ (g : A → ℝ)
        (step : ShortestBoundSpec.AugmentationStep N (flow N choose i) g),
          choose i (flow N choose i) = SearchResult.found g step) ∧
      ∀ i : ℕ, n ≤ i → flow N choose i = flow N choose n

/-- Every bounded finite prefix starting at zero preserves feasibility. -/
def prefix_feasible : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (choose : Strategy N) (i : ℕ), N.Feasible (flow N choose i)

/-- The concrete flow sequence is a legal semantic shortest-augmentation run. -/
def bfs_refinement : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (rows : BFSSpec.Rows V A), BFSSpec.LegalRows N.graph rows →
    ∃ choose : Strategy N, ∀ i, bfsFlow N rows i = flow N choose i

/-- Every legal adjacency order terminates with at most the uniform number
of augmentations, linear work per iteration, and exactly one final failed search. -/
def bfs_termination : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (rows : BFSSpec.Rows V A), BFSSpec.LegalRows N.graph rows →
    ∃ n, n ≤ 2 * Fintype.card V * Fintype.card A ∧ BFSExecution N rows n

/-- End-to-end program theorem, including once-only setup and zero initialization.
The work constant is universal and independent of all real capacity magnitudes.
There is no cutoff termination: `finished=true` means a genuine failed search. -/
def algorithm_correct_and_linear : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (vs : List V) (as : List A),
    BFSSpec.Enumeration vs → BFSSpec.Enumeration as →
    let out := algorithm N vs as
    out.finished = true ∧
    out.augmentations ≤ 2 * Fintype.card V * Fintype.card A ∧
    out.searches = out.augmentations + 1 ∧
    TerminalCertificate N out.flow ∧
    BFSExecution N (BFSSpec.prepareFromArcs N.graph as) out.augmentations ∧
    out.flow = bfsFlow N (BFSSpec.prepareFromArcs N.graph as) out.augmentations ∧
    out.work.operations ≤ (40 + 310 * out.searches) *
      (Fintype.card V + Fintype.card A) ∧
    out.work.inspections ≤ 310 * out.searches * (Fintype.card V + Fintype.card A) ∧
    out.work.operations ≤ (40 + 310 * (2 * Fintype.card V * Fintype.card A + 1)) *
      (Fintype.card V + Fintype.card A)

end Expected
end P205.Networks.EdmondsKarpSpec
