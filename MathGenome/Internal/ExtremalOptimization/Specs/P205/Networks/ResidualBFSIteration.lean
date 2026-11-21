import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ResidualBFS

/-! Costed Edmonds–Karp iteration, paper.tex 1730–1772.
The canonical search and all adjacency orders are those of BFSSpec.  The two
additional passes below use indexed RAM loads/stores, with the same convention
as BFSSpec: functional tables denote mutable arrays, not closure chains. The
input flow array is updated in place; there is no all-arc copy. The bottleneck
pass finishes before any load is changed. Recursive calls are tail calls, and
work is ghost instrumentation, not a list allocated by the program.
-/
open scoped Classical BigOperators
universe u v
namespace P205.Networks.IterationSpec
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows
open BFSSpec
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

/-- One residual capacity fetch includes its inspection and exact subtraction. -/
def minimumAux (c : Label A → ℝ) : ℝ → List (Label A) → ℝ
  | d, [] => d
  | d, r :: rs => minimumAux c (min d (c r)) rs

def minimum (c : Label A → ℝ) : List (Label A) → Option ℝ
  | [] => none
  | r :: rs => some (minimumAux c (c r) rs)

def minimumAuxWork : List (Label A) → Work
  | [] => Work.events [.listTest, .branch]
  | _ :: rs => (Work.events [.listTest, .listRead, .inspect, .read, .read,
      .branch, .subtract, .compare, .branch, .branch]).plus (minimumAuxWork rs)

def minimumWork : List (Label A) → Work
  | [] => Work.events [.listTest, .branch]
  | _ :: rs => (Work.events [.listTest, .listRead, .inspect, .read, .read,
      .branch, .subtract, .branch]).plus (minimumAuxWork rs)

/-- A sparse signed pass: exactly one indexed load and store per path copy.
The increment event denotes one exact real addition (or subtraction for false);
there is no separately evaluated unary negation in the backward update.
Repeated original labels and either direction are handled by sequential stores. -/
noncomputable def sparse (d : ℝ) : List (Label A) → (A → ℝ) → (A → ℝ)
  | [], g => g
  | r :: rs, g => sparse d rs
      (Function.update g r.1 (if r.2 then g r.1 + d else g r.1 - d))

def sparseWork : List (Label A) → Work
  | [] => Work.events [.listTest, .branch]
  | _ :: rs => (Work.events [.listTest, .listRead, .read, .branch,
      .increment, .write, .branch]).plus (sparseWork rs)

structure Output (A : Type v) where
  labels : List (Label A)
  amount : ℝ
  flow : A → ℝ

/-- The output contains exactly the predecessor trace, its computed minimum,
and the actual sparse array update. `none` also covers an empty raw trace;
the correctness theorem must rule that case out on successful s–t searches. -/
noncomputable def iteration (N : Network V A) (f : A → ℝ) (rows : Rows V A) :
    Option (Output A) × Work :=
  let out := search N f rows
  match out.1 with
  | none => (none, out.2.plus (Work.events [.branch]))
  | some rs =>
    match minimum (BoundedSpec.capacity (fun _ => 0) N.capacity f) rs with
    | none => (none, out.2.plus ((Work.events [.branch, .branch]).plus (minimumWork rs)))
    | some d =>
      (some ⟨rs, d, sparse d rs f⟩,
       out.2.plus ((Work.events [.branch]).plus ((minimumWork rs).plus
         ((Work.events [.branch, .allocate, .write, .allocate, .write, .allocate, .write, .branch]).plus (sparseWork rs)))))

/-- Reusable semantic refinement of the concrete iteration. -/
def Correct (N : Network V A) (f : A → ℝ) (rows : Rows V A) : Prop :=
  match (iteration N f rows).1 with
  | none => ¬ Nonempty (Walk (residual N f) N.source N.sink)
  | some out => ∃ p : Walk (residual N f) N.source N.sink,
      (search N f rows).1 = some out.labels ∧ Represents N f out.labels p ∧
      p.IsPath ∧ DistanceSpec.IsShortest p ∧
      (trace N.graph N.source N.sink (run N f rows).1.pred).1 = some out.labels ∧
      BoundedSpec.Bottleneck N.graph (fun _ => 0) N.capacity f p out.amount ∧
      out.flow = BoundedSpec.augment N.graph (fun _ => 0) N.capacity f p out.amount ∧
      N.Feasible out.flow

section Expected
set_option linter.checkUnivs false

/-- Every finite legal execution, including partial executions, is bounded.
This accounts for amortized queue reversals rather than assigning them unit cost. -/
def execution_linear : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (rows : Rows V A), LegalRows N.graph rows →
    ∀ (σ : State V A) (w : Work), Execution N f rows (initial N.source) σ w →
      w.operations ≤ 150 * (Fintype.card V + Fintype.card A) ∧
      w.inspections ≤ 150 * (Fintype.card V + Fintype.card A)

/-- Once-only construction, including producing both signed labels, is linear
for every input enumeration. No per-search adjacency rebuild is required. -/
def setup_linear : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (vs : List V) (as : List A), Enumeration vs → Enumeration as →
      LegalRows N.graph (prepareFromArcs N.graph as) ∧
      (prepareFromArcsWork vs as).operations ≤
        30 * (Fintype.card V + Fintype.card A) ∧
      (prepareFromArcsWork vs as).inspections = 0

/-- Includes initialization, row-length budget computation, final halt tests,
all search operations, and the actual trace, on success and failure alike. -/
def search_linear : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ) (rows : Rows V A), LegalRows N.graph rows →
      (search N f rows).2.operations ≤ 200 * (Fintype.card V + Fintype.card A) ∧
      (search N f rows).2.inspections ≤ 200 * (Fintype.card V + Fintype.card A)

/-- Full successful and final unsuccessful iteration, at arbitrary feasible
real flows and every legal adjacency ordering. The numerical constant is universal. -/
def iteration_correct_and_linear : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (N : Network V A) (f : A → ℝ), N.Feasible f →
    ∀ rows : Rows V A, LegalRows N.graph rows →
      Correct N f rows ∧
      (iteration N f rows).2.operations ≤ 300 * (Fintype.card V + Fintype.card A) ∧
      (iteration N f rows).2.inspections ≤ 300 * (Fintype.card V + Fintype.card A)

end Expected
end P205.Networks.IterationSpec
