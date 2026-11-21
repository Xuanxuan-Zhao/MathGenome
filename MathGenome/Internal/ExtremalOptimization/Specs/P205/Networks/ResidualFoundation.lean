import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Flows.Augmentation

/-! Bounded real flows on the canonical finite labelled directed multigraph.
Independent definitions and full expected propositions for paper.tex 1673–1692,
1821–1823. True denotes forward, false backward. No hypotheses exclude loops,
parallel/opposite labels, empty vertex types, or negative lower bounds. -/
open scoped BigOperators Classical
universe u v
namespace P205.Networks.BoundedSpec
open FiniteCombinatorics.Directed
open FiniteCombinatorics.Graph.Flows
variable {V : Type u} {A : Type v} [Fintype V] [Fintype A]

noncomputable def arcSum (f : A → ℝ) (F : Finset A) : ℝ := ∑ a ∈ F, f a
noncomputable def outgoing (G : Digraph V A) (S : Set V) : Finset A :=
  Finset.univ.filter (fun a => G.tail a ∈ S ∧ G.head a ∉ S)
noncomputable def incoming (G : Digraph V A) (S : Set V) : Finset A :=
  Finset.univ.filter (fun a => G.tail a ∉ S ∧ G.head a ∈ S)
def WithinBounds (lo hi f : A → ℝ) : Prop := ∀ a, lo a ≤ f a ∧ f a ≤ hi a
def Feasible (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ) (f : A → ℝ) : Prop :=
  WithinBounds lo hi f ∧ ∀ x, G.divergence f x = b x
def capacity (lo hi f : A → ℝ) (r : A × Bool) : ℝ :=
  if r.2 then hi r.1 - f r.1 else f r.1 - lo r.1
/-- Only strictly positive copies are present; original arc identities survive. -/
def ResidualArc (lo hi f : A → ℝ) := {r : A × Bool // 0 < capacity lo hi f r}
noncomputable instance (lo hi f : A → ℝ) : Fintype (ResidualArc lo hi f) := by
  unfold ResidualArc
  infer_instance

def graph (G : Digraph V A) (lo hi f : A → ℝ) : Digraph V (ResidualArc lo hi f) where
  tail r := if r.val.2 then G.tail r.val.1 else G.head r.val.1
  head r := if r.val.2 then G.head r.val.1 else G.tail r.val.1
def cost (w : A → ℝ) (r : A × Bool) : ℝ := if r.2 then w r.1 else -w r.1
noncomputable def step (ε : ℝ) (r : A × Bool) (a : A) : ℝ :=
  if a = r.1 then (if r.2 then ε else -ε) else 0
noncomputable def adjustment (ε : ℝ) (l : List (A × Bool)) (a : A) : ℝ :=
  (l.map (fun r => step ε r a)).sum
noncomputable def augment (G : Digraph V A) (lo hi f : A → ℝ) {x y : V}
    (p : Walk (graph G lo hi f) x y) (ε : ℝ) : A → ℝ :=
  fun a => f a + adjustment ε (p.arcs.map Subtype.val) a
/-- An attained positive minimum on a nonempty walk. -/
def Bottleneck (G : Digraph V A) (lo hi f : A → ℝ) {x y : V}
    (p : Walk (graph G lo hi f) x y) (δ : ℝ) : Prop :=
  0 < δ ∧ (∀ r ∈ p.arcs, δ ≤ capacity lo hi f r.val) ∧
    ∃ r ∈ p.arcs, δ = capacity lo hi f r.val

/-- Identity on the signed label, retaining the positivity certificate. -/
def toLibrary (N : Network V A) (f : A → ℝ)
    (r : ResidualArc (fun _ => 0) N.capacity f) : N.ResidualArc f :=
  ⟨r.val, by simpa [capacity, ResidualSpec.capacity] using r.property⟩
def fromLibrary (N : Network V A) (f : A → ℝ)
    (r : N.ResidualArc f) : ResidualArc (fun _ => 0) N.capacity f :=
  ⟨r.val, by simpa [capacity, ResidualSpec.capacity] using r.property⟩
def toLibraryWalk (N : Network V A) (f : A → ℝ) {x y : V} :
    Walk (graph N.graph (fun _ => 0) N.capacity f) x y →
    Walk (N.residualGraph f) x y
  | .nil x => .nil x
  | .cons a p => .cons ⟨toLibrary N f a.val, a.property⟩ (toLibraryWalk N f p)

section Expected
set_option linter.checkUnivs false

def arcSumType := ∀ {A : Type v}, (A → ℝ) → Finset A → ℝ

def outgoingType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Digraph V A → Set V → Finset A

def incomingType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Digraph V A → Set V → Finset A

def WithinBoundsType := ∀ {A : Type v}, (A → ℝ) → (A → ℝ) → (A → ℝ) → Prop

def FeasibleType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], Digraph V A → (A → ℝ) → (A → ℝ) → (V → ℝ) → (A → ℝ) → Prop

def capacityType := ∀ {A : Type v}, (A → ℝ) → (A → ℝ) → (A → ℝ) → A × Bool → ℝ

def ResidualArcType := ∀ {A : Type v}, (A → ℝ) → (A → ℝ) → (A → ℝ) → Type v

def graphType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], (G : Digraph V A) → (lo hi f : A → ℝ) → Digraph V (ResidualArc lo hi f)

def costType := ∀ {A : Type v}, (A → ℝ) → A × Bool → ℝ

def stepType := ∀ {A : Type v}, ℝ → A × Bool → A → ℝ

def adjustmentType := ∀ {A : Type v}, ℝ → List (A × Bool) → A → ℝ

def augmentType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], (G : Digraph V A) → (lo hi f : A → ℝ) → ∀ {x y : V}, Walk (graph G lo hi f) x y → ℝ → A → ℝ

def BottleneckType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], (G : Digraph V A) → (lo hi f : A → ℝ) → ∀ {x y : V}, Walk (graph G lo hi f) x y → ℝ → Prop

def toLibraryType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], (N : Network V A) → (f : A → ℝ) → ResidualArc (fun _ => 0) N.capacity f → N.ResidualArc f

def fromLibraryType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], (N : Network V A) → (f : A → ℝ) → N.ResidualArc f → ResidualArc (fun _ => 0) N.capacity f

def toLibraryWalkType := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], (N : Network V A) → (f : A → ℝ) → ∀ {x y : V}, Walk (graph N.graph (fun _ => 0) N.capacity f) x y → Walk (N.residualGraph f) x y

def cut_divergence : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], ∀ (G : Digraph V A) (f : A → ℝ) (S : Set V),
  (∑ x ∈ Finset.univ.filter (fun x => x ∈ S), G.divergence f x) =
    arcSum f (outgoing G S) - arcSum f (incoming G S)

def sum_divergence : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], ∀ (G : Digraph V A) (f : A → ℝ), (∑ x, G.divergence f x) = 0

def augment_divergence : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], ∀ (G : Digraph V A) (lo hi f : A → ℝ) {x y : V}
  (p : Walk (graph G lo hi f) x y) (ε : ℝ) (z : V),
  G.divergence (augment G lo hi f p ε) z = G.divergence f z +
    ((if x = z then ε else 0) - (if y = z then ε else 0))

def exists_bottleneck : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], ∀ (G : Digraph V A) (lo hi f : A → ℝ) {x y : V}
  (p : Walk (graph G lo hi f) x y), p.arcs ≠ [] → ∃ δ, Bottleneck G lo hi f p δ

def augment_path : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], ∀ (G : Digraph V A) (lo hi f : A → ℝ) {x y : V}
  (p : Walk (graph G lo hi f) x y), p.IsPath → WithinBounds lo hi f →
  ∀ (δ ε : ℝ), Bottleneck G lo hi f p δ → 0 ≤ ε → ε ≤ δ →
  WithinBounds lo hi (augment G lo hi f p ε) ∧
    ∀ z, G.divergence (augment G lo hi f p ε) z = G.divergence f z +
      ((if x = z then ε else 0) - (if y = z then ε else 0))

def augment_cycle : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], ∀ (G : Digraph V A) (lo hi f : A → ℝ) (b : V → ℝ) {x : V}
  (p : Walk (graph G lo hi f) x x), p.IsCycle → Feasible G lo hi b f →
  ∀ (δ ε : ℝ), Bottleneck G lo hi f p δ → 0 ≤ ε → ε ≤ δ →
  Feasible G lo hi b (augment G lo hi f p ε)

def paired_cancellation : Prop := ∀ {A : Type v} [Fintype A], ∀ (a : A) (ε : ℝ) (l₁ l₂ l₃ : List (A × Bool)),
  adjustment ε (l₁ ++ [(a, true)] ++ l₂ ++ [(a, false)] ++ l₃) =
    adjustment ε (l₁ ++ l₂ ++ l₃)

def loop_cycle : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], ∀ (G : Digraph V A) (lo hi f : A → ℝ) (r : ResidualArc lo hi f)
  (h : (graph G lo hi f).tail r = (graph G lo hi f).head r),
  (Walk.cons (⟨r, rfl, h.symm⟩ : Arc (graph G lo hi f)
    ((graph G lo hi f).tail r) ((graph G lo hi f).tail r))
      (Walk.nil _)).IsCycle

def zero_lower_bridge : Prop := ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A], ∀ (N : Network V A) (f : A → ℝ),
  (∀ r, fromLibrary N f (toLibrary N f r) = r) ∧
  (∀ r, toLibrary N f (fromLibrary N f r) = r) ∧
  (∀ r, capacity (fun _ => 0) N.capacity f r = N.residualCapacity f r) ∧
  (∀ r, (N.residualGraph f).tail (toLibrary N f r) =
    (graph N.graph (fun _ => 0) N.capacity f).tail r ∧
    (N.residualGraph f).head (toLibrary N f r) =
    (graph N.graph (fun _ => 0) N.capacity f).head r) ∧
  (∀ {x y : V} (p : Walk (graph N.graph (fun _ => 0) N.capacity f) x y) ε,
    augment N.graph (fun _ => 0) N.capacity f p ε =
      N.augment f (toLibraryWalk N f p) ε) ∧
  (N.Feasible f ↔ WithinBounds (fun _ => 0) N.capacity f ∧
    ∀ x, x ≠ N.source → x ≠ N.sink → N.graph.divergence f x = 0)

/-- Cycle augmentation needs bounds alone; no prescribed balance is assumed. -/
def augment_cycle_bounds : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi f : A → ℝ) {x : V}
    (p : Walk (graph G lo hi f) x x), p.IsCycle → WithinBounds lo hi f →
    ∀ (δ ε : ℝ), Bottleneck G lo hi f p δ → 0 ≤ ε → ε ≤ δ →
      WithinBounds lo hi (augment G lo hi f p ε) ∧
      ∀ z, G.divergence (augment G lo hi f p ε) z = G.divergence f z

def cycle_bottleneck : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi f : A → ℝ) {x : V}
    (p : Walk (graph G lo hi f) x x), p.IsCycle → ∃ δ, Bottleneck G lo hi f p δ

end Expected
end P205.Networks.BoundedSpec
