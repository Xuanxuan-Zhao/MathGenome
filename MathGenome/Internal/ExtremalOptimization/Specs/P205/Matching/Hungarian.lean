import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.HungarianStep

/-! The nondeterministic tight-edge Hungarian method of paper.tex W43.
Search is the full directed reachability relation from HungarianStep. Root
selection and path choices are unrestricted. A search itself is finite graph
reachability; the transitions below count root selections, potential updates,
and actual alternating path flips. No optimizer or progress certificate is
part of the definition of a transition. -/
set_option linter.checkUnivs false
universe u v
noncomputable section
namespace Specs.P205.Matching.Hungarian.Algorithm
open Specs.P205.Matching
open Specs.P205.Matching.Hungarian

variable {L : Type u} {R : Type v}

structure State (G : BipartiteGraph L R) where
  left : L → ℝ
  right : R → ℝ
  matching : Set (Edge G)
  root : Option L

variable [Fintype L] [Fintype R] {G : BipartiteGraph L R}

def initial (w : Edge G → ℝ) : State G :=
  ⟨initialLeft w, fun _ => 0, ∅, none⟩

def Valid (w : Edge G → ℝ) (s : State G) : Prop :=
  Legal w s.left s.right s.matching ∧
    ∀ i, s.root = some i → ¬ Covered s.matching (.inl i)

/-- The minimum is over actual allowed boundary edges. Reached sets and the
minimum are recomputed after each update with the same unmatched root. -/
def PotentialUpdate (w : Edge G → ℝ) (M : Set (Edge G)) (root : L)
    (p q : (L → ℝ) × (R → ℝ)) : Prop :=
  Legal w p.1 p.2 M ∧ ¬ Covered M (.inl root) ∧ Stalled w p.1 p.2 M root ∧
  q = (updateLeft p.1 (leftReach w p.1 p.2 M root) (minimumSlack w p.1 p.2 M root),
       updateRight p.2 (rightReach w p.1 p.2 M root) (minimumSlack w p.1 p.2 M root))

/-- `none` means that the previous augmentation is finished and a new root
may be selected. An augmentation resets the root, and flips precisely the
simple alternating path recorded by `Augments`. -/
inductive Step (w : Edge G → ℝ) : State G → State G → Prop
  | choose (a : L → ℝ) (b : R → ℝ) (M : Set (Edge G)) (i : L)
      (h : Legal w a b M) (hi : ¬ Covered M (.inl i)) :
      Step w ⟨a, b, M, none⟩ ⟨a, b, M, some i⟩
  | update (M : Set (Edge G)) (i : L) (p q : (L → ℝ) × (R → ℝ))
      (h : PotentialUpdate w M i p q) :
      Step w ⟨p.1, p.2, M, some i⟩ ⟨q.1, q.2, M, some i⟩
  | augment (a : L → ℝ) (b : R → ℝ) (M N : Set (Edge G)) (i : L) (j : R)
      (h : Legal w a b M) (hi : ¬ Covered M (.inl i))
      (hj : j ∈ rightReach w a b M i) (hf : ¬ Covered M (.inr j))
      (path : Augments w a b M N i j) :
      Step w ⟨a, b, M, some i⟩ ⟨a, b, N, none⟩

/-- A complete execution makes a permitted transition whenever possible and
stays at its output after stopping. There is no fairness or tie-breaking rule. -/
def Execution (w : Edge G → ℝ) (f : ℕ → State G) : Prop :=
  f 0 = initial w ∧ ∀ n, Step w (f n) (f (n + 1)) ∨
    ((¬ ∃ t, Step w (f n) t) ∧ f (n + 1) = f n)

def Optimal (w : Edge G → ℝ) (s : State G) : Prop :=
  IsPerfectMatching s.matching ∧ FreeFeasible w s.left s.right ∧
  matchingWeight w s.matching = potentialSum s.left s.right ∧
  (∀ N : Set (Edge G), IsPerfectMatching N →
    matchingWeight w N ≤ matchingWeight w s.matching) ∧
  (∀ (a : L → ℝ) (b : R → ℝ), FreeFeasible w a b →
    potentialSum s.left s.right ≤ potentialSum a b)

def initializationType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ),
    (∃ P : Set (Edge G), IsPerfectMatching P) → Valid w (initial w)

def updateProgressType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ)
    (M : Set (Edge G)) (i : L) (p q : (L → ℝ) × (R → ℝ)),
    (∃ P : Set (Edge G), IsPerfectMatching P) → PotentialUpdate w M i p q →
    Legal w q.1 q.2 M ∧ rightReach w p.1 p.2 M i ⊂ rightReach w q.1 q.2 M i

/-- A quantitative finite bound for every sequence of updates at a fixed root,
including every search/tie choice consistent with the method. -/
def updateBoundType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ) (M : Set (Edge G)) (i : L),
    (∃ P : Set (Edge G), IsPerfectMatching P) →
    ∀ (p : ℕ → (L → ℝ) × (R → ℝ)) (n : ℕ),
    (∀ k < n, PotentialUpdate w M i (p k) (p (k + 1))) →
    n + Nat.card (rightReach w (p 0).1 (p 0).2 M i) ≤ Nat.card R

def augmentationProgressType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ) (a : L → ℝ) (b : R → ℝ)
    (M N : Set (Edge G)) (i : L) (j : R),
    Legal w a b M → Augments w a b M N i j →
    Legal w a b N ∧ Nat.card N = Nat.card M + 1

def preservationType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ),
    (∃ P : Set (Edge G), IsPerfectMatching P) →
    ∀ s t, Step w s t → Valid w t

def progressType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ),
    (∃ P : Set (Edge G), IsPerfectMatching P) →
    ∀ s, Valid w s → ¬ IsPerfectMatching s.matching → ∃ t, Step w s t

/-- Reverse well-foundedness excludes every infinite permitted execution, with
no fairness restriction. The two decreasing quantities are the remaining
matching size and the remaining reached-right capacity of the active root. -/
def terminationType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ),
    (∃ P : Set (Edge G), IsPerfectMatching P) →
    WellFounded (fun t s => Step w s t)

def correctnessType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ),
    (∃ P : Set (Edge G), IsPerfectMatching P) →
    ∀ s, Relation.ReflTransGen (Step w) (initial w) s →
    (¬ ∃ t, Step w s t) → Optimal w s

/-- Every finite prefix of an execution can be completed to an optimal terminal
state by actual algorithm transitions, including the zero-size case. Together
with termination and correctness this states termination for all choices. -/
def completionType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ),
    (∃ P : Set (Edge G), IsPerfectMatching P) →
    ∀ s, Relation.ReflTransGen (Step w) (initial w) s →
    ∃ t, Relation.ReflTransGen (Step w) s t ∧ (¬ ∃ z, Step w t z) ∧ Optimal w t

/-- Every execution, for arbitrary permitted choices, reaches its optimal
output at a finite index and remains there. -/
def executionTerminatesType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ),
    (∃ P : Set (Edge G), IsPerfectMatching P) →
    ∀ f, Execution w f → ∃ n, (¬ ∃ t, Step w (f n) t) ∧ Optimal w (f n) ∧
      ∀ m, n ≤ m → f m = f n

end Specs.P205.Matching.Hungarian.Algorithm
