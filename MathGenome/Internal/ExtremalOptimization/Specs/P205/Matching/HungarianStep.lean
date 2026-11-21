import MathGenome.Internal.ExtremalOptimization.Specs.P205.Matching.Models
import MathGenome.Internal.FiniteCombinatorics.FiniteCombinatorics.Graph.Matching.Berge
import Mathlib.Data.Finset.Max
import Mathlib.Logic.Relation

/-! Independent statements for the initialization, alternating search, augmentation,
and potential update in paper.tex, W43. All edges retain their original coordinates.
The search starts at one specified unmatched left vertex. -/
set_option linter.checkUnivs false

universe u v
noncomputable section
namespace Specs.P205.Matching.Hungarian
open Specs.P205.Matching

variable {L : Type u} {R : Type v} {G : BipartiteGraph L R}

def Legal (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ) (M : Set (Edge G)) : Prop :=
  FreeFeasible w u v ∧ IsMatching M ∧ UsesTightEdges w M u v

def SearchArc (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) : L ⊕ R → L ⊕ R → Prop
  | .inl i, .inr j => ∃ e : Edge G, e.val.1 = i ∧ e.val.2 = j ∧
      e ∉ M ∧ Tight w u v e
  | .inr j, .inl i => ∃ e : Edge G, e.val.1 = i ∧ e.val.2 = j ∧ e ∈ M
  | _, _ => False

def Reached (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) (root : L) (x : L ⊕ R) : Prop :=
  Relation.ReflTransGen (SearchArc w u v M) (.inl root) x

def leftReach (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) (root : L) : Set L := {i | Reached w u v M root (.inl i)}

def rightReach (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) (root : L) : Set R := {j | Reached w u v M root (.inr j)}

def Stalled (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) (root : L) : Prop :=
  ∀ j ∈ rightReach w u v M root, Covered M (.inr j)

def boundary (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) (root : L) : Set (Edge G) :=
  {e | e.val.1 ∈ leftReach w u v M root ∧ e.val.2 ∉ rightReach w u v M root}

def updateLeft (u : L → ℝ) (S : Set L) (δ : ℝ) : L → ℝ := by
  classical
  exact fun i => if i ∈ S then u i - δ else u i

def updateRight (v : R → ℝ) (T : Set R) (δ : ℝ) : R → ℝ := by
  classical
  exact fun j => if j ∈ T then v j + δ else v j

variable [Fintype L] [Fintype R]

def rowWeights (w : Edge G → ℝ) (i : L) : Finset ℝ := by
  classical
  exact (Finset.univ.filter (fun e : Edge G => e.val.1 = i)).image w

/-- The fallback is used only at isolated left vertices; perfect matchability
makes every row queried by a left vertex nonempty. Empty sides need no choices. -/
def initialLeft (w : Edge G → ℝ) (i : L) : ℝ := by
  classical
  exact if h : (rowWeights w i).Nonempty then (rowWeights w i).max' h else 0

def minimumSlack (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) (root : L) : ℝ := by
  classical
  let s := (Finset.univ.filter (fun e : Edge G => e ∈ boundary w u v M root)).image
    (slack w u v)
  exact if h : s.Nonempty then s.min' h else 0

/-- An augmentation is an actual path flip on original edges, rather than an
arbitrary larger matching. Simplicity and alternation use the checked graph API. -/
def Augments (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M N : Set (Edge G)) (root : L) (j : R) : Prop :=
  ∃ p : (graph G).Walk (.inl root) (.inr j),
    FiniteCombinatorics.Graph.Matching.IsAugmentingPath (graph G) (edgeSet M) p ∧
    (∀ d ∈ p.darts, SearchArc w u v M d.fst d.snd) ∧
    edgeSet N = FiniteCombinatorics.Graph.Matching.flipAlong (edgeSet M) p

/- Exact public definition types, separate from their expected values. -/
def LegalType := ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Set (Edge G) → Prop

def SearchArcType := ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Set (Edge G) → (L ⊕ R) → (L ⊕ R) → Prop

def ReachedType := ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Set (Edge G) → L → (L ⊕ R) → Prop

def leftReachType := ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Set (Edge G) → L → Set L

def rightReachType := ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Set (Edge G) → L → Set R

def StalledType := ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Set (Edge G) → L → Prop

def boundaryFunctionType := ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R}, (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Set (Edge G) → L → Set (Edge G)

def updateLeftType := ∀ {L : Type u}, (L → ℝ) → Set L → ℝ → L → ℝ

def updateRightType := ∀ {R : Type v}, (R → ℝ) → Set R → ℝ → R → ℝ

def rowWeightsType := ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], (Edge G → ℝ) → L → Finset ℝ

def initialLeftType := ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], (Edge G → ℝ) → L → ℝ

def minimumSlackFunctionType := ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Set (Edge G) → L → ℝ

def AugmentsType := ∀ {L : Type u} {R : Type v} {G : BipartiteGraph L R} [Fintype L] [Fintype R], (Edge G → ℝ) → (L → ℝ) → (R → ℝ) → Set (Edge G) → Set (Edge G) → L → R → Prop

/-- Initialization uses the maximum of each actual allowed row, with zero
right potentials and the empty matching, for arbitrary signed weights. -/
def initializationType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ),
    (∃ P : Set (Edge G), IsPerfectMatching P) →
    Legal w (initialLeft w) (fun _ => 0) ∅ ∧
    ∀ i, initialLeft w i ∈ rowWeights w i ∧ ∀ a ∈ rowWeights w i, a ≤ initialLeft w i

def augmentationType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) (root : L) (j : R),
    Legal w u v M → ¬ Covered M (.inl root) →
    j ∈ rightReach w u v M root → ¬ Covered M (.inr j) →
    ∃ N : Set (Edge G), Augments w u v M N root j ∧
      Legal w u v N ∧ Nat.card N = Nat.card M + 1

def reachedCardType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) (root : L),
    Legal w u v M → ¬ Covered M (.inl root) → Stalled w u v M root →
    Nat.card (leftReach w u v M root) = Nat.card (rightReach w u v M root) + 1

def boundaryType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) (root : L),
    (∃ P : Set (Edge G), IsPerfectMatching P) →
    Legal w u v M → ¬ Covered M (.inl root) → Stalled w u v M root →
    (boundary w u v M root).Nonempty ∧
    ∀ e ∈ boundary w u v M root, e ∉ M ∧ 0 < slack w u v e

def minimumSlackType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) (root : L),
    (∃ P : Set (Edge G), IsPerfectMatching P) →
    Legal w u v M → ¬ Covered M (.inl root) → Stalled w u v M root →
    0 < minimumSlack w u v M root ∧
    (∀ e ∈ boundary w u v M root, minimumSlack w u v M root ≤ slack w u v e) ∧
    ∃ e ∈ boundary w u v M root, minimumSlack w u v M root = slack w u v e

def updateType : Prop :=
  ∀ {L : Type u} {R : Type v} [Fintype L] [Fintype R]
    {G : BipartiteGraph L R} (w : Edge G → ℝ) (u : L → ℝ) (v : R → ℝ)
    (M : Set (Edge G)) (root : L),
    (∃ P : Set (Edge G), IsPerfectMatching P) →
    Legal w u v M → ¬ Covered M (.inl root) → Stalled w u v M root →
    let S := leftReach w u v M root
    let T := rightReach w u v M root
    let δ := minimumSlack w u v M root
    let u' := updateLeft u S δ
    let v' := updateRight v T δ
    Legal w u' v' M ∧
    (∀ x, Reached w u v M root x → Reached w u' v' M root x) ∧
    (∀ x y, Reached w u v M root x → SearchArc w u v M x y →
      SearchArc w u' v' M x y) ∧
    rightReach w u v M root ⊂ rightReach w u' v' M root

end Specs.P205.Matching.Hungarian
