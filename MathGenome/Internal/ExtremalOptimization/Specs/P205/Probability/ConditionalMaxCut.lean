import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.ConditionalSelection
import Mathlib.Combinatorics.SimpleGraph.Finite

open scoped BigOperators Classical

namespace P205.Probability.ConditionalMaxCut

/-- The coordinate distribution used for independent fair vertex colors. -/
noncomputable def fairBit : FiniteModel Bool where
  weight _ := 1 / 2
  weight_nonneg _ := by norm_num
  weight_sum := by norm_num [Fintype.sum_bool]

noncomputable def fairModel (V : Type*) [Fintype V] : FiniteModel (V → Bool) :=
  FiniteModel.pi (fun _ : V => fairBit)

variable {V : Type*} [Fintype V]

/-- Each unordered edge contributes once. -/
noncomputable def edgeIndicator (c : V → Bool) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun a b => if c a ≠ c b then 1 else 0,
    fun a b => by simp only [ne_comm]⟩

noncomputable def cutEdges (G : SimpleGraph V) (c : V → Bool) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => edgeIndicator c e = 1)

noncomputable def cutObjective (G : SimpleGraph V) (c : V → Bool) : ℝ :=
  ∑ e ∈ G.edgeFinset, edgeIndicator c e

/-- A partial coloring specifies colors on an arbitrary revealed vertex set. -/
noncomputable def partialCell (S : Finset V) (c : V → Bool) : Finset (V → Bool) :=
  Finset.univ.filter (fun d => ∀ v ∈ S, d v = c v)

noncomputable def edgeMean (S : Finset V) (c : V → Bool) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun a b => if a ∈ S ∧ b ∈ S then
      (if c a ≠ c b then 1 else 0) else 1 / 2,
    fun a b => by simp only [and_comm, ne_comm]⟩

noncomputable def potential (G : SimpleGraph V) (S : Finset V) (c : V → Bool) : ℝ :=
  ∑ e ∈ G.edgeFinset, edgeMean S c e

/-- Every such cell is proved positive; the ratio uses the upstream moment and mass. -/
noncomputable def conditionalCut (G : SimpleGraph V) (S : Finset V) (c : V → Bool) : ℝ :=
  ConditionalSelection.cellMoment (fairModel V) (cutObjective G) (partialCell S c) /
    ConditionalSelection.cellMass (fairModel V) (partialCell S c)

/-- The first i vertices of an arbitrary enumeration; n = 0 is allowed. -/
noncomputable def revealed {n : ℕ} (e : Fin n ≃ V) (i : ℕ) : Finset V :=
  Finset.univ.filter (fun v => (e.symm v).val < i)

end ConditionalMaxCut

namespace ConditionalMaxCutSpec
open ConditionalMaxCut ConditionalSelection

def cutCount : Prop := ∀ {V : Type*} [Fintype V] (G : SimpleGraph V) (c : V → Bool),
  cutObjective G c = ((cutEdges G c).card : ℝ)

def partialPositive : Prop := ∀ {V : Type*} [Fintype V]
  (S : Finset V) (c : V → Bool), 0 < cellMass (fairModel V) (partialCell S c)

def conditionalEdge : Prop := ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
  (S : Finset V) (c : V → Bool) (e : Sym2 V), e ∈ G.edgeFinset →
  cellMoment (fairModel V) (fun d => edgeIndicator d e) (partialCell S c) /
    cellMass (fairModel V) (partialCell S c) = edgeMean S c e

def conditionalFormula : Prop := ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
  (S : Finset V) (c : V → Bool), conditionalCut G S c = potential G S c

def initialExpectation : Prop := ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
  (fairModel V).expectation (cutObjective G) = (G.edgeFinset.card : ℝ) / 2

def chooseBit : Prop := ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
  (S : Finset V) (c : V → Bool) (v : V), v ∉ S →
  ∃ b : Bool, potential G S c ≤ potential G (insert v S) (Function.update c v b)

/-- Successive vertex choices give nested positive cells and nondecreasing conditional
means, terminating at a cut with at least half of all edges. The input equivalence
allows every vertex order, and includes the empty revelation sequence. -/
def successiveChoices : Prop := ∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
  (n : ℕ) (e : Fin n ≃ V),
  ∃ c : ℕ → (V → Bool), c 0 = (fun _ => false) ∧
    (∀ i (hi : i < n), ∃ b : Bool, c (i + 1) = Function.update (c i) (e ⟨i, hi⟩) b) ∧
    (∀ i, i < n → partialCell (revealed e (i + 1)) (c (i + 1)) ⊆
        partialCell (revealed e i) (c i) ∧
      0 < cellMass (fairModel V) (partialCell (revealed e i) (c i)) ∧
      conditionalCut G (revealed e i) (c i) ≤
        conditionalCut G (revealed e (i + 1)) (c (i + 1))) ∧
    partialCell (revealed e n) (c n) = {c n} ∧
    0 < (fairModel V).weight (c n) ∧
    conditionalCut G (revealed e n) (c n) = ((cutEdges G (c n)).card : ℝ) ∧
    (G.edgeFinset.card : ℝ) / 2 ≤ ((cutEdges G (c n)).card : ℝ)

def existsCut : Prop := ∀ {V : Type*} [Fintype V] (G : SimpleGraph V),
  ∃ c : V → Bool, (G.edgeFinset.card : ℝ) / 2 ≤ ((cutEdges G c).card : ℝ)

end ConditionalMaxCutSpec
end P205.Probability
