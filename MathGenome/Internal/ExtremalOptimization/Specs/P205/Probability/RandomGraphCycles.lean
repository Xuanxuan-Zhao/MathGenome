import MathGenome.Internal.ExtremalOptimization.Specs.P205.Probability.FiniteModels
import Mathlib.Combinatorics.SimpleGraph.CycleGraph
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! The independent-edge experiment and unoriented short cycles in the first
stage of paper.tex, Theorem p205:W24. A potential cycle is the edge set of
an injectively labelled cycle graph. Taking an image of a finite set removes
all repetitions arising from changing the starting vertex or direction.
Extra ambient edges are allowed: these are subgraph cycles, not induced cycles. -/

open MeasureTheory
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

namespace P205.Probability.RandomGraphCycles

abbrev Edge (n : ℕ) := (⊤ : SimpleGraph (Fin n)).edgeSet
noncomputable instance edgeDecidableEq (n : ℕ) : DecidableEq (Edge n) :=
  fun a b => Classical.propDecidable (a = b)

abbrev Outcome (n : ℕ) := Edge n → Bool

noncomputable def parameter (g n : ℕ) : ℝ :=
  (n : ℝ) ^ (-1 + 1 / (2 * (g : ℝ)))

/-- This elementary fact makes the canonical experiment well-defined. -/
lemma parameter_valid {g n : ℕ} (hg : 3 ≤ g) (hn : 1 ≤ n) :
    parameter g n ∈ Set.Icc (0 : ℝ) 1 := by
  have hg' : (3 : ℝ) ≤ g := by exact_mod_cast hg
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨Real.rpow_nonneg (by positivity) _, ?_⟩
  apply Real.rpow_le_one_of_one_le_of_nonpos hn'
  have : 1 / (2 * (g : ℝ)) ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  linarith

noncomputable def bernoulli (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    FiniteModel Bool where
  weight b := if b then p else 1 - p
  weight_nonneg b := by cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith [hp.1, hp.2]
  weight_sum := by simp

noncomputable def model (g n : ℕ) (hg : 3 ≤ g) (hn : 1 ≤ n) : FiniteModel (Outcome n) :=
  FiniteModel.pi (fun _ : Edge n => bernoulli (parameter g n) (parameter_valid hg hn))

/-- Decode the independent bits into a simple undirected graph. -/
noncomputable def graph {n : ℕ} (ω : Outcome n) : SimpleGraph (Fin n) :=
  SimpleGraph.fromEdgeSet {e | ∃ h : e ∈ (⊤ : SimpleGraph (Fin n)).edgeSet, ω ⟨e, h⟩ = true}

/-- The edges of a graph, viewed inside the fixed universe of possible edges. -/
noncomputable def graphEdges {n : ℕ} (H : SimpleGraph (Fin n)) : Finset (Edge n) :=
  H.edgeFinset.attach.map
    ⟨fun (e : {e // e ∈ H.edgeFinset}) => ⟨e.val, SimpleGraph.edgeSet_mono (show H ≤ ⊤ from le_top) (SimpleGraph.mem_edgeFinset.mp e.property)⟩,
      fun _a _b h => Subtype.ext (congrArg (fun e : Edge n => e.val) h)⟩

/-- Unoriented simple cycles of a given length in the complete graph. -/
noncomputable def cycles (n l : ℕ) : Finset (Finset (Edge n)) :=
  Finset.univ.image (fun f : Fin l ↪ Fin n => graphEdges ((SimpleGraph.cycleGraph l).map f))

def occurs {n : ℕ} (S : Finset (Edge n)) : Set (Outcome n) :=
  {ω | ∀ e ∈ S, ω e = true}

/-- Each distinct edge set contributes exactly one indicator. -/
noncomputable def count (g n : ℕ) (ω : Outcome n) : ℝ :=
  ∑ l ∈ Finset.Icc 3 g, ∑ S ∈ cycles n l, (occurs S).indicator (fun _ => (1 : ℝ)) ω

end P205.Probability.RandomGraphCycles

namespace Specs.P205.Probability.RandomGraphCycles
open _root_.P205.Probability.RandomGraphCycles

def ParameterInUnitInterval : Prop := ∀ g n : ℕ, 3 ≤ g → 1 ≤ n →
  parameter g n ∈ Set.Icc (0 : ℝ) 1

def IndependentEdges : Prop := ∀ (g n : ℕ) (hg : 3 ≤ g) (hn : 1 ≤ n),
  ProbabilityTheory.iIndepFun (fun e (ω : Outcome n) => ω e) (model g n hg hn).measure

def EdgeMarginal : Prop := ∀ (g n : ℕ) (hg : 3 ≤ g) (hn : 1 ≤ n) (e : Edge n),
  (model g n hg hn).eventMass {ω | ω e = true} = parameter g n

/-- The real indicator sum is the cardinal count of the distinct cycle edge
sets contained in the decoded graph, summed over precisely the stated lengths. -/
def CountMeaning : Prop := ∀ (g n : ℕ) (ω : Outcome n),
  count g n ω = ∑ l ∈ Finset.Icc 3 g,
    (((cycles n l).filter (fun S => ∀ e ∈ S, e.val ∈ (graph ω).edgeSet)).card : ℝ)

/-- Potential cycles occur exactly when the sampled graph contains a simple
closed walk of that length. This also checks completeness of the representation. -/
def CycleMeaning : Prop := ∀ (n l : ℕ), 3 ≤ l → ∀ ω : Outcome n,
  (∃ S ∈ cycles n l, ω ∈ occurs S) ↔
    ∃ (v : Fin n) (w : (graph ω).Walk v v), w.IsCycle ∧ w.length = l

def ExpectedShortCycles : Prop := ∀ (g n : ℕ) (hg : 3 ≤ g) (hn : 1 ≤ n),
  (model g n hg hn).expectation (count g n) ≤ (g : ℝ) * Real.sqrt n

def ShortCycleTail : Prop := ∀ (g n : ℕ) (hg : 3 ≤ g) (hn : 1 ≤ n),
  (model g n hg hn).eventMass {ω | (n : ℝ) / 2 ≤ count g n ω} ≤
    2 * (g : ℝ) / Real.sqrt n

end Specs.P205.Probability.RandomGraphCycles
