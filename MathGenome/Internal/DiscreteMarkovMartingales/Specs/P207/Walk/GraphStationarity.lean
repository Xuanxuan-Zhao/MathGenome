import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.TimeReversal
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! The stationary/reversible assertions of paper.tex, §4.5, graph-walk theorem.
`Nontrivial V` is precisely the assumption of at least two vertices. Degrees
and the edge count below are those of the given undirected simple graph. -/

open scoped ENNReal
universe u
namespace P207.Walk
open P207.Markov
noncomputable section

variable {V : Type u} [Fintype V] [Nontrivial V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private lemma positive_degree (hG : G.Connected) (v : V) : 0 < G.degree v :=
  hG.preconnected.degree_pos_of_nontrivial v

private lemma positive_edges (hG : G.Connected) : 0 < G.edgeFinset.card := by
  exact lt_of_lt_of_le (positive_degree G hG (Classical.arbitrary V))
    (G.degree_le_card_edgeFinset (Classical.arbitrary V))

/-- The neighbor-uniform stochastic matrix, in the shared PMF representation. -/
def neighborKernel (hG : G.Connected) : StochasticMatrix V := fun v =>
  PMF.ofFintype (fun w => if G.Adj v w then (G.degree v : ℝ≥0∞)⁻¹ else 0) (by
    classical
    have hcard : (Finset.univ.filter (G.Adj v)).card = G.degree v := by
      rw [← G.card_neighborFinset_eq_degree]
      congr 1
      ext w
      simp
    rw [← Finset.sum_filter, Finset.sum_const, hcard, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by exact_mod_cast (positive_degree G hG v).ne')
      (by simp))

/-- Degree-proportional probability; its denominator is twice the actual
number of unordered edges, by the degree-sum formula. -/
def degreeLaw (hG : G.Connected) : ProbabilityLaw V :=
  PMF.ofFintype
    (fun v => (G.degree v : ℝ≥0∞) / ((2 * G.edgeFinset.card : ℕ) : ℝ≥0∞)) (by
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      have hsum : ∑ v, (G.degree v : ℝ≥0∞) = ((2 * G.edgeFinset.card : ℕ) : ℝ≥0∞) := by
        exact_mod_cast G.sum_degrees_eq_twice_card_edges
      rw [hsum]
      exact ENNReal.mul_inv_cancel (by exact_mod_cast (Nat.mul_pos (by decide) (positive_edges G hG)).ne')
        (ENNReal.natCast_ne_top _))

namespace GraphStationaritySpec

def neighborKernelType := {V : Type u} → [Fintype V] → [Nontrivial V] →
  (G : SimpleGraph V) → [DecidableRel G.Adj] → G.Connected → StochasticMatrix V
def neighborKernelValue : neighborKernelType.{u} := @neighborKernel

def degreeLawType := {V : Type u} → [Fintype V] → [Nontrivial V] →
  (G : SimpleGraph V) → [DecidableRel G.Adj] → G.Connected → ProbabilityLaw V
def degreeLawValue : degreeLawType.{u} := @degreeLaw

def degree_pos : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
  (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → ∀ v, 0 < G.degree v

def edge_count_pos : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
  (G : SimpleGraph V) [DecidableRel G.Adj], G.Connected → 0 < G.edgeFinset.card

def neighborKernel_apply : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (v w : V),
  neighborKernel G hG v w = if G.Adj v w then 1 / (G.degree v : ℝ≥0∞) else 0

def neighborKernel_row_sum : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (v : V),
  ∑' w, neighborKernel G hG v w = 1

def neighborKernel_irreducible : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected),
  Irreducible (neighborKernel G hG)

def degreeLaw_apply : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (v : V),
  degreeLaw G hG v = (G.degree v : ℝ≥0∞) / ((2 * G.edgeFinset.card : ℕ) : ℝ≥0∞)

def degreeLaw_sum : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected),
  ∑' v, degreeLaw G hG v = 1

def detailed_balance : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected),
  DetailedBalance (neighborKernel G hG) (degreeLaw G hG)

def stationary : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected),
  IsStationary (neighborKernel G hG) (degreeLaw G hG)

def reversible : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
  [MeasurableSpace V] [DiscreteMeasurableSpace V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected),
  IsReversible (neighborKernel G hG) (degreeLaw G hG)

def stationary_unique : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
  [MeasurableSpace V] [DiscreteMeasurableSpace V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (ρ : ProbabilityLaw V),
  IsStationary (neighborKernel G hG) ρ → ρ = degreeLaw G hG

end GraphStationaritySpec
end
end P207.Walk
