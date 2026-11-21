import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Walk.GraphStationarity
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.AperiodicMixing
import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Markov.PeriodicLimits
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Period and mixing assertions of paper.tex, W24. The graph is finite,
connected, undirected and simple, with at least two vertices. The original
neighbor kernel is not made lazy in the period classification. A coloring
by Fin 2 specifies the two ordered parts of a bipartition. -/

open Filter
open scoped ENNReal Topology Classical
universe u
namespace P207.Walk
open P207.Markov
noncomputable section

/-- The actual convex combination α I + (1-α) P, for every real 0 < α < 1. -/
def lazyKernel {S : Type u} (P : StochasticMatrix S)
    (α : ℝ) (hα₀ : 0 < α) (hα₁ : α < 1) : StochasticMatrix S :=
  fun i => ⟨fun j => ENNReal.ofReal α * PMF.pure i j + ENNReal.ofReal (1-α) * P i j,
    ENNReal.summable.hasSum_iff.mpr (by
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
        (PMF.pure i).tsum_coe, (P i).tsum_coe, mul_one, mul_one,
        ← ENNReal.ofReal_add hα₀.le (by linarith)]
      simp)⟩

namespace GraphPeriodMixingSpec

def lazyKernelType := {S : Type u} → StochasticMatrix S →
  (α : ℝ) → 0 < α → α < 1 → StochasticMatrix S
def lazyKernelValue : lazyKernelType.{u} := @P207.Walk.lazyKernel

def lazyKernel_apply : Prop := ∀ {S : Type u} (P : StochasticMatrix S)
    (α : ℝ) (h₀ : 0 < α) (h₁ : α < 1) (i j : S),
  lazyKernel P α h₀ h₁ i j =
    ENNReal.ofReal α * (if j = i then 1 else 0) + ENNReal.ofReal (1-α) * P i j

def period_two_iff_bipartite : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (v : V),
  period (neighborKernel G hG) v = 2 ↔ G.IsBipartite

def period_one_of_nonbipartite : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected),
  ¬ G.IsBipartite → ∀ v, period (neighborKernel G hG) v = 1

def nonbipartite_mixing : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected),
  ¬ G.IsBipartite → ∀ ν : ProbabilityLaw V,
    Tendsto (fun n => totalVariation (evolve ν (neighborKernel G hG) n) (degreeLaw G hG))
      atTop (𝓝 0)

/-- Each part has half the stationary mass. Point starts alternate parts.
For r=0,1 the residue limit is twice π on the corresponding part. -/
def bipartite_limits : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (c : G.Coloring (Fin 2)),
  (∀ l, lawEvent (degreeLaw G hG) {v | c v = l} = 1 / (2 : ℝ≥0∞)) ∧
  (∀ (i : V) (n : ℕ), lawEvent (power (neighborKernel G hG) n i)
    {v | (c v).val = ((c i).val + n) % 2} = 1) ∧
  ∃ μ : Fin 2 → ProbabilityLaw V,
    (∀ l v, μ l v = if c v = l then (2 : ℝ≥0∞) * degreeLaw G hG v else 0) ∧
    ∀ (i : V) (r : Fin 2),
      Tendsto (fun m => totalVariation (power (neighborKernel G hG) (m*2+r.val) i)
        (μ ⟨((c i).val+r.val) % 2, Nat.mod_lt _ (by decide)⟩)) atTop (𝓝 0)

def cesaro_mixing : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (ν : ProbabilityLaw V),
  Tendsto (fun n => totalVariation (cesaroLaw ν (neighborKernel G hG) n) (degreeLaw G hG))
    atTop (𝓝 0)

def lazy_stationary : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (α : ℝ) (h₀ : 0 < α) (h₁ : α < 1),
  IsStationary (lazyKernel (neighborKernel G hG) α h₀ h₁) (degreeLaw G hG)

def lazy_irreducible : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (α : ℝ) (h₀ : 0 < α) (h₁ : α < 1),
  Irreducible (lazyKernel (neighborKernel G hG) α h₀ h₁)

def lazy_aperiodic : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (α : ℝ) (h₀ : 0 < α) (h₁ : α < 1),
  ∀ v, Aperiodic (lazyKernel (neighborKernel G hG) α h₀ h₁) v

def lazy_mixing : Prop := ∀ {V : Type u} [Fintype V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected)
    (α : ℝ) (h₀ : 0 < α) (h₁ : α < 1) (ν : ProbabilityLaw V),
  Tendsto (fun n => totalVariation (evolve ν (lazyKernel (neighborKernel G hG) α h₀ h₁) n)
    (degreeLaw G hG)) atTop (𝓝 0)

end GraphPeriodMixingSpec
end
end P207.Walk
