import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Topology.Instances.Real.Lemmas

/-! Independent statements for paper.tex, Theorem 1.5 (W04).
The extremal number is Mathlib's maximum over graphs avoiding injective
adjacency-preserving copies. Thus extra ambient edges are allowed.
No connectedness assumption is imposed, and isolated vertices are retained.
For a finite graph, `chromaticNumber.toNat` is its finite chromatic number. -/
namespace P205.Extremal.ErdosStoneSimonovitsSpecs

open SimpleGraph Filter
open scoped Topology

def densityStatement : Prop :=
  ∀ {W : Type*} [Fintype W] (H : SimpleGraph W), H ≠ ⊥ →
    Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n.choose 2 : ℝ))
      atTop (𝓝 (1 - 1 / ((H.chromaticNumber.toNat : ℝ) - 1)))

def bipartiteStatement : Prop :=
  ∀ {W : Type*} [Fintype W] (H : SimpleGraph W), H ≠ ⊥ → H.IsBipartite →
    Tendsto (fun n : ℕ => (extremalNumber n H : ℝ) / (n.choose 2 : ℝ))
      atTop (𝓝 0)

end P205.Extremal.ErdosStoneSimonovitsSpecs
