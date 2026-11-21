import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Independent statements of paper.tex, d10:17:brouwer-convex.
The subsets carry their induced topology. No interior, affine dimension,
preferred norm, or positive dimension hypothesis is imposed. -/
namespace Specs.D10Topology.Ch17.BrouwerConvex

def brouwer_euclidean : Prop :=
  ∀ (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin m))),
    K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ f : K → K, Continuous f → ∃ x, f x = x

universe u

def brouwer_finiteDimensional : Prop :=
  ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (K : Set V),
    K.Nonempty → IsCompact K → Convex ℝ K →
    ∀ f : K → K, Continuous f → ∃ x, f x = x

end Specs.D10Topology.Ch17.BrouwerConvex
