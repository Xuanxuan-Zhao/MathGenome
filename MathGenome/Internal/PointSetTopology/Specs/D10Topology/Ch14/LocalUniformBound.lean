import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch14.CategoryInterface
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Independent statement of `paper.tex`, `d10:14:local-uniform-boundedness`.
The family consists of continuous real-valued functions and may be empty.
Pointwise bounds may depend on the point; the resulting integer bound holds
on one nonempty open subset of the specified ambient space.
-/

open Set
universe u

namespace Specs.D10Topology.Ch14.LocalUniformBound

def local_uniform_bound : Prop :=
  ∀ {X : Type u} [TopologicalSpace X] [Nonempty X],
    Specs.D10Topology.Ch14.CategoryInterface.baireValue X →
    ∀ A : Set C(X, ℝ),
      (∀ x : X, ∃ b : ℝ, ∀ f ∈ A, |f x| ≤ b) →
      ∃ U : Set X, IsOpen U ∧ U.Nonempty ∧
        ∃ M : ℤ, 1 ≤ M ∧ ∀ f ∈ A, ∀ x ∈ U, |f x| ≤ (M : ℝ)

end Specs.D10Topology.Ch14.LocalUniformBound
