import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.FunctionTopologies

/-! The finite-sampling conclusion, stated directly as finite nets for the
paper's metric D(f,g) = sup_x min(1,d(f(x),g(x))). Centers lie in A.
There is no separation condition on X and no completeness condition on Y. -/
namespace Specs.D10Topology.Ch13.FiniteSampling
open Set
universe u v

def finite_sampling : Prop :=
  ∀ {X : Type u} {Y : Type v} [TopologicalSpace X] [CompactSpace X] [MetricSpace Y]
    (A : Set (FunctionTopologies.ContinuousMaps X Y)),
    FunctionTopologies.Equicontinuous A →
    (∀ x : X, TotallyBounded ((fun f : FunctionTopologies.ContinuousMaps X Y => f x) '' A)) →
    ∀ ε : ℝ, 0 < ε →
      ∃ F : Set (FunctionTopologies.ContinuousMaps X Y), F.Finite ∧ F ⊆ A ∧
        ∀ f ∈ A, ∃ g ∈ F,
          FunctionTopologies.uniformDistance (f : X → Y) (g : X → Y) < ε

end Specs.D10Topology.Ch13.FiniteSampling
