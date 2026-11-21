import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-!
Independent statements of paper.tex, d10:07:zero-sets.
Normality does not include T1. The codomain is the usual real unit interval;
the equalities prescribe entire fibers, including for empty prescribed sets
and the empty underlying space.
-/

open Set
universe u

namespace Specs.D10Topology.Ch07.NormalZeroSets

/-- A closed set in a normal space is G_delta exactly when it is a zero fiber. -/
def closed_gdelta_iff_zero_fiber : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], NormalSpace X →
    ∀ A : Set X, IsClosed A →
      (IsGδ A ↔ ∃ g : X → unitInterval, Continuous g ∧ g ⁻¹' {0} = A)

/-- If all closed sets are G_delta, both Urysohn fibers can be exact. -/
def normal_exact_zero_one_fibers : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], NormalSpace X →
    (∀ F : Set X, IsClosed F → IsGδ F) →
    ∀ A B : Set X, IsClosed A → IsClosed B → Disjoint A B →
      ∃ f : X → unitInterval, Continuous f ∧ f ⁻¹' {0} = A ∧ f ⁻¹' {1} = B

end Specs.D10Topology.Ch07.NormalZeroSets
