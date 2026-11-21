import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch07.SeparationConventions

/-!
Independent statements for paper.tex, d10:07:urysohn and d10:07:t4-tychonoff.
The unit interval carries its usual real subspace topology. Normality has no
T1 assumption. The space and either prescribed closed set may be empty.
-/

open Set
universe u

namespace Specs.D10Topology.Ch07.UrysohnSeparation

def normal_iff_urysohn : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], NormalSpace X ↔
    ∀ A B : Set X, IsClosed A → IsClosed B → Disjoint A B →
      ∃ f : X → unitInterval, Continuous f ∧
        (∀ x ∈ A, f x = 0) ∧ (∀ x ∈ B, f x = 1)

def normal_closed_open_function : Prop :=
  ∀ (X : Type u) [TopologicalSpace X], NormalSpace X →
    ∀ F U : Set X, IsClosed F → IsOpen U → F ⊆ U →
      ∃ f : X → unitInterval, Continuous f ∧
        (∀ x ∈ F, f x = 1) ∧ (∀ x ∈ Uᶜ, f x = 0)

def t4_implies_tychonoff : Prop :=
  ∀ (X : Type u) [TopologicalSpace X],
    SeparationConventions.t4Value X → SeparationConventions.tychonoffValue X

end Specs.D10Topology.Ch07.UrysohnSeparation
