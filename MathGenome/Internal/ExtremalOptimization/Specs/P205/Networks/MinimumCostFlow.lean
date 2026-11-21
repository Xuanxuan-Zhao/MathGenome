import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.ResidualCycleOptimality
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.NegativeCyclePotentials
import MathGenome.Internal.ExtremalOptimization.Specs.P205.Networks.BoundedFlowIntegrality

/-! W39: the three equivalent certificates and integral existence.
The residual graph contains exactly the strictly positive labelled copies.
No nonnegativity assumption is made on lower bounds or costs. -/

universe u v
namespace P205.Networks.MinimumCostFlowSpecs
open FiniteCombinatorics.Directed

def certificates : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℝ) (b : V → ℝ) (w f : A → ℝ),
    BoundedSpec.Feasible G lo hi b f →
    (CycleSpec.Optimal G lo hi b w f ↔ CycleSpec.NoNegativeCycles G lo hi f w) ∧
    (CycleSpec.NoNegativeCycles G lo hi f w ↔
      ∃ π : V → ℝ, ∀ r : BoundedSpec.ResidualArc lo hi f,
        0 ≤ BoundedSpec.cost w r.val + π ((BoundedSpec.graph G lo hi f).tail r) -
          π ((BoundedSpec.graph G lo hi f).head r))

def integral_minimum : Prop :=
  ∀ {V : Type u} {A : Type v} [Fintype V] [Fintype A]
    (G : Digraph V A) (lo hi : A → ℤ) (b : V → ℤ) (w : A → ℝ),
    (∃ f : A → ℝ, BoundedSpec.Feasible G (fun a => (lo a : ℝ))
      (fun a => (hi a : ℝ)) (fun x => (b x : ℝ)) f) →
    ∃ f : A → ℝ,
      BoundedSpec.Feasible G (fun a => (lo a : ℝ))
        (fun a => (hi a : ℝ)) (fun x => (b x : ℝ)) f ∧
      (∀ a, ∃ z : ℤ, f a = (z : ℝ)) ∧
      CycleSpec.Optimal G (fun a => (lo a : ℝ))
        (fun a => (hi a : ℝ)) (fun x => (b x : ℝ)) w f

end P205.Networks.MinimumCostFlowSpecs
