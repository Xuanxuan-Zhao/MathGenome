import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.SmoothConstraintModels
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.LocalExtr

/-! Independent specifications for `paper.tex`, Theorem
`thm:licq-second-order-necessity`, §v06-06. The domain is part of
feasibility. Index types and the ambient finite-dimensional space may be empty
or zero-dimensional. The critical cone is the shared full critical cone. -/

noncomputable section
universe u v w
namespace VariationalNotes.Ch06.SecondOrderNecessitySpecs
open Specs

/-- Every KKT pair at a C² constrained minimum satisfying LICQ has a
nonnegative Lagrangian Hessian on the entire critical cone. -/
def secondOrderNecessary_of_licq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ)
    (x : X) (lam : I → ℝ) (nu : J → ℝ),
    IsOpen U → ContDiffOn ℝ 2 f U →
    (∀ i, ContDiffOn ℝ 2 (g i) U) → (∀ j, ContDiffOn ℝ 2 (h j) U) →
    IsLocalMinOn f (feasibleSet U g h) x → LICQ U g h x →
    KKT U f g h x lam nu → ∀ d ∈ criticalCone f g h x,
      0 ≤ fderiv ℝ (fderiv ℝ (lagrangian f g h lam nu)) x d d

/-- The unique KKT pair exists under exactly the stated hypotheses and
satisfies the second-order conclusion; uniqueness compares all KKT pairs. -/
def existsUnique_secondOrder_kkt_of_licq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    IsOpen U → ContDiffOn ℝ 2 f U →
    (∀ i, ContDiffOn ℝ 2 (g i) U) → (∀ j, ContDiffOn ℝ 2 (h j) U) →
    IsLocalMinOn f (feasibleSet U g h) x → LICQ U g h x →
    ∃ p : (I → ℝ) × (J → ℝ), KKT U f g h x p.1 p.2 ∧
      (∀ q : (I → ℝ) × (J → ℝ), KKT U f g h x q.1 q.2 → q = p) ∧
      ∀ d ∈ criticalCone f g h x,
        0 ≤ fderiv ℝ (fderiv ℝ (lagrangian f g h p.1 p.2)) x d d

end VariationalNotes.Ch06.SecondOrderNecessitySpecs
