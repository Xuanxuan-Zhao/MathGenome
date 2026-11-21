import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.SmoothConstraintModels
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The unconditional part of `paper.tex`, Theorem `thm:fritz-john`
(lines 2864–2874), in the finite-dimensional C¹ setting of §v06-03.
The open domain belongs to feasibility. Both finite constraint families can be empty.
The conclusion uses the shared Fritz John system, including complementarity and
joint nonzeroness; no qualification is assumed. -/

universe u v w
namespace VariationalNotes.Ch06.FritzJohnSpecs

def fritzJohn : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    Specs.SmoothConstraintData U f g h → x ∈ Specs.feasibleSet U g h →
    IsLocalMinOn f (Specs.feasibleSet U g h) x →
    ∃ (lam0 : ℝ) (lam : I → ℝ) (nu : J → ℝ),
      Specs.FritzJohn U f g h x lam0 lam nu

end VariationalNotes.Ch06.FritzJohnSpecs
