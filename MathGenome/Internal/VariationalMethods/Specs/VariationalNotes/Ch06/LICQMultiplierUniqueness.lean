import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Ch06.SmoothConstraintModels
import Mathlib.Topology.Order.LocalExtr
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
The LICQ clause of `prop:qualified-multiplier-sets`, paper.tex §v06-05.
All multipliers are normalized by the objective coefficient one in the shared KKT
system. The finite index families may be empty. Uniqueness itself is algebraic;
existence uses the finite-dimensional C¹ constrained local minimum hypotheses.
-/
universe u v w
namespace VariationalNotes.Ch06.LICQMultiplierUniquenessSpecs
open Specs

/-- Any two full KKT pairs agree under LICQ. No regularity is needed for this
algebraic implication concerning the actual differentials. -/
def kkt_multipliers_unique_of_licq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X)
    (lam lam' : I → ℝ) (nu nu' : J → ℝ),
    LICQ U g h x → KKT U f g h x lam nu → KKT U f g h x lam' nu' →
    lam = lam' ∧ nu = nu'

/-- Existence of a unique full pair, with all inactive coefficients zero. The
last clause compares the witness against every KKT pair, not just active ones. -/
def existsUnique_kkt_of_licq : Prop :=
  ∀ {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {I : Type v} {J : Type w} [Fintype I] [Fintype J]
    (U : Set X) (f : X → ℝ) (g : I → X → ℝ) (h : J → X → ℝ) (x : X),
    SmoothConstraintData U f g h → IsLocalMinOn f (feasibleSet U g h) x →
    LICQ U g h x →
    ∃ p : (I → ℝ) × (J → ℝ),
      KKT U f g h x p.1 p.2 ∧
      (∀ i, i ∉ activeSet g x → p.1 i = 0) ∧
      ∀ q : (I → ℝ) × (J → ℝ), KKT U f g h x q.1 q.2 → q = p

end VariationalNotes.Ch06.LICQMultiplierUniquenessSpecs
