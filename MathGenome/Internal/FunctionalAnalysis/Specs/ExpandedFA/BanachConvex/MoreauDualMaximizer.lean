import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C06Conjugates
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Topology.MetricSpace.Bounded

/-! Dual maximization stage of `fa2:p2:banach-moreau`, paper.tex:8284–8339.
The primal infimum and conjugate use the full extended real line, while φ
has the established half-extended value type. No primal minimizer is selected. -/
namespace ExpandedFA.BanachConvex.Moreau
open P1.ExtendedConvexFunctions

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

noncomputable def primal (φ : ExtendedFunction X) (n : ℕ) (x : X) : EReal :=
  ⨅ y, P1.C06Conjugates.Spec.ExtendedRealValueValue (φ y) +
    ((n * ‖x - y‖ ^ 2 / 2 : ℝ) : EReal)

/-- The real envelope, used only after finiteness has been established. -/
noncomputable def envelope (φ : ExtendedFunction X) (n : ℕ) (x : X) : ℝ :=
  (primal φ n x).toReal

noncomputable def objective (φ : ExtendedFunction X) (n : ℕ) (x : X)
    (f : X →L[ℝ] ℝ) : EReal :=
  (f x : EReal) - P1.C06Conjugates.Spec.ConvexConjugateValue X φ f -
    ((‖f‖ ^ 2 / (2 * n) : ℝ) : EReal)

namespace Spec

def FiniteConvex : Prop :=
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [UniformConvexSpace (X →L[ℝ] ℝ)] (φ : ExtendedFunction X),
    P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue X φ →
    ∀ n : ℕ, 1 ≤ n →
      (∀ x, primal φ n x = (envelope φ n x : EReal)) ∧
      ConvexOn ℝ Set.univ (envelope φ n)

def ExactDual : Prop :=
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [UniformConvexSpace (X →L[ℝ] ℝ)] (φ : ExtendedFunction X),
    P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue X φ →
    ∀ n : ℕ, 1 ≤ n → ∀ x,
      primal φ n x = ⨆ f : X →L[ℝ] ℝ, objective φ n x f ∧
      ∃! f : X →L[ℝ] ℝ, objective φ n x f = primal φ n x

/-- A continuous selection of the unique maximizers, bounded on every
norm-bounded subset of the original real Banach space. -/
def MaximizerRegularity : Prop :=
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [UniformConvexSpace (X →L[ℝ] ℝ)] (φ : ExtendedFunction X),
    P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue X φ →
    ∀ n : ℕ, 1 ≤ n →
      ∃ S : X → (X →L[ℝ] ℝ),
        (∀ x f, objective φ n x f = primal φ n x ↔ f = S x) ∧
        Continuous S ∧
        ∀ s : Set X, Bornology.IsBounded s → Bornology.IsBounded (S '' s)

end Spec
end ExpandedFA.BanachConvex.Moreau
