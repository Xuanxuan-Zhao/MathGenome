import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.MoreauDualMaximizer
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-! Independent statements for `fa2:p2:banach-moreau`, paper.tex:8290–8306.
The source's integer n ≥ 1 is indexed by n + 1 in the approximation sequence.
The infimum is the shared EReal-valued primal; the finite envelope is its
shared real representative. Thus convergence retains the value +∞. -/
namespace ExpandedFA.BanachConvex.Moreau.BanachSpec
open P1.ExtendedConvexFunctions
open Filter
open scoped Topology

/-- Finiteness, convexity, Fréchet C¹ regularity, and identification of the
continuous derivative with the unique dual maximizer. No primal minimizer is
chosen and no strict convexity of the primal space is assumed. -/
def Regularity : Prop :=
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [UniformConvexSpace (X →L[ℝ] ℝ)] (φ : ExtendedFunction X),
    P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue X φ →
    ∀ n : ℕ, 1 ≤ n →
      (∀ x, primal φ n x = (envelope φ n x : EReal)) ∧
      ConvexOn ℝ Set.univ (envelope φ n) ∧
      ContDiff ℝ 1 (envelope φ n) ∧
      ∃ S : X → (X →L[ℝ] ℝ), Continuous S ∧
        (∀ x, HasFDerivAt (envelope φ n) (S x) x) ∧
        (∀ x, fderiv ℝ (envelope φ n) x = S x) ∧
        (∀ x, primal φ n x = ⨆ f : X →L[ℝ] ℝ, objective φ n x f) ∧
        (∀ x f, objective φ n x f = primal φ n x ↔ f = S x)

/-- Monotone approximation at all points, with both the supremum and the
order-topological limit specified, including points outside the finite domain. -/
def Approximation : Prop :=
  ∀ (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [UniformConvexSpace (X →L[ℝ] ℝ)] (φ : ExtendedFunction X),
    P1.ExtendedConvexFunctions.Spec.ProperValue X φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue X φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue X φ →
    ∀ x : X,
      Monotone (fun k : ℕ => primal φ (k + 1) x) ∧
      (∀ k : ℕ, primal φ (k + 1) x ≤
        P1.C06Conjugates.Spec.ExtendedRealValueValue (φ x)) ∧
      (⨆ k : ℕ, primal φ (k + 1) x) =
        P1.C06Conjugates.Spec.ExtendedRealValueValue (φ x) ∧
      Tendsto (fun k : ℕ => primal φ (k + 1) x) atTop
        (𝓝 (P1.C06Conjugates.Spec.ExtendedRealValueValue (φ x)))

end ExpandedFA.BanachConvex.Moreau.BanachSpec
