import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.StrictDualSmoothness
import Mathlib.Analysis.Convex.Uniform
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Topology.MetricSpace.Bounded

/-! The uniform conclusions of `fa2:p2:duality-smoothness`.
The duality set is the shared normalized real continuous-linear duality set.
Boundedness and uniform continuity use the norm metrics on both spaces. -/
namespace ExpandedFA.BanachConvex.UniformDualSpec
open Set
universe u

/-- Both directions, for every real Banach space, including the zero space. -/
def Equivalence : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X],
    UniformConvexSpace (X →L[ℝ] ℝ) ↔
      ∃ J : X → (X →L[ℝ] ℝ),
        (∀ x, Spec.DualityMapValue X x = {J x}) ∧
        ∀ s : Set X, Bornology.IsBounded s → UniformContinuousOn J s

/-- Under the equivalent conditions, the quadratic is Fréchet C¹ with
its derivative equal to the (unique) duality selection at every point. -/
def FrechetC1 : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (J : X → (X →L[ℝ] ℝ)),
    (∀ x, Spec.DualityMapValue X x = {J x}) →
    (∀ s : Set X, Bornology.IsBounded s → UniformContinuousOn J s) →
    (∀ x, HasFDerivAt (fun z : X => ‖z‖ ^ 2 / 2) (J x) x) ∧
      ContDiff ℝ 1 (fun z : X => ‖z‖ ^ 2 / 2) ∧
      (∀ x, fderiv ℝ (fun z : X => ‖z‖ ^ 2 / 2) x = J x)
end ExpandedFA.BanachConvex.UniformDualSpec
