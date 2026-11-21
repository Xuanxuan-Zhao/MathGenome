import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.BanachConvex.Definitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Independent statements for the strict-dual part of
`fa2:p2:duality-smoothness`, paper.tex:8204–8252.
All functionals are continuous real-linear functionals. A selection is specified
by equality with the original duality set; no differentiability or continuity
is built into that hypothesis. -/
namespace ExpandedFA.BanachConvex.StrictDualSpec
open Filter Set
open scoped Topology
universe u v

/-- Every normalized duality set is a singleton. -/
def SingleValued : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [StrictConvexSpace ℝ (X →L[ℝ] ℝ)],
    ∃ J : X → (X →L[ℝ] ℝ), ∀ x, Spec.DualityMapValue X x = {J x}

/-- Gâteaux differentiability with the continuous linear functional Jx as derivative. -/
def GateauxDifferentiability : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [StrictConvexSpace ℝ (X →L[ℝ] ℝ)]
    (J : X → (X →L[ℝ] ℝ)), (∀ x, Spec.DualityMapValue X x = {J x}) →
    ∀ x v, HasDerivAt (fun t : ℝ => ‖x + t • v‖ ^ 2 / 2) (J x v) 0

/-- Domain: norm topology. Codomain: the shared weak-star topology. -/
def WeakStarContinuity : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [StrictConvexSpace ℝ (X →L[ℝ] ℝ)]
    (J : X → (X →L[ℝ] ℝ)), (∀ x, Spec.DualityMapValue X x = {J x}) →
    @Continuous X (X →L[ℝ] ℝ) inferInstance
      (P1.C12WeakStar.Spec.WeakStarTopologyValue ℝ X) J

/-- In particular this is convergence along arbitrary nets (indeed all filters). -/
def NetContinuity : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [StrictConvexSpace ℝ (X →L[ℝ] ℝ)]
    (J : X → (X →L[ℝ] ℝ)), (∀ x, Spec.DualityMapValue X x = {J x}) →
    ∀ (A : Type v) (l : Filter A) (z : A → X) (x : X),
      Tendsto z l (𝓝 x) →
      Tendsto (J ∘ z) l
        (@nhds _ (P1.C12WeakStar.Spec.WeakStarTopologyValue ℝ X) (J x))

def PairingIdentity : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [StrictConvexSpace ℝ (X →L[ℝ] ℝ)]
    (J : X → (X →L[ℝ] ℝ)), (∀ x, Spec.DualityMapValue X x = {J x}) →
    ∀ x y, (J x + J y) (x + y) + (J x - J y) (x - y) =
      2 * (‖x‖ ^ 2 + ‖y‖ ^ 2)

/-- The inverse, identified canonically with a map from the dual to X, is
exactly the normalized duality map on the dual, including its uniqueness. -/
def BijectiveInverse : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [StrictConvexSpace ℝ (X →L[ℝ] ℝ)] [StrictConvexSpace ℝ X],
    P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ (J : X → (X →L[ℝ] ℝ)), (∀ x, Spec.DualityMapValue X x = {J x}) →
      Function.Bijective J ∧ ∃ K : (X →L[ℝ] ℝ) → X,
        Function.LeftInverse K J ∧ Function.RightInverse K J ∧
        ∀ f, Spec.DualityMapValue (X →L[ℝ] ℝ) f =
          {P1.C04CanonicalMap.Spec.CanonicalEvaluationValue ℝ X (K f)}
end ExpandedFA.BanachConvex.StrictDualSpec
