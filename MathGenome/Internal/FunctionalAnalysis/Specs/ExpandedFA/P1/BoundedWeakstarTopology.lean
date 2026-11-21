import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.SeminormModel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar
import Mathlib.Analysis.Normed.Operator.Bilinear

/-! Independent statements for the topology and closed-set clauses of
`fa2:p1:bounded-weak-star`, paper.tex:3311–3354. The Banach-only description
of the continuous dual is a separately allocated obligation. The dual carrier
and its operator norm always use the original norm topology on E. -/

open Set Filter
open scoped Topology

noncomputable section
namespace ExpandedFA.P1.BoundedWeakstarTopology.Spec

/-- All sequences converging to zero in the original norm topology. -/
def NullSequence (E : Type*) [NormedAddCommGroup E] :=
  {x : ℕ → E // Tendsto x atTop (𝓝 0)}

def SeminormType :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    NullSequence E → Seminorm 𝕜 (E →L[𝕜] 𝕜)

/-- The supremum of the evaluation seminorms. The implementation must prove
boundedness and the pointwise supremum formula, so the conditional supremum
here has its intended finite meaning. -/
def SeminormValue : SeminormType := fun 𝕜 _E _ _ _ x =>
  ⨆ n : ℕ, (normSeminorm 𝕜 𝕜).comp
    (ContinuousLinearMap.apply 𝕜 𝕜 (x.1 n)).toLinearMap

def TopologyType :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    TopologicalSpace (E →L[𝕜] 𝕜)

def TopologyValue : TopologyType := fun 𝕜 E _ _ _ =>
  SeminormModelSpec.topologyValue 𝕜 (E →L[𝕜] 𝕜) (NullSequence E)
    (SeminormValue 𝕜 E)

def FiniteSupremum : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (x : NullSequence E) (f : E →L[𝕜] 𝕜),
    BddAbove (range (fun n => ‖f (x.1 n)‖)) ∧
      SeminormValue 𝕜 E x f = ⨆ n : ℕ, ‖f (x.1 n)‖

def Construction : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    letI : TopologicalSpace (E →L[𝕜] 𝕜) := TopologyValue 𝕜 E
    LCS 𝕜 (E →L[𝕜] 𝕜) ∧ T2Space (E →L[𝕜] 𝕜) ∧
      ∀ x : NullSequence E, Continuous (SeminormValue 𝕜 E x)

/-- Equality of the relative topologies on every norm-bounded set. -/
def BoundedAgreement : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : Set (E →L[𝕜] 𝕜)), Bornology.IsBounded A →
    TopologicalSpace.induced (Subtype.val : A → (E →L[𝕜] 𝕜)) (TopologyValue 𝕜 E) =
      TopologicalSpace.induced (Subtype.val : A → (E →L[𝕜] 𝕜))
        (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)

/-- Finest among all topologies, with no vector-topology restriction on t.
Lean's order on topologies reverses the inclusion of open sets. -/
def Finest : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (t : TopologicalSpace (E →L[𝕜] 𝕜)),
    (∀ A : Set (E →L[𝕜] 𝕜), Bornology.IsBounded A →
      TopologicalSpace.induced (Subtype.val : A → (E →L[𝕜] 𝕜)) t =
        TopologicalSpace.induced (Subtype.val : A → (E →L[𝕜] 𝕜))
          (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)) →
    TopologyValue 𝕜 E ≤ t

/-- The slice is closed in the whole weak-star dual, not merely in the ball.
No convexity assumption is imposed on C. -/
def ClosedCriterion : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (C : Set (E →L[𝕜] 𝕜)),
    @IsClosed _ (TopologyValue 𝕜 E) C ↔
      ∀ r : ℝ, 0 < r → @IsClosed _ (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 E)
        (C ∩ {f : E →L[𝕜] 𝕜 | ‖f‖ ≤ r})

end ExpandedFA.P1.BoundedWeakstarTopology.Spec
