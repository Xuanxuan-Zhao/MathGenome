import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C14Reflexive
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Annihilators
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.Algebra.Group.Pointwise

/-! The general assertion of `fa2:p4:constrained-support`, paper.tex:21391–21426.
The subsequent Lp and L1 applications are separately allocated. All duals here
are real continuous linear duals; closure and boundedness use the operator norm.
Reflexivity is surjectivity of the shared canonical evaluation map (and hence
already entails completeness). The support value is extended-real, so an
unbounded convex set is allowed in the equivalence. -/
namespace ExpandedFA.PartIV.ConstrainedSupport.Spec

open Set
open scoped Pointwise
universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Continuous annihilator, using the shared dual-pairing definition. -/
noncomputable abbrev annihilator (M : Submodule ℝ X) : Submodule ℝ (X →L[ℝ] ℝ) :=
  P1.C04Annihilators.Spec.AnnihilatorValue ℝ X (M : Set X)

/-- The supremum can equal positive infinity. -/
noncomputable def supportValue (C : Set (X →L[ℝ] ℝ)) (u : X) : EReal :=
  ⨆ g : C, (g.val u : EReal)

/-- Support domination on a closed subspace characterizes the norm closure. -/
def SupportClosure : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ (M : Submodule ℝ X), IsClosed (M : Set X) →
    ∀ (C : Set (X →L[ℝ] ℝ)), C.Nonempty → Convex ℝ C →
    ∀ f : X →L[ℝ] ℝ,
      (∀ u ∈ M, (f u : EReal) ≤ supportValue C u) ↔
      f ∈ closure ((annihilator M : Set (X →L[ℝ] ℝ)) + C)

/-- Closed bounded convex sets give a closed sum with the annihilator. -/
def ClosedSum : Prop :=
  ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace ℝ X],
    P1.C04CanonicalMap.Spec.IsReflexiveValue ℝ X →
    ∀ (M : Submodule ℝ X), IsClosed (M : Set X) →
    ∀ (C : Set (X →L[ℝ] ℝ)), C.Nonempty → Convex ℝ C →
    IsClosed C → Bornology.IsBounded C →
    IsClosed ((annihilator M : Set (X →L[ℝ] ℝ)) + C)

end ExpandedFA.PartIV.ConstrainedSupport.Spec
