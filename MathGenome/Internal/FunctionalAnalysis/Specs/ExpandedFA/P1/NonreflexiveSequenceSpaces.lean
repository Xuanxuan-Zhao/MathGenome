import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04CanonicalMap
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12DualPair
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Negative examples in `fa2:p1:c14:reflexive-examples`, paper.tex 2977–2990.
All objects are the canonical Part I sequence spaces. The scalar field is real
or complex, the duals are scalar-linear, and reflexivity is surjectivity of
canonical evaluation. These assertions concern sequences on counting measure. -/

noncomputable section

namespace ExpandedFA.P1.NonreflexiveSequenceSpaces.Spec

universe u
open Filter
open C01SequenceSpaces
open scoped Topology ENNReal

-- Cache the inherited structures before iterating the dual constructor.
local instance (𝕜 : Type u) [RCLike 𝕜] : NormedAddCommGroup (SequenceC0 𝕜) :=
  inferInstance
local instance (𝕜 : Type u) [RCLike 𝕜] : NormedSpace 𝕜 (SequenceC0 𝕜) :=
  inferInstance

/-- The bidual identification respects canonical evaluation, so its image is
exactly the null sequences and misses the constant sequence one. -/
def C0BidualImage : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∃ B : ((SequenceC0 𝕜 →L[𝕜] 𝕜) →L[𝕜] 𝕜) ≃ₗᵢ[𝕜] SequenceLInfinity 𝕜,
      (∀ x : SequenceC0 𝕜,
        B (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 (SequenceC0 𝕜) x) = x.val) ∧
      Set.range (fun x : SequenceC0 𝕜 =>
        B (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 (SequenceC0 𝕜) x)) =
        {a | Tendsto (fun n => a n) atTop (𝓝 0)} ∧
      (1 : SequenceLInfinity 𝕜) ∉ Set.range (fun x : SequenceC0 𝕜 =>
        B (C04CanonicalMap.Spec.CanonicalEvaluationValue 𝕜 (SequenceC0 𝕜) x))

def C0Nonreflexive : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (SequenceC0 𝕜)

/-- No strictly increasing extraction of the ℓ¹ unit vectors converges in
σ(ℓ¹,(ℓ¹)′), with the dual taken for the original norm. -/
def L1NoWeakSubsequence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (k : ℕ → ℕ), StrictMono k →
    ¬ ∃ x : SequenceLp 𝕜 1,
      Tendsto (fun n => (lp.single 1 (k n) (1 : 𝕜) : SequenceLp 𝕜 1)) atTop
        (@nhds (SequenceLp 𝕜 1)
          (C12DualPairSpec.DualPairTopologyValue 𝕜 (SequenceLp 𝕜 1)
            (SequenceLp 𝕜 1 →L[𝕜] 𝕜) (topDualPairing 𝕜 (SequenceLp 𝕜 1))) x)

def L1Nonreflexive : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (SequenceLp 𝕜 1)

/-- The actual inherited-norm submodule c₀ of ℓ∞ is closed. -/
def C0Closed : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    IsClosed (sequenceC0Submodule 𝕜 : Set (SequenceLInfinity 𝕜))

def LInfinityNonreflexive : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ¬ C04CanonicalMap.Spec.IsReflexiveValue 𝕜 (SequenceLInfinity 𝕜)

end ExpandedFA.P1.NonreflexiveSequenceSpaces.Spec
