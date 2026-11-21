import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01SequenceSpaces
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C12WeakStar

/-!
Independent statements for `fa2:p1:c12:qualifications` (paper.tex 2388–2398).
`C00L1` is the range of the canonical inclusion of finitely supported sequences
into ℓ¹, with precisely its inherited norm. Natural coordinate `n` denotes
manuscript coordinate `n+1`; the functional with index `n` is therefore
`x ↦ (n+1) * x n`. The scalar net uses the componentwise directed order on ℕ×ℕ.
-/
noncomputable section
open Filter
open scoped Topology ENNReal
universe u
namespace ExpandedFA.P1.WeakstarSequenceQualification

/-- Finitely supported sequences, embedded in the shared canonical ℓ¹ space. -/
def c00L1Submodule (𝕜 : Type u) [RCLike 𝕜] : Submodule 𝕜 (C01SequenceSpaces.SequenceLp 𝕜 1) :=
  LinearMap.range (C01SequenceSpaces.Spec.C00ToLpValue 𝕜 1)

abbrev C00L1 (𝕜 : Type u) [RCLike 𝕜] := ↥(c00L1Submodule 𝕜)

namespace Spec

def FunctionalType := ∀ (𝕜 : Type u) [RCLike 𝕜], ℕ → (C00L1 𝕜 →L[𝕜] 𝕜)
def FunctionalValue : FunctionalType := fun 𝕜 _ n =>
  ((n + 1 : ℕ) : 𝕜) •
    (lp.evalCLM 𝕜 (fun _ : ℕ => 𝕜) (1 : ℝ≥0∞) n).comp (c00L1Submodule 𝕜).subtypeL

def Identification : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    (∀ x : ℕ → 𝕜,
      (∃ y : C00L1 𝕜, ∀ n, y.val n = x n) ↔ (Function.support x).Finite) ∧
    (∀ y : C00L1 𝕜, ‖y‖ = ∑' n, ‖y.val n‖) ∧
    (∀ y : C01SequenceSpaces.SequenceC00 𝕜,
      ∃! x : C00L1 𝕜, ∀ n, x.val n = y n)

def FunctionalFormula : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ) (x : C00L1 𝕜),
    FunctionalValue 𝕜 n x = ((n + 1 : ℕ) : 𝕜) * x.val n

def FunctionalContinuityAndNorm : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (n : ℕ),
    Continuous (FunctionalValue 𝕜 n) ∧ ‖FunctionalValue 𝕜 n‖ = (n + 1 : ℕ)

def EventuallyZero : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : C00L1 𝕜),
    ∀ᶠ n in atTop, FunctionalValue 𝕜 n x = 0

def PointwiseConvergence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜] (x : C00L1 𝕜),
    Tendsto (fun n => FunctionalValue 𝕜 n x) atTop (𝓝 0)

def WeakStarConvergence : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    Tendsto (FunctionalValue 𝕜) atTop
      (@nhds (C00L1 𝕜 →L[𝕜] 𝕜)
        (C12WeakStar.Spec.WeakStarTopologyValue 𝕜 (C00L1 𝕜)) 0)

def UnboundedNorms : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜],
    ∀ C : ℝ, ∃ n : ℕ, C < ‖FunctionalValue 𝕜 n‖

def IncompleteDomain : Prop :=
  ∀ (𝕜 : Type u) [RCLike 𝕜], ¬ CompleteSpace (C00L1 𝕜)

/-- The strip with first coordinate zero is unbounded, while the final segment
above (1,0) is identically zero. -/
def ScalarNetType := (ℕ × ℕ) → ℝ
def ScalarNetValue : ScalarNetType := fun a => if a.1 = 0 then a.2 else 0

def ScalarNetConvergence : Prop :=
  Tendsto ScalarNetValue atTop (𝓝 0)
def ScalarNetUnbounded : Prop :=
  ∀ C : ℝ, ∃ a : ℕ × ℕ, C < ‖ScalarNetValue a‖
def ScalarNetFinalSegment : Prop :=
  ∀ a : ℕ × ℕ, (1, 0) ≤ a → ScalarNetValue a = 0

end Spec
end ExpandedFA.P1.WeakstarSequenceQualification
