import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C01Norm
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.Seminorm.Norm

/-!
Independent specifications for Definition `fa2:p1:c02:quotient-norm`,
paper.tex, lines 360–369. The quotient is the algebraic quotient by the original
subspace, including nonclosed subspaces. The scalar field can be real or complex.
The norm notation on an arbitrary quotient denotes its distance seminorm;
closedness is required only to select a genuine normed group structure.
-/

noncomputable section

namespace ExpandedFA.P1.C02QuotientNorm.Spec

/-- The canonical scalar-linear projection onto the algebraic quotient. -/
def quotientMapType :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), E →ₗ[𝕜] E ⧸ M

def quotientMapValue : quotientMapType := fun _ _ _ _ _ M => M.mkQ

/-- The native quotient's bundled seminorm, without a closedness assumption. -/
def distanceSeminormType :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), Seminorm 𝕜 (E ⧸ M)

def distanceSeminormValue : distanceSeminormType :=
  fun 𝕜 E _ _ _ M => normSeminorm 𝕜 (E ⧸ M)

/-- For closed subspaces the same quotient carries a genuine norm. -/
def quotientNormedGroupType :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), IsClosed (M : Set E) → NormedAddCommGroup (E ⧸ M)

def quotientNormedGroupValue : quotientNormedGroupType :=
  fun _ E _ _ _ M hM => by
    letI : IsClosed (M : Set E) := hM
    exact Submodule.Quotient.normedAddCommGroup M

def ProjectionFormula : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (x : E),
    quotientMapValue 𝕜 E M x = (Submodule.Quotient.mk x : E ⧸ M)

def ProjectionSurjective : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E), Function.Surjective (quotientMapValue 𝕜 E M)

/-- The real infimum has a nonempty, bounded-below set of candidates even
when `E` is zero or `M` is the whole space. -/
def DistanceCandidates : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (x : E),
    ((fun m : E => ‖x - m‖) '' (M : Set E)).Nonempty ∧
    BddBelow ((fun m : E => ‖x - m‖) '' (M : Set E))

/-- The manuscript formula, with the distance seminorm explicitly identified
with the native quotient's norm function. No closure replaces `M`. -/
def DistanceFormula : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (x : E),
    distanceSeminormValue 𝕜 E M (quotientMapValue 𝕜 E M x) =
      sInf ((fun m : E => ‖x - m‖) '' (M : Set E)) ∧
    distanceSeminormValue 𝕜 E M (quotientMapValue 𝕜 E M x) =
      Metric.infDist x (M : Set E) ∧
    (∀ z : E ⧸ M, distanceSeminormValue 𝕜 E M z = ‖z‖)

/-- Closedness makes exactly this distance seminorm a norm, with the same
underlying scalar module and the full manuscript norm axioms. -/
def ClosedQuotientNorm : Prop :=
  ∀ (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (M : Submodule 𝕜 E) (hM : IsClosed (M : Set E)),
    letI := quotientNormedGroupValue 𝕜 E M hM
    C01Norm.NormAxioms 𝕜 (norm : E ⧸ M → ℝ) ∧
      ∀ z : E ⧸ M, ‖z‖ = distanceSeminormValue 𝕜 E M z

end ExpandedFA.P1.C02QuotientNorm.Spec
