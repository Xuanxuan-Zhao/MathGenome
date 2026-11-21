import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.C04Dual
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
Independent specification of Definition `fa2:p1:c04:annihilators`, paper.tex
805–815. These are annihilators for the continuous scalar-linear dual pairing.
The input sets need not be subspaces or closed. No completeness, inner product,
or nonzero-space assumption is imposed. `RCLike` covers both scalar fields.
-/

namespace ExpandedFA.P1.C04Annihilators.Spec

universe u v w

def AnnihilatorType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Set E → Submodule 𝕜 (E →L[𝕜] 𝕜)

/-- The underlying set is exactly the functionals vanishing on every point of A. -/
def AnnihilatorValue : AnnihilatorType :=
  fun 𝕜 E _ _ _ A =>
    { carrier := {f : E →L[𝕜] 𝕜 | ∀ a ∈ A, f a = 0}
      zero_mem' := by simp
      add_mem' := by
        intro f g hf hg a ha
        simp [hf a ha, hg a ha]
      smul_mem' := by
        intro c f hf a ha
        simp [hf a ha] }

def PreannihilatorType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E],
    Set (E →L[𝕜] 𝕜) → Submodule 𝕜 E

/-- The underlying set is exactly the points killed by every functional in B. -/
def PreannihilatorValue : PreannihilatorType :=
  fun 𝕜 E _ _ _ B =>
    { carrier := {x : E | ∀ f ∈ B, f x = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy f hf
        simp [map_add, hx f hf, hy f hf]
      smul_mem' := by
        intro c x hx f hf
        simp [hx f hf] }

def BanachTransposeType :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F],
    (E →L[𝕜] F) → (F →L[𝕜] 𝕜) →L[𝕜] (E →L[𝕜] 𝕜)

/-- Fixing the right argument of continuous bilinear composition yields the
bounded scalar-linear transpose. There is no complex conjugation. -/
noncomputable def BanachTransposeValue : BanachTransposeType :=
  fun 𝕜 E F _ _ _ _ _ T => (ContinuousLinearMap.compL 𝕜 E F 𝕜).flip T

def AnnihilatorMembership : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (A : Set E) (f : E →L[𝕜] 𝕜),
    f ∈ AnnihilatorValue 𝕜 E A ↔ ∀ a ∈ A, f a = 0

def PreannihilatorMembership : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (B : Set (E →L[𝕜] 𝕜)) (x : E),
    x ∈ PreannihilatorValue 𝕜 E B ↔ ∀ f ∈ B, f x = 0

def BanachTransposeEvaluation : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) (F : Type w) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace 𝕜 E] [NormedSpace 𝕜 F]
    (T : E →L[𝕜] F) (f : F →L[𝕜] 𝕜) (x : E),
    BanachTransposeValue 𝕜 E F T f x = f (T x)

end ExpandedFA.P1.C04Annihilators.Spec
