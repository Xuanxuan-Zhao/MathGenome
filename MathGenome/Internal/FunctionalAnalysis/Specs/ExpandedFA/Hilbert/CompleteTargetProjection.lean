import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions

/-!
Independent statements for `paper.tex` 7703–7740, the convex-set part of
`fa2:p2:prehilbert-projection`. Only the target set is assumed complete.
Convexity uses the shared restriction to real scalars, with the original
norm, metric, uniform structure, and conjugate-first inner product.
The complete-linear-subspace specialization is allocated separately.
-/

noncomputable section
open scoped InnerProductSpace

namespace ExpandedFA.Hilbert.CompleteTargetProjection.Spec
universe u v

/-- Minimality is stated directly, over all competitors in the original set. -/
def ExistsUniqueNearestPoint : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (C : Set E), C.Nonempty → IsComplete C →
    Conventions.Spec.RealConvexValue 𝕜 E C →
    ∀ x : E, ∃! p : E, p ∈ C ∧ ∀ z ∈ C, ‖x - p‖ ≤ ‖x - z‖

/-- This characterization needs no completeness assumption. -/
def MinimizerIffVariational : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (C : Set E), Conventions.Spec.RealConvexValue 𝕜 E C →
    ∀ (x p : E), p ∈ C →
      ((∀ z ∈ C, ‖x - p‖ ≤ ‖x - z‖) ↔
        ∀ z ∈ C, RCLike.re ⟪x - p, z - p⟫_𝕜 ≤ 0)

def ConvexProjectionType :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (C : Set E), C.Nonempty → IsComplete C →
    Conventions.Spec.RealConvexValue 𝕜 E C → E → E

/-- Choice of a minimizer, with existence and uniqueness to be proved. -/
def ConvexProjectionValue : ConvexProjectionType.{u, v} :=
  fun _ _ _ _ _ C _ _ _ x =>
    Classical.epsilon fun p => p ∈ C ∧ ∀ z ∈ C, ‖x - p‖ ≤ ‖x - z‖

def ConvexProjectionSpec : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (C : Set E) (hne : C.Nonempty) (hc : IsComplete C)
    (hv : Conventions.Spec.RealConvexValue 𝕜 E C) (x : E),
    ConvexProjectionValue 𝕜 E C hne hc hv x ∈ C ∧
      ∀ z ∈ C, ‖x - ConvexProjectionValue 𝕜 E C hne hc hv x‖ ≤ ‖x - z‖

def EqConvexProjectionIffVariational : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (C : Set E) (hne : C.Nonempty) (hc : IsComplete C)
    (hv : Conventions.Spec.RealConvexValue 𝕜 E C) (x p : E),
    p = ConvexProjectionValue 𝕜 E C hne hc hv x ↔
      p ∈ C ∧ ∀ z ∈ C, RCLike.re ⟪x - p, z - p⟫_𝕜 ≤ 0

def ConvexProjectionFirmNonexpansive : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (C : Set E) (hne : C.Nonempty) (hc : IsComplete C)
    (hv : Conventions.Spec.RealConvexValue 𝕜 E C) (x y : E),
    let P := ConvexProjectionValue 𝕜 E C hne hc hv
    ‖P x - P y‖ ^ 2 ≤ RCLike.re ⟪x - y, P x - P y⟫_𝕜

def ConvexProjectionNonexpansive : Prop :=
  ∀ (𝕜 : Type u) (E : Type v) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (C : Set E) (hne : C.Nonempty) (hc : IsComplete C)
    (hv : Conventions.Spec.RealConvexValue 𝕜 E C) (x y : E),
    let P := ConvexProjectionValue 𝕜 E C hne hc hv
    ‖P x - P y‖ ≤ ‖x - y‖

end ExpandedFA.Hilbert.CompleteTargetProjection.Spec
