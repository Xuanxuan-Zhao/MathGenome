import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.RCLike.Basic

/-!
Independent interface for paper.tex:6726–6736 (`fa2:p1:frechet-derivative`).
A map on an open set is represented by an ambient function restricted to that
set, as in Mathlib's calculus API. At a point of the open set all sufficiently
small increments remain in the set. No condition is imposed outside the set.
We use `HasFDerivWithinAt`, `fderiv`, and `ContDiffOn` themselves, rather than
introducing a second derivative notion. The norm on `E →L[𝕜] F` in
`ContinuousOn` is the native operator norm.
-/

open scoped Topology Asymptotics ContDiff

namespace ExpandedFA.Differential.Spec

/-- Type of the canonical derivative on the displayed domain. As for native
`fderivWithin`, its value is zero where a derivative cannot be chosen. -/
def FrechetDerivativeType :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (Ω : Set E) (f : E → F) (x : E), E →L[𝕜] F

/-- The required definition is exactly the native derivative, with no
independently defined differentiability predicate. -/
noncomputable def frechetDerivativeValue : FrechetDerivativeType :=
  fun 𝕜 _ _ _ _ _ _ _ _ _ Ω f x => fderivWithin 𝕜 f Ω x

/-- On the open domain the chosen derivative equals every candidate satisfying
the printed definition. No existence of a derivative is assumed separately. -/
def CanonicalDerivativeIdentification : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (Ω : Set E), IsOpen Ω → ∀ (f : E → F) (x : E), x ∈ Ω →
    ∀ A : E →L[𝕜] F,
      (fun h : E => ‖f (x + h) - f x - A h‖) =o[𝓝 0] (fun h => ‖h‖) →
      fderivWithin 𝕜 f Ω x = A

/-- Native differentiation on an open set is precisely the printed norm
small-o expansion in increments. -/
def FrechetDerivativeSmallO : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (Ω : Set E), IsOpen Ω → ∀ (f : E → F) (x : E), x ∈ Ω →
    ∀ A : E →L[𝕜] F,
      HasFDerivWithinAt f A Ω x ↔
        (fun h : E => ‖f (x + h) - f x - A h‖) =o[𝓝 0] (fun h => ‖h‖)

/-- Two candidates satisfying the small-o definition coincide. -/
def SmallOUniqueness : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (f : E → F) (x : E) (A B : E →L[𝕜] F),
      (fun h : E => ‖f (x + h) - f x - A h‖) =o[𝓝 0] (fun h => ‖h‖) →
      (fun h : E => ‖f (x + h) - f x - B h‖) =o[𝓝 0] (fun h => ‖h‖) →
      A = B

/-- The C¹ notation agrees with existence of a continuous field of bounded
linear derivatives on the open domain. -/
def C1DerivativeField : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (Ω : Set E), IsOpen Ω → ∀ f : E → F,
      ContDiffOn 𝕜 1 f Ω ↔
        ∃ D : E → E →L[𝕜] F,
          ContinuousOn D Ω ∧ ∀ x ∈ Ω, HasFDerivWithinAt f (D x) Ω x

/-- The derivative field can be the canonical Mathlib Fréchet derivative. -/
def C1CanonicalDerivative : Prop :=
  ∀ (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (Ω : Set E), IsOpen Ω → ∀ f : E → F,
      ContDiffOn 𝕜 1 f Ω ↔
        DifferentiableOn 𝕜 f Ω ∧ ContinuousOn (fderiv 𝕜 f) Ω

end ExpandedFA.Differential.Spec
