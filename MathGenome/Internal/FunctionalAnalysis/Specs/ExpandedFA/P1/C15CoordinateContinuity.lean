import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.P1.BasisNormCompleteness
import Mathlib.Analysis.Normed.Module.Bases

/-! Independent statements for paper.tex 3824–3874 and its finite/empty cases.
The inputs retain unique ordered expansions with algebraic coordinates. Boundedness
and the native basis structures occur only in the conclusions. -/

noncomputable section
universe u v
namespace ExpandedFA.P1.C15CoordinateContinuity.Spec

variable {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- All boundedness assertions concern the original norm on E. -/
def ContinuousCoordinates {ι : Type*} (a : E → ι → 𝕜) (P : ℕ → E → E) : Prop :=
  ExpandedFA.P1.BasisNormCompleteness.Spec.CompleteSupremumNorm (𝕜 := 𝕜) P ∧
  (∃ C : ℝ, 0 ≤ C ∧ ∀ x : E,
    ‖x‖ ≤ ExpandedFA.P1.BasisNormCompleteness.Spec.partialSumSupNorm P x ∧
    ExpandedFA.P1.BasisNormCompleteness.Spec.partialSumSupNorm P x ≤ C * ‖x‖) ∧
  (∀ i, ∃ f : E →L[𝕜] 𝕜, ∀ x, f x = a x i) ∧
  (∀ N, ∃ T : E →L[𝕜] E, ∀ x, T x = P N x)

def RawCoordinateContinuity : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e),
    ContinuousCoordinates (ExpandedFA.P1.C15Basis.Spec.rawCoordinates h) (ExpandedFA.P1.C15Basis.Spec.rawPartialSum h)

def FiniteCoordinateContinuity : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e),
    ContinuousCoordinates (ExpandedFA.P1.C15Basis.Spec.finiteCoordinates h) (ExpandedFA.P1.C15Basis.Spec.finitePartialSum h)

/-- Conditional (ordered) convergence is preserved by the native packaging. -/
def RawNativeBasis : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {e : ℕ → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawSchauderBasis (𝕜 := 𝕜) e),
    ∃ b : SchauderBasis 𝕜 E, b.basis = e ∧
      (∀ i x, b.coord i x = ExpandedFA.P1.C15Basis.Spec.rawCoordinates h x i) ∧
      (∀ N x, b.proj N x = ExpandedFA.P1.C15Basis.Spec.rawPartialSum h N x)

/-- A finite list has the native finite unconditional interface, also for d = 0. -/
def FiniteNativeBasis : Prop :=
  ∀ {𝕜 : Type u} {E : Type v} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    {d : ℕ} {e : Fin d → E} (h : ExpandedFA.P1.C15Basis.Spec.IsRawFiniteBasis (𝕜 := 𝕜) e),
    ∃ b : UnconditionalSchauderBasis (Fin d) 𝕜 E, b.basis = e ∧
      (∀ i x, b.coord i x = ExpandedFA.P1.C15Basis.Spec.finiteCoordinates h x i) ∧
      (∀ N x, b.proj (Finset.univ.filter (fun i : Fin d => i.val < N)) x =
        ExpandedFA.P1.C15Basis.Spec.finitePartialSum h N x)

end ExpandedFA.P1.C15CoordinateContinuity.Spec
