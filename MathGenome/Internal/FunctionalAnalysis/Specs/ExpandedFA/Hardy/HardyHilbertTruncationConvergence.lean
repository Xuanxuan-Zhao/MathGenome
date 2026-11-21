import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hardy.AtomicHardySpace
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.SingularIntegrals.HilbertTransform

/-!
The Hilbert-truncation clause of `fa2:p4:hardy-maximal-forward`,
paper.tex:18486--18523. The separate smooth maximal assertion is not this goal.
The Hardy space below is the original atomic quotient on the ordinary real line,
with Lebesgue measure. The truncations are the upstream actual integrals, with
kernel 1/(πt), and the limit agrees with every compatible weak Hilbert extension.
No truncation or atom estimate is assumed in the final statement.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

namespace ExpandedFA.Hardy.HardyHilbertTruncationConvergenceSpec
open AtomicHardySpaceSpec
open _root_.ExpandedFA.SingularIntegrals.HilbertTransform
open _root_.Specs.ExpandedFA.SingularIntegrals.HilbertTransform

abbrev LineHardy (𝕜 : Type) [RCLike 𝕜] :=
  HardyValue (𝕜 := 𝕜) (volume : Measure ℝ)
abbrev LineAtom (𝕜 : Type) [RCLike 𝕜] :=
  AtomValue (𝕜 := 𝕜) (volume : Measure ℝ)

/-- All positive cutoffs define absolute integrals at every point of an L¹ input.
This prevents a totalized Bochner integral from hiding nonexistence. -/
def TruncatedL1Existence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (ε : ℝ), 0 < ε →
    ∀ (f : LineLp 𝕜 1) (x : ℝ),
      IntegrableOn (fun t => ((Real.pi * t : ℝ) : 𝕜)⁻¹ * f (x - t))
        {t : ℝ | ε < |t|}

/-- A single bound for the genuine L² integrals, over every positive cutoff. -/
def UniformL2Bounds : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    (∀ (ε : ℝ), 0 < ε → ∀ f : ComplexL2,
      eLpNorm (truncated ε f) 2 volume ≤ ENNReal.ofReal (C * ‖f‖)) ∧
    (∀ (ε : ℝ), 0 < ε → ∀ f : RealL2,
      eLpNorm (truncated ε f) 2 volume ≤ ENNReal.ofReal (C * ‖f‖))

/-- The cutoff discontinuity contributes a shell term in addition to the
usual smooth-kernel difference estimate. The expression is written directly
so this Spec does not depend on the implementation's `cutKernel` helper. -/
def CutoffKernelDifferenceControl : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] {x c y ε R : ℝ},
    0 < R → 2*R < |x-c| → |y-c| ≤ R →
    ‖(if ε < |x-y| then ((Real.pi * (x-y) : ℝ) : 𝕜)⁻¹ else 0) -
      (if ε < |x-c| then ((Real.pi * (x-c) : ℝ) : 𝕜)⁻¹ else 0)‖ ≤
      2 * R / (Real.pi * |x-c| ^ 2) +
        (if |(|x-c| - ε)| ≤ R then (Real.pi * |x-c|)⁻¹ else 0)

/-- The partial-interval contribution has a uniform far-field integral bound. -/
def PartialCutoffIntegralControl : Prop :=
  ∀ {c R ε : ℝ}, 0 < R →
    IntegrableOn (fun x : ℝ => (Real.pi * |x-c|)⁻¹)
      {x : ℝ | 2*R < |x-c| ∧ |(|x-c| - ε)| ≤ R} ∧
    (∫ x in {x : ℝ | 2*R < |x-c| ∧ |(|x-c| - ε)| ≤ R},
      (Real.pi * |x-c|)⁻¹) ≤ 2 / Real.pi

/-- A proper intermediate atom estimate. This is not an assumption of the
final endpoint theorem below; it must be proved from the original atoms. -/
def UniformAtomBounds (𝕜 : Type) [RCLike 𝕜] : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ∀ a : LineAtom 𝕜,
    Integrable (truncated ε a.val) volume ∧
      (∫ x : ℝ, ‖truncated ε a.val x‖) ≤ C

/-- Single-atom limits must be the actual L² Hilbert image. This intermediate
property is also an obligation, not a certificate assumed in FullTheorem. -/
def AtomLimits (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) : Prop :=
  ∀ a : LineAtom 𝕜,
    ∃ h2 : MemLp (a.val : ℝ → 𝕜) 2 volume,
    ∃ g : LineLp 𝕜 1,
      (g : ℝ → 𝕜) =ᵐ[volume] (A (h2.toLp a.val) : ℝ → 𝕜) ∧
      Tendsto (fun ε : ℝ => eLpNorm
        (fun x => truncated ε a.val x - g x) 1 volume) (𝓝[>] 0) (𝓝 0)

/-- Actual continuous linear realizations of every truncated integral, a
uniform operator norm bound, and strong L¹ convergence to the compatible
Hilbert transform, for every element of the completed atomic space. The bound
is chosen before the compatible realization S. -/
def Endpoint (𝕜 : Type) [RCLike 𝕜]
    (A : LineLp 𝕜 2 → LineLp 𝕜 2) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Extensions 𝕜 A,
    ∃ E : LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1,
    ∃ U : ∀ ε : ℝ, 0 < ε → LineHardy 𝕜 →L[𝕜] LineLp 𝕜 1,
      ‖E‖ ≤ C ∧
      (∀ h : LineHardy 𝕜,
        (E h : ℝ → 𝕜) =ᵐ[volume]
          (S.weak (EmbeddingValue volume h) : ℝ → 𝕜)) ∧
      (∀ (ε : ℝ) (hε : 0 < ε), ‖U ε hε‖ ≤ C ∧
        ∀ h : LineHardy 𝕜,
          Integrable (truncated ε (EmbeddingValue volume h)) volume ∧
          (U ε hε h : ℝ → 𝕜) =ᵐ[volume]
            truncated ε (EmbeddingValue volume h)) ∧
      ∀ h : LineHardy 𝕜,
        Tendsto (fun ε : ℝ => eLpNorm
          (fun x => truncated ε (EmbeddingValue volume h) x - E h x) 1 volume)
          (𝓝[>] 0) (𝓝 0)

/-- Both original scalar fields, with the real operator tied to the fixed
complex Fourier multiplier by the upstream scalar embedding. -/
def FullTheorem : Prop :=
  TruncatedL1Existence ∧ Endpoint ℂ complexHilbert ∧
    ∃ A : RealL2 →L[ℝ] RealL2, IsRealRestriction A ∧ Endpoint ℝ A

end ExpandedFA.Hardy.HardyHilbertTruncationConvergenceSpec
