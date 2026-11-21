import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Unweighted portion of paper.tex, fa2:p5:schur (21747–21774).
The weighted L² assertion is allocated separately. Bounds below use the
nonnegative integral of the norm, so a finite bound includes absolute existence.
All maps act on a.e. classes and use the same ordinary kernel integral. -/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace ExpandedFA.PartV.SchurLp

/-- The unweighted row and column bounds, allowing a.e. exceptional sections. -/
def KernelBounds {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) (k : X × Y → 𝕜)
    (A B : ℝ≥0) : Prop :=
  (∀ᵐ x ∂μ, ∫⁻ y, ‖k (x,y)‖ₑ ∂ν ≤ A) ∧
  (∀ᵐ y ∂ν, ∫⁻ x, ‖k (x,y)‖ₑ ∂μ ≤ B)

/-- The intended integral formula. Absolute existence is asserted separately. -/
def kernelValue {X Y 𝕜 : Type*} [MeasurableSpace Y] [RCLike 𝕜]
    (ν : Measure Y) (k : X × Y → 𝕜) (f : Y → 𝕜) (x : X) : 𝕜 :=
  ∫ y, k (x,y) * f y ∂ν

/-- The sharp bound; the reciprocal of infinity is zero. -/
def schurConstant (A B : ℝ≥0) (p : ℝ≥0∞) : ℝ :=
  (A : ℝ) ^ (1 - (p⁻¹).toReal) * (B : ℝ) ^ (p⁻¹).toReal

/-- A compatible family, with the integral formula and absolute existence
for every input class, including the two endpoints. -/
structure KernelFamily {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) (k : X × Y → 𝕜)
    (A B : ℝ≥0) where
  op : ∀ p : ℝ≥0∞, ∀ [Fact (1 ≤ p)], Lp 𝕜 p ν →L[𝕜] Lp 𝕜 p μ
  integral_exists : ∀ p [Fact (1 ≤ p)] (f : Lp 𝕜 p ν),
    ∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν
  represents : ∀ p [Fact (1 ≤ p)] (f : Lp 𝕜 p ν),
    (op p f : X → 𝕜) =ᵐ[μ] kernelValue ν k f
  norm_le : ∀ p [Fact (1 ≤ p)], ‖op p‖ ≤ schurConstant A B p
  compatible : ∀ p q [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (f : Lp 𝕜 p ν) (g : Lp 𝕜 q ν),
    (f : Y → 𝕜) =ᵐ[ν] g → (op p f : X → 𝕜) =ᵐ[μ] (op q g : X → 𝕜)

namespace Spec

/-- Full assigned unweighted Schur conclusion, for both scalar fields. -/
def SchurBoundedness : Prop :=
  ∀ {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → 𝕜), Measurable k → ∀ A B : ℝ≥0,
    KernelBounds μ ν k A B → Nonempty (KernelFamily μ ν k A B)

/-- The endpoint conclusions, with their original row/column constants. -/
def EndpointEstimates : Prop :=
  ∀ {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → 𝕜), Measurable k → ∀ A B : ℝ≥0,
    KernelBounds μ ν k A B → ∀ f : Y → 𝕜,
    (MemLp f 1 ν →
      (∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν) ∧
      MemLp (kernelValue ν k f) 1 μ ∧
      eLpNorm (kernelValue ν k f) 1 μ ≤ B * eLpNorm f 1 ν) ∧
    (MemLp f ∞ ν →
      (∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν) ∧
      MemLp (kernelValue ν k f) ∞ μ ∧
      eLpNorm (kernelValue ν k f) ∞ μ ≤ A * eLpNorm f ∞ ν)

/-- A nonzero compactly supported L¹ kernel for the translation example. -/
def boxKernel (x : ℝ) : ℝ := (Set.Icc (0 : ℝ) 1).indicator (fun _ => 1) x

/-- Convolution by the unit interval indicator on ℝ is Schur bounded on L∞
and is not compact. The operator uses the same absolutely convergent integral. -/
def NoncompactConvolution : Prop :=
  Measurable boxKernel ∧ HasCompactSupport boxKernel ∧
    Integrable boxKernel volume ∧ (∫ x, boxKernel x) = 1 ∧
    KernelBounds volume volume (fun z : ℝ × ℝ => boxKernel (z.1-z.2)) 1 1 ∧
    ∃ T : Lp ℝ ∞ (volume : Measure ℝ) →L[ℝ] Lp ℝ ∞ volume,
      (∀ f : Lp ℝ ∞ volume,
        (∀ᵐ x ∂volume, Integrable (fun y => boxKernel (x-y) * f y) volume) ∧
        (T f : ℝ → ℝ) =ᵐ[volume] kernelValue volume (fun z => boxKernel (z.1-z.2)) f) ∧
      ‖T‖ ≤ 1 ∧ ¬ IsCompactOperator T

end Spec
end ExpandedFA.PartV.SchurLp
