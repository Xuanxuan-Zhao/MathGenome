import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! Independent specification of the weighted L² part of `fa2:p5:schur`,
paper.tex:21747–21761. Weights are extended nonnegative measurable functions,
strictly positive and finite almost everywhere. Nonnegative integrals are
Lebesgue integrals, so the bounds include finiteness on the good sections.
No integrability or uniform bound on either weight is assumed. -/

open MeasureTheory
open scoped ENNReal NNReal
universe u v
noncomputable section
namespace ExpandedFA.PartV.SchurWeightedSpec

structure Hypotheses {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    (μ : Measure X) (ν : Measure Y) (k : X × Y → 𝕜)
    (a : X → ℝ≥0∞) (b : Y → ℝ≥0∞) (A B : ℝ≥0) : Prop where
  kernel_measurable : Measurable k
  a_measurable : Measurable a
  b_measurable : Measurable b
  a_positive_finite : ∀ᵐ x ∂μ, 0 < a x ∧ a x < ∞
  b_positive_finite : ∀ᵐ y ∂ν, 0 < b y ∧ b y < ∞
  row_bound : ∀ᵐ x ∂μ, (∫⁻ y, ‖k (x,y)‖ₑ * b y ∂ν) ≤ A * a x
  column_bound : ∀ᵐ y ∂ν, (∫⁻ x, ‖k (x,y)‖ₑ * a x ∂μ) ≤ B * b y

def WeightedSchur : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → 𝕜) (a : X → ℝ≥0∞) (b : Y → ℝ≥0∞) (A B : ℝ≥0),
    Hypotheses μ ν k a b A B →
    ∃ K : Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ,
      ‖K‖ ≤ Real.sqrt ((A : ℝ) * (B : ℝ)) ∧
      ∀ (f : Y → 𝕜) (hf : MemLp f 2 ν),
        (∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * f y) ν ∧
          Integrable (fun y => ‖k (x,y) * f y‖) ν) ∧
        MemLp (fun x => ∫ y, k (x,y) * f y ∂ν) 2 μ ∧
        (K (hf.toLp f) : X → 𝕜) =ᵐ[μ] fun x => ∫ y, k (x,y) * f y ∂ν

/-- The raw formula respects simultaneous changes of kernel and input on null sets. -/
def RepresentativeIndependence : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k k' : X × Y → 𝕜) (f f' : Y → 𝕜),
    k =ᵐ[μ.prod ν] k' → f =ᵐ[ν] f' →
    (fun x => ∫ y, k (x,y) * f y ∂ν) =ᵐ[μ]
      fun x => ∫ y, k' (x,y) * f' y ∂ν

end ExpandedFA.PartV.SchurWeightedSpec
