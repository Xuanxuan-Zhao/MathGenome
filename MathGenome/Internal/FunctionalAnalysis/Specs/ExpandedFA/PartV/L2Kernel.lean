import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod

/-! Independent specification for the bounded-operator portion of
`fa2:p5:l2-kernel` (paper.tex:21704–21722). Native L² uses ordinary a.e.
equality and the measure is the ordinary product measure. Scalars are ℝ or ℂ.
There are no separability, nonzero-measure, or finite-mass assumptions. -/

open MeasureTheory
open scoped ENNReal

universe u v
noncomputable section
namespace ExpandedFA.PartV.L2KernelSpec

/-- A total choice of the continuous linear map with the integral formula.
Existence (and hence the correctness of this choice) is a theorem below. -/
def OperatorType :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν],
    Lp 𝕜 2 (μ.prod ν) → (Lp 𝕜 2 ν →L[𝕜] Lp 𝕜 2 μ)

def OperatorValue : OperatorType.{u,v} := fun μ ν _ _ k =>
  Classical.epsilon fun K : Lp _ 2 ν →L[_] Lp _ 2 μ =>
    ∀ u, (K u : _ → _) =ᵐ[μ] fun x => ∫ y, k (x, y) * u y ∂ν

def Sections : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → 𝕜), MemLp k 2 (μ.prod ν) →
    ∀ᵐ x ∂μ, MemLp (fun y => k (x,y)) 2 ν

def AbsoluteSectionIntegrability : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → 𝕜) (u : Y → 𝕜), MemLp k 2 (μ.prod ν) → MemLp u 2 ν →
    ∀ᵐ x ∂μ, Integrable (fun y => k (x,y) * u y) ν ∧
      Integrable (fun y => ‖k (x,y) * u y‖) ν

def OutputMemLp : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → 𝕜) (u : Y → 𝕜), MemLp k 2 (μ.prod ν) → MemLp u 2 ν →
    MemLp (fun x => ∫ y, k (x,y) * u y ∂ν) 2 μ

/-- Formula for any raw representatives, not only the native chosen ones. -/
def RepresentativeFormula : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → 𝕜) (u : Y → 𝕜) (hk : MemLp k 2 (μ.prod ν)) (hu : MemLp u 2 ν),
    (OperatorValue μ ν (hk.toLp k) (hu.toLp u) : X → 𝕜) =ᵐ[μ]
      fun x => ∫ y, k (x,y) * u y ∂ν

/-- Both representatives can change simultaneously. -/
def RepresentativeIndependence : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k k' : X × Y → 𝕜) (u u' : Y → 𝕜), k =ᵐ[μ.prod ν] k' → u =ᵐ[ν] u' →
    (fun x => ∫ y, k (x,y) * u y ∂ν) =ᵐ[μ]
      fun x => ∫ y, k' (x,y) * u' y ∂ν

def NormBound : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)), ‖OperatorValue μ ν k‖ ≤ ‖k‖

/-- Measurability of the actual integral output, together with a measurable
representative of its ordinary a.e. class. -/
def OutputMeasurability : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : X × Y → 𝕜) (u : Y → 𝕜), MemLp k 2 (μ.prod ν) → MemLp u 2 ν →
    AEStronglyMeasurable (fun x => ∫ y, k (x,y) * u y ∂ν) μ ∧
      ∃ f : X → 𝕜, Measurable f ∧
        f =ᵐ[μ] fun x => ∫ y, k (x,y) * u y ∂ν

end ExpandedFA.PartV.L2KernelSpec
