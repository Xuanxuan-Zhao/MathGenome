import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

/-! Independent specifications for `fa2:p5:fractional-definition`.
The interval has positive finite real length. Scalars are real or complex.
The power integral at alpha=0 is deliberately not the logarithmic integral.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace ExpandedFA.PartV.FractionalIntegrals.Spec

def PowerIntegralType := ∀ {𝕜 : Type} [RCLike 𝕜], ℝ → (ℝ → 𝕜) → ℝ → 𝕜

def LogarithmicIntegralType := ∀ {𝕜 : Type} [RCLike 𝕜], (ℝ → 𝕜) → ℝ → 𝕜

def intervalMeasure (T : ℝ) : Measure ℝ := volume.restrict (Ioc 0 T)

def powerKernel (α T : ℝ) : ℝ → ℝ :=
  (Ioc 0 T).indicator (fun r => r ^ (α - 1))

def powerValue {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (f : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  ∫ s in Ioc 0 t, (t - s) ^ (α - 1) • f s

def fractionalValue {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (f : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  (Real.Gamma α)⁻¹ • powerValue α f t

def logarithmicValue {𝕜 : Type} [RCLike 𝕜] (f : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  ∫ s in Ioc 0 t, Real.log (t - s) • f s

def operatorBound (α T : ℝ) : ℝ := T ^ α / Real.Gamma (α + 1)

/-- A continuous function is evaluated outside its interval by clamping. The
integral statements only use its original values on the interval. -/
def continuousExtension {𝕜 : Type} [RCLike 𝕜] {T : ℝ} (hT : 0 ≤ T)
    (f : C(Icc (0 : ℝ) T, 𝕜)) (s : ℝ) : 𝕜 := f (projIcc 0 T hT s)

def KernelMass : Prop := ∀ (α T : ℝ), 0 < α → 0 < T →
  Integrable (powerKernel α T) ∧
  (∫ r, ‖powerKernel α T r‖) = T ^ α / α ∧
  (Real.Gamma α)⁻¹ * (∫ r, ‖powerKernel α T r‖) = operatorBound α T

def ContinuousConstruction : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ) (hα : 0 < α) (hT : 0 < T),
  ∃ J : C(Icc (0 : ℝ) T, 𝕜) →L[𝕜] C(Icc (0 : ℝ) T, 𝕜),
    (∀ f (t : Icc (0 : ℝ) T),
      IntegrableOn (fun s => ((t : ℝ) - s) ^ (α - 1) • continuousExtension hT.le f s)
        (Ioc 0 (t : ℝ)) ∧
      J f t = fractionalValue α (continuousExtension hT.le f) t) ∧
    ‖J‖ ≤ operatorBound α T

/-- Construction on the actual a.e. quotient for every exponent, including
infinity. The defining formula is required for every MemLp representative. -/
def LpConstruction : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ) (hα : 0 < α) (hT : 0 < T) (p : ℝ≥0∞) [Fact (1 ≤ p)],
  ∃ J : Lp 𝕜 p (intervalMeasure T) →L[𝕜] Lp 𝕜 p (intervalMeasure T),
    (∀ (f : ℝ → 𝕜) (hf : MemLp f p (intervalMeasure T)),
      (∀ᵐ t ∂intervalMeasure T,
        IntegrableOn (fun s => (t - s) ^ (α - 1) • f s) (Ioc 0 t)) ∧
      (J (hf.toLp f) : ℝ → 𝕜) =ᵐ[intervalMeasure T] fractionalValue α f) ∧
    ‖J‖ ≤ operatorBound α T

def RepresentativeIndependence : Prop := ∀ {𝕜 : Type} [RCLike 𝕜]
    (α T : ℝ) (f g : ℝ → 𝕜), f =ᵐ[intervalMeasure T] g →
    ∀ t ∈ Icc (0 : ℝ) T,
      (IntegrableOn (fun s => (t - s) ^ (α - 1) • f s) (Ioc 0 t) ↔
       IntegrableOn (fun s => (t - s) ^ (α - 1) • g s) (Ioc 0 t)) ∧
      fractionalValue α f t = fractionalValue α g t

def KernelDistinction : Prop :=
  (∀ T : ℝ, 0 < T → ¬ IntegrableOn (fun r : ℝ => r ^ ((0 : ℝ) - 1)) (Ioo 0 T)) ∧
  (∀ T : ℝ, 0 < T → IntegrableOn Real.log (Ioc 0 T))

def Normalization : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {α : ℝ},
  0 < α → ∀ (f : ℝ → 𝕜) (t : ℝ),
    powerValue α f t = Real.Gamma α • fractionalValue α f t

def ZeroTime : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] (α : ℝ) (f : ℝ → 𝕜),
  fractionalValue α f 0 = 0

end ExpandedFA.PartV.FractionalIntegrals.Spec
