import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2Kernel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Compactness.Definitions
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! The compactness and adjoint portion of `fa2:p5:l2-kernel`, paper.tex
21704–21743. All L² spaces use ordinary a.e. equality and ordinary product
measures. No finite mass, nonzero measure, or separability is assumed.
The continuous-model bridge and Hilbert–Schmidt norm are separately allocated. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace ComplexConjugate Topology
universe u v
namespace ExpandedFA.PartV.L2KernelCompactSpec

/-- Finite-measure rectangles, whose indicators are products of indicators. -/
def rectangles {X : Type u} {Y : Type v} (𝕜 : Type) [RCLike 𝕜]
    [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν] :
    Set (Lp 𝕜 2 (μ.prod ν)) :=
  {f | ∃ (B : Set X) (C : Set Y) (hB : MeasurableSet B) (hC : MeasurableSet C)
      (hμB : μ B ≠ ∞) (hνC : ν C ≠ ∞),
    f = indicatorConstLp 2 (hB.prod hC)
      (by rw [Measure.prod_prod]; exact ENNReal.mul_ne_top hμB hνC) (1 : 𝕜)}

def TensorDensity : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν],
    Dense (Submodule.span 𝕜 (rectangles 𝕜 μ ν) : Set (Lp 𝕜 2 (μ.prod ν)))

def OperatorApproximation : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)),
    ∃ kn : ℕ → Lp 𝕜 2 (μ.prod ν),
      (∀ n, kn n ∈ Submodule.span 𝕜 (rectangles 𝕜 μ ν)) ∧
      (∀ n, FiniteDimensional 𝕜 (LinearMap.range
        (L2KernelSpec.OperatorValue μ ν (kn n)).toLinearMap)) ∧
      Tendsto kn atTop (𝓝 k) ∧
      Tendsto (fun n => L2KernelSpec.OperatorValue μ ν (kn n)) atTop
        (𝓝 (L2KernelSpec.OperatorValue μ ν k))

def Compact : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)),
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (L2KernelSpec.OperatorValue μ ν k).toLinearMap

/-- Conjugate transpose, using the measure-preserving swap on product spaces. -/
def dagger {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)) : Lp 𝕜 2 (ν.prod μ) :=
  Lp.compMeasurePreserving Prod.swap
    (Measure.measurePreserving_swap (μ := ν) (ν := μ)) (star k)

/-- Absolute integrability on the full product, sufficient for Fubini. -/
def TripleBound : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)) (v : Lp 𝕜 2 μ) (u : Lp 𝕜 2 ν),
    Integrable (fun p : X × Y => conj (v p.1) * k p * u p.2) (μ.prod ν) ∧
    (∫ p : X × Y, ‖conj (v p.1) * k p * u p.2‖ ∂μ.prod ν) ≤
      ‖k‖ * ‖v‖ * ‖u‖

def AdjointFormula : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (k : Lp 𝕜 2 (μ.prod ν)),
    ContinuousLinearMap.adjoint (L2KernelSpec.OperatorValue μ ν k) =
      L2KernelSpec.OperatorValue ν μ (dagger μ ν k) ∧
    ∀ v : Lp 𝕜 2 μ,
      (∀ᵐ y ∂ν, Integrable (fun x => conj (k (x,y)) * v x) μ) ∧
      (ContinuousLinearMap.adjoint (L2KernelSpec.OperatorValue μ ν k) v : Y → 𝕜)
        =ᵐ[ν] (fun y => ∫ x, conj (k (x,y)) * v x ∂μ)

/-- Hermitian symmetry includes conjugation, unlike plain complex symmetry. -/
def Hermitian {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (k : Lp 𝕜 2 (μ.prod μ)) : Prop :=
  (k : X × X → 𝕜) =ᵐ[μ.prod μ] fun p => conj (k p.swap)

def Symmetric {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (k : Lp 𝕜 2 (μ.prod μ)) : Prop :=
  (k : X × X → 𝕜) =ᵐ[μ.prod μ] fun p => k p.swap

def HermitianCompactSelfAdjoint : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (k : Lp 𝕜 2 (μ.prod μ)), Hermitian μ k →
    ExpandedFA.Compactness.DefinitionsSpec.IsCompactLinearMapValue
      (L2KernelSpec.OperatorValue μ μ k).toLinearMap ∧
    ContinuousLinearMap.adjoint (L2KernelSpec.OperatorValue μ μ k) =
      L2KernelSpec.OperatorValue μ μ k

/-- Plain symmetry over ℂ does not suffice, even on a probability space. -/
def SymmetryCounterexample : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ],
    ∃ k : Lp ℂ 2 (μ.prod μ), Symmetric μ k ∧
      ContinuousLinearMap.adjoint (L2KernelSpec.OperatorValue μ μ k) ≠
        L2KernelSpec.OperatorValue μ μ k

end ExpandedFA.PartV.L2KernelCompactSpec
