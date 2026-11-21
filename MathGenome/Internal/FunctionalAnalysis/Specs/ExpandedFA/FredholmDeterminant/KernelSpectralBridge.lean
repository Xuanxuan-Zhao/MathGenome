import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.ContinuousKernel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2Kernel
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-! The representation bridge in paper.tex, 11156–11174. Finite Borel
measures suffice, hence in particular finite positive Radon measures.
No full support, nonzero mass, or nonempty domain is imposed. -/
noncomputable section
open MeasureTheory
universe u
namespace ExpandedFA.FredholmDeterminant.KernelSpectralBridge.Spec

/-- Full generalized eigenspace, including every finite power kernel. -/
def generalizedSpace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (z : ℂ) : Submodule ℂ E :=
  ⨆ n : ℕ, LinearMap.ker ((z • LinearMap.id - T.toLinearMap) ^ n)

section
variable {Q : Type u} [MetricSpace Q] [CompactSpace Q]
  [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]

/-- Natural map to the almost-everywhere quotient; no injectivity claim. -/
abbrev inclusion : C(Q, ℂ) →L[ℂ] Lp ℂ 2 μ := ContinuousMap.toLp 2 μ ℂ

/-- Total choice of the bounded kernel map. Its defining property is proved
in the implementation, without assuming an existence certificate. -/
def kernelMap (k : C(Q × Q, ℂ)) : Lp ℂ 2 μ →L[ℂ] C(Q, ℂ) :=
  Classical.epsilon fun A : Lp ℂ 2 μ →L[ℂ] C(Q, ℂ) =>
    ∀ (f : Lp ℂ 2 μ) (x : Q), A f x = ∫ y, k (x,y) * f y ∂μ

abbrev continuousOperator (k : C(Q × Q, ℂ)) :=
  ExpandedFA.PartV.ContinuousKernel.Spec.KernelOperatorValue μ k

/-- The same continuous kernel, in the ordinary product L² space. -/
def kernelClass (k : C(Q × Q, ℂ)) : Lp ℂ 2 (μ.prod μ) :=
  ContinuousMap.toLp 2 (μ.prod μ) ℂ k

abbrev hilbertOperator (k : C(Q × Q, ℂ)) :=
  ExpandedFA.PartV.L2KernelSpec.OperatorValue μ μ (kernelClass μ k)
end

/-- Construction and both actual operator identifications. -/
def Representation : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
    (k : C(Q × Q, ℂ)),
    (∀ (f : Lp ℂ 2 μ) (x : Q), kernelMap μ k f x = ∫ y, k (x,y) * f y ∂μ) ∧
    (kernelMap μ k).comp (inclusion μ) = continuousOperator μ k ∧
    (inclusion μ).comp (kernelMap μ k) = hilbertOperator μ k

/-- The full nonzero spectra agree. The equivalence of full generalized
spaces is induced by J itself, so this compares algebraic multiplicities,
not merely ordinary eigenspaces. Finiteness is included explicitly. -/
def SpectralComparison : Prop :=
  ∀ {Q : Type u} [MetricSpace Q] [CompactSpace Q]
    [MeasurableSpace Q] [BorelSpace Q] (μ : Measure Q) [IsFiniteMeasure μ]
    (k : C(Q × Q, ℂ)) (z : ℂ), z ≠ 0 →
    (z ∈ spectrum ℂ (continuousOperator μ k) ↔ z ∈ spectrum ℂ (hilbertOperator μ k)) ∧
    FiniteDimensional ℂ (generalizedSpace (continuousOperator μ k) z) ∧
    FiniteDimensional ℂ (generalizedSpace (hilbertOperator μ k) z) ∧
    (∃ e : generalizedSpace (continuousOperator μ k) z ≃ₗ[ℂ]
        generalizedSpace (hilbertOperator μ k) z,
      ∀ x, (e x : Lp ℂ 2 μ) = inclusion μ (x : C(Q, ℂ))) ∧
    Module.finrank ℂ (generalizedSpace (continuousOperator μ k) z) =
      Module.finrank ℂ (generalizedSpace (hilbertOperator μ k) z)

end ExpandedFA.FredholmDeterminant.KernelSpectralBridge.Spec
