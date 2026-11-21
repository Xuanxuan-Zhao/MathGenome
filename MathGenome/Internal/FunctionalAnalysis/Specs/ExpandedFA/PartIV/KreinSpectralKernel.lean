import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinHilbertSchmidtBridge
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinFiberAmplitudes
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Separation.Hausdorff

/-! Independent full assembly statement for the spectral-kernel part of
`fa2:p4:krein-kernel`. Canonical definitions and the three component
obligations are shared through the upstream Specs. The later mollifier limits
and the final representations of F are allocated separately. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal InnerProductSpace Topology

namespace ExpandedFA.PartIV.KreinSpectralKernel.Spec

/-- Original construction, starting with positivity, with no spectral-model
or kernel certificate among the hypotheses. -/
def Main : Prop :=
  ∀ (p : Bool) (F : ℝ → ℝ), Continuous F → Function.Even F →
    KreinSolutions.Specs.PositiveDefiniteValue (KreinSymmetricOperator.Spec.kernel p F) →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (_ : CompleteSpace H) (_ : TopologicalSpace.SeparableSpace H)
      (G : KreinSymmetricOperator.Spec.GramData p F H)
      (S₀ S : Unbounded.Operator ℂ H H),
      (S₀.domain : Set H) = Set.range (fun f : KreinSymmetricOperator.Spec.SmoothTest p =>
        KreinSymmetricOperator.Spec.testIntegral G.vectors f.val) ∧
      (∀ f : KreinSymmetricOperator.Spec.SmoothTest p,
        ∃ hf : KreinSymmetricOperator.Spec.testIntegral G.vectors f.val ∈ S₀.domain,
          S₀ ⟨KreinSymmetricOperator.Spec.testIntegral G.vectors f.val, hf⟩ =
            KreinSymmetricOperator.Spec.testIntegral G.vectors (deriv (deriv f.val))) ∧
      Unbounded.SymmetryAndDeficienciesSpec.symmetricValue S₀ ∧
      KreinSymmetricOperator.Spec.CommutesWith S₀ G.conjugation ∧
      S₀.IsClosable ∧ S₀.closure ≤ S ∧
      Unbounded.SymmetryAndDeficienciesSpec.selfAdjointValue S ∧
      ∃ (M : RealSpectralModel S) (K : KernelData G M), Nonempty (AmplitudeData K)

/-- The quantifier exchange used for all tests after passing to a countable
dense subset in a topology in which the two test pairings are continuous. -/
def CommonNullSet : Prop :=
  ∀ {Ω E Y : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [TopologicalSpace E] [TopologicalSpace.SeparableSpace E]
    [TopologicalSpace Y] [T2Space Y] (L R : Ω → E → Y),
    (∀ᵐ ω ∂μ, Continuous (L ω) ∧ Continuous (R ω)) →
    (∀ x, ∀ᵐ ω ∂μ, L ω x = R ω x) →
    ∀ᵐ ω ∂μ, ∀ x, L ω x = R ω x

/-- The operator identity becomes an a.e. identity for each test. The kernel
and dense-test argument must still perform the subsequent quantifier exchange. -/
def SpectralTestIdentity : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} (G : KreinSymmetricOperator.Spec.GramData p F H)
    (S : Unbounded.Operator ℂ H H) (M : RealSpectralModel S),
    (∀ f : KreinSymmetricOperator.Spec.SmoothTest p,
      ∃ hf : KreinSymmetricOperator.Spec.testIntegral G.vectors f.val ∈ S.domain,
        S ⟨KreinSymmetricOperator.Spec.testIntegral G.vectors f.val, hf⟩ =
          KreinSymmetricOperator.Spec.testIntegral G.vectors (deriv (deriv f.val))) →
    ∀ f : KreinSymmetricOperator.Spec.SmoothTest p,
      (M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors (deriv (deriv f.val))) :
        ℝ → FiberSpace) =ᵐ[M.μ]
        fun ξ => (ξ : ℂ) • M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors f.val) ξ

/-- Conversion of the vector-kernel energy to scalar energy for the actual
amplitude-weighted measure. No continuity of the amplitude is required. -/
def AmplitudeEnergyTransfer : Prop :=
  ∀ (μ τ : Measure ℝ) (c : ℝ → FiberSpace), AEStronglyMeasurable c μ →
    ∀ (h : ℝ → ℝ → FiberSpace) (Z : ℝ → ℝ → ℂ),
    (∀ᵐ ξ ∂μ, (h ξ) =ᵐ[τ] fun t => Z ξ t • c ξ) →
    (∫⁻ ξ, ∫⁻ t, ‖h ξ t‖ₑ ^ 2 ∂τ ∂μ) =
      ∫⁻ ξ, ∫⁻ t, ‖Z ξ t‖ₑ ^ 2 ∂τ ∂amplitudeMeasure μ c

/-- In particular the original local solution-energy bound follows from the
kernel energy and an a.e. factorization, before any total-mass assertion. -/
def FactoredLocalEnergy : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} {G : KreinSymmetricOperator.Spec.GramData p F H}
    {S : Unbounded.Operator ℂ H H} {M : RealSpectralModel S} (K : KernelData G M)
    (c : ℝ → FiberSpace), AEStronglyMeasurable c M.μ →
    (∀ᵐ ξ ∂M.μ, (K.h ξ) =ᵐ[volume] fun t => (solution p ξ t : ℂ) • c ξ) →
    ∀ R : ℝ, 0 < R →
      (∫⁻ ξ, ∫⁻ t, ENNReal.ofReal (|solution p ξ t| ^ 2)
        ∂intervalMeasure R ∂amplitudeMeasure M.μ c) < ∞

/-- The positive squared-solution norm supplies such a weight. This general
criterion proves local finiteness without imposing boundedness of c. -/
def LocalFinitenessCriterion : Prop :=
  ∀ {X : Type} [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X]
    (ν : Measure X) (q : X → ℝ), Continuous q → (∀ x, 0 < q x) →
    (∫⁻ x, ENNReal.ofReal (q x) ∂ν) < ∞ → IsLocallyFiniteMeasure ν

end ExpandedFA.PartIV.KreinSpectralKernel.Spec
