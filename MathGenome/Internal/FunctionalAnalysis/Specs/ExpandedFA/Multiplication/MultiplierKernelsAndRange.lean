import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.MultiplierTranspose

/-! Independent statements for the kernel, annihilator and range clauses of
`fa2:p3:lp-multiplication`, paper.tex:13937ff. The dual is identified by the
scalar-linear bilinear integral pairing. All equalities concern ordinary a.e.
Lp classes on an arbitrary positive measure space. -/
noncomputable section
open MeasureTheory
open scoped ENNReal Topology
universe u
namespace ExpandedFA.Multiplication.MultiplierKernelsAndRangeSpec
open FunctionSpaces.ScalarLpIntegralPairingSpec Unbounded

def Kernel : Prop :=
  ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    (μ : Measure Ω) (r : ℝ≥0∞) (a : Ω → 𝕜),
    (maximalMultiplier μ r a).ker = supportedLp μ r (zeroSet a)

def KernelAnnihilator : Prop :=
  ∀ {Ω : Type u} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], 1 < p → p ≠ ∞ →
    ∀ (a : Ω → 𝕜), Measurable a →
    {g : Lp 𝕜 q μ | ∀ f ∈ (maximalMultiplier μ p a).ker,
      IntegralPairingValue μ p q g f = 0} =
      (supportedLp (𝕜 := 𝕜) μ q (zeroSet a)ᶜ : Set (Lp 𝕜 q μ))

def TransposeKernel : Prop :=
  ∀ {Ω : Type u} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], 1 < p → p ≠ ∞ →
    ∀ (a : Ω → 𝕜), Measurable a →
    ((BanachAdjointSpec.adjointValue (maximalMultiplier μ p a)).ker).comap
      (IntegralPairingValue μ p q).toLinearMap = supportedLp μ q (zeroSet a)

def TransposeKernelPreannihilator : Prop :=
  ∀ {Ω : Type u} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], 1 < p → p ≠ ∞ →
    ∀ (a : Ω → 𝕜), Measurable a →
    {f : Lp 𝕜 p μ | ∀ g : Lp 𝕜 q μ,
      IntegralPairingValue μ p q g ∈
        (BanachAdjointSpec.adjointValue (maximalMultiplier μ p a)).ker →
      IntegralPairingValue μ p q g f = 0} =
      (supportedLp (𝕜 := 𝕜) μ p (zeroSet a)ᶜ : Set (Lp 𝕜 p μ))

def RangeClosure : Prop :=
  ∀ {Ω : Type u} {𝕜 : Type} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], 1 < p → p ≠ ∞ →
    ∀ (a : Ω → 𝕜), Measurable a →
    closure ((maximalMultiplier μ p a).toFun.range : Set (Lp 𝕜 p μ)) =
      (supportedLp (𝕜 := 𝕜) μ p (zeroSet a)ᶜ : Set (Lp 𝕜 p μ))

/-- The masked quotient has value zero on Z; no choice of representative
changes either a.e. condition. No assumption on the size of the measure. -/
def ExactRange : Prop :=
  ∀ {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure Ω) (p : ℝ≥0∞) (a : Ω → 𝕜), Measurable a →
    ((maximalMultiplier μ p a).toFun.range : Set (Lp 𝕜 p μ)) =
      {h | (∀ᵐ x ∂μ, x ∈ zeroSet a → h x = 0) ∧
        MemLp ((zeroSet a)ᶜ.indicator (fun x => h x / a x)) p μ}

end ExpandedFA.Multiplication.MultiplierKernelsAndRangeSpec
