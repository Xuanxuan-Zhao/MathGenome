import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinRealSpectralModel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.L2HilbertSchmidt

/-! Independent obligation for paper.tex:21274–21301. The canonical data are
imported unchanged from the real spectral model Specs. In particular, the
conclusion includes every native compact test, one scalar null set, product
L², the exact energy, and representation on every local L² input. -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace

namespace ExpandedFA.PartIV.KreinSpectralKernel.Spec

def KernelExistence : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] {p : Bool} {F : ℝ → ℝ}
    (G : KreinSymmetricOperator.Spec.GramData p F H)
    (S : Unbounded.Operator ℂ H H) (M : RealSpectralModel S),
    (∀ f : KreinSymmetricOperator.Spec.SmoothTest p,
      ∃ hf : KreinSymmetricOperator.Spec.testIntegral G.vectors f.val ∈ S.domain,
        S ⟨KreinSymmetricOperator.Spec.testIntegral G.vectors f.val, hf⟩ =
          KreinSymmetricOperator.Spec.testIntegral G.vectors (deriv (deriv f.val))) →
    Nonempty (KernelData G M)

end ExpandedFA.PartIV.KreinSpectralKernel.Spec

namespace ExpandedFA.PartIV.KreinHilbertSchmidtBridge.Spec
open ExpandedFA.PartIV.KreinSpectralKernel

/-- A general separable-test quantifier exchange, including empty test spaces.
Its application requires continuity and separability of the actual test space. -/
def CommonNullSet : Prop :=
  ∀ {Ω E Y : Type} [MeasurableSpace Ω] (μ : Measure Ω)
    [TopologicalSpace E] [TopologicalSpace.SeparableSpace E]
    [TopologicalSpace Y] [T2Space Y] (L R : Ω → E → Y),
    (∀ᵐ ω ∂μ, Continuous (L ω) ∧ Continuous (R ω)) →
    (∀ x, ∀ᵐ ω ∂μ, L ω x = R ω x) →
    ∀ᵐ ω ∂μ, ∀ x, L ω x = R ω x

/-- The graph condition gives the equation separately for each matching test.
This alone does not assert an exchange of the test and a.e. quantifiers. -/
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

/-- The local synthesis map uses the actual restricted Lebesgue integral.
No Hilbert–Schmidt or reverse representation certificate is a hypothesis. -/
def LocalSynthesis : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (v : ℝ → H), Continuous v → ∀ R : ℝ,
    ∃ J : Lp ℂ 2 (intervalMeasure R) →L[ℂ] H,
      (∀ f : Lp ℂ 2 (intervalMeasure R), Integrable (fun t => f t • v t) (intervalMeasure R)) ∧
      (∀ f, J f = ∫ t, f t • v t ∂intervalMeasure R)

/-- The quantitative source assertion about the local synthesis operator. -/
def LocalSynthesisEnergy : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (v : ℝ → H), Continuous v → ∀ R : ℝ,
    ∃ J : Lp ℂ 2 (intervalMeasure R) →L[ℂ] H,
      (∀ f, J f = ∫ t, f t • v t ∂intervalMeasure R) ∧
      TraceIdeals.HilbertSchmidtDefinitions.Spec.HilbertSchmidtSquareValue J =
        ENNReal.ofReal (∫ t, ‖v t‖ ^ 2 ∂intervalMeasure R)

/-- Reverse direction of the scalar kernel theorem. This is a construction
obligation, not an assumption imported from the forward kernel theorem. -/
def ReverseScalarKernel : Prop :=
  ∀ {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ),
    TraceIdeals.HilbertSchmidtDefinitions.Spec.IsHilbertSchmidtValue T →
    ∃! k : Lp ℂ 2 (μ.prod ν), PartV.L2KernelSpec.OperatorValue μ ν k = T

/-- A zero Gram realization has the literal zero kernel, even without making
any assumption that the chosen spectral control measure has positive mass. -/
def ZeroKernel : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} (G : KreinSymmetricOperator.Spec.GramData p F H)
    (S : Unbounded.Operator ℂ H H) (M : RealSpectralModel S),
    (∀ t, G.vectors t = 0) → Nonempty (KernelData G M)

/-- The quantifier exchange for the actual native compact smooth tests. Local
L² is sufficient; separability or continuity of an unspecified test space is
not assumed. The real parameter may be unbounded and the measure arbitrary. -/
def NativeCommonNullSet : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (parameter : Ω → ℝ)
    (h : Ω → ℝ → FiberSpace),
    (∀ᵐ ξ ∂μ, ∀ n : ℕ, MemLp (h ξ) 2 (intervalMeasure (n + 1))) →
    (∀ φ : LineTest, ∀ᵐ ξ ∂μ,
      (∫ t : ℝ, deriv (deriv (φ : ℝ → ℂ)) t • h ξ t) =
        (parameter ξ : ℂ) • ∫ t : ℝ, φ t • h ξ t) →
    ∀ᵐ ξ ∂μ, WeakEquation (parameter ξ) (h ξ)

/-- The exact graph identity on every native test, derived from the action on
matching-parity tests, with no parity assumption on the native input. -/
def NativeSpectralTestIdentity : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} (G : KreinSymmetricOperator.Spec.GramData p F H)
    (S : Unbounded.Operator ℂ H H) (M : RealSpectralModel S),
    (∀ f : KreinSymmetricOperator.Spec.SmoothTest p,
      ∃ hf : KreinSymmetricOperator.Spec.testIntegral G.vectors f.val ∈ S.domain,
        S ⟨KreinSymmetricOperator.Spec.testIntegral G.vectors f.val, hf⟩ =
          KreinSymmetricOperator.Spec.testIntegral G.vectors (deriv (deriv f.val))) →
    ∀ φ : LineTest,
      (M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors
        (deriv (deriv (φ : ℝ → ℂ)))) : ℝ → FiberSpace) =ᵐ[M.μ]
        fun ξ => (ξ : ℂ) • M.U (KreinSymmetricOperator.Spec.testIntegral G.vectors φ) ξ

/-- The complete pointwise-distribution implication once an actual local L²
kernel representation has been constructed. Neither a countable-test
certificate nor an a.e.-for-all-tests conclusion is assumed. -/
def WeakEquationOfRepresentation : Prop :=
  ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {p : Bool} {F : ℝ → ℝ} (G : KreinSymmetricOperator.Spec.GramData p F H)
    (S : Unbounded.Operator ℂ H H) (M : RealSpectralModel S),
    (∀ f : KreinSymmetricOperator.Spec.SmoothTest p,
      ∃ hf : KreinSymmetricOperator.Spec.testIntegral G.vectors f.val ∈ S.domain,
        S ⟨KreinSymmetricOperator.Spec.testIntegral G.vectors f.val, hf⟩ =
          KreinSymmetricOperator.Spec.testIntegral G.vectors (deriv (deriv f.val))) →
    ∀ h : ℝ → ℝ → FiberSpace,
    (∀ᵐ ξ ∂M.μ, ∀ n : ℕ, MemLp (h ξ) 2 (intervalMeasure (n + 1))) →
    (∀ R : ℝ, 0 < R → ∀ f : Lp ℂ 2 (intervalMeasure R),
      (M.U (∫ t, f t • G.vectors t ∂intervalMeasure R) : ℝ → FiberSpace) =ᵐ[M.μ]
        fun ξ => ∫ t, f t • h ξ t ∂intervalMeasure R) →
    ∀ᵐ ξ ∂M.μ, WeakEquation ξ (h ξ)

end ExpandedFA.PartIV.KreinHilbertSchmidtBridge.Spec
