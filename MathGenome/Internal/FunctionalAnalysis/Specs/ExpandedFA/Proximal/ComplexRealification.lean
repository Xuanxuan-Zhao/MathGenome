import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.ScaledLimit
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.EmptyMinimizerDivergence
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.EnvelopeGradient
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Hilbert.Conventions

/-!
Independent statements for paper.tex:8696–8707, `fa2:p2:prox-realification`.
The normed group, topology and uniform structure are those of the original
complex space. Only scalars and the inner product are restricted to ℝ.
All convexity, derivatives and continuous subgradients below are real.
The functions are the SAME canonical proximal/envelope/conjugate choices
from the upstream definitions, instantiated with this real Hilbert structure.
No complex linearity is required of any proximal map or gradient.

The statements include every preceding proximal theorem and the agreed
Problem 26 differentiability assertion, with arbitrary positive real parameters,
finite or infinite primal values, and full parameter limits in norm.
-/
noncomputable section
open Filter Set
open scoped InnerProductSpace Topology
namespace ExpandedFA.Proximal.ComplexSpec
open P1.ExtendedConvexFunctions
universe u

/-- Restriction of scalars retains the original geometry and completeness. -/
def Geometry : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H],
    let innerC : H → H → ℂ := inner ℂ
    let normH : H → ℝ := norm
    let distH : H → H → ℝ := dist
    let topH : TopologicalSpace H := inferInstance
    let uniformH : UniformSpace H := inferInstance
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    (∀ x y, ⟪x, y⟫_ℝ = (innerC x y).re) ∧
    (∀ x, ‖x‖ = normH x) ∧ (∀ x y, dist x y = distH x y) ∧
    (inferInstance : TopologicalSpace H) = topH ∧
    (inferInstance : UniformSpace H) = uniformH ∧
    (∀ (r : ℝ) (x : H), r • x = (r : ℂ) • x)

/-- The displayed objective and infimum use the unchanged complex norm. -/
def ObjectiveAndEnvelope : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H) (μ : ℝ) (f v : H),
      Spec.ProximalObjectiveValue H φ μ f v =
        φ v + ((‖f - v‖ ^ 2 / (2 * μ) : ℝ) : WithTop ℝ) ∧
      Spec.MoreauEnvelopeValue H φ μ f =
        ⨅ y, P1.C06Conjugates.Spec.ExtendedRealValueValue (φ y) +
          ((‖f - y‖ ^ 2 / (2 * μ) : ℝ) : EReal)

/-- In particular the conjugate uses a real pairing, not an antidual. -/
def ConjugateFormula : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H) (w : H),
      Spec.HilbertConjugateValue H φ w =
        ⨆ v, ((inner ℂ w v).re : EReal) -
          P1.C06Conjugates.Spec.ExtendedRealValueValue (φ v)

/-- This also fixes the value outside the effective domain to be empty. -/
def SubgradientFormula : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H) (x : H),
      Spec.HilbertSubdifferentialValue H φ x =
        {w | x ∈ P1.ExtendedConvexFunctions.Spec.finiteDomainValue H φ ∧
          ∀ v, φ x + ((inner ℂ w (v - x)).re : WithTop ℝ) ≤ φ v}

/-- Every continuous real functional has exactly one real Riesz vector. -/
def RealRieszRepresentation : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ F : H →L[ℝ] ℝ, ∃! w : H, ∀ v, F v = (inner ℂ w v).re

/-- The real Banach subdifferential is exactly the image, including empty sets. -/
def SubgradientRieszImage : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H) (x : H),
      BanachConvex.Spec.SubdifferentialValue H φ x =
        (InnerProductSpace.toDual ℝ H) '' Spec.HilbertSubdifferentialValue H φ x

/-- The shared Banach conjugate is evaluated on the real continuous dual. -/
def ConjugateRieszIdentification : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H) (w : H),
      Spec.HilbertConjugateValue H φ w =
        P1.C06Conjugates.Spec.ConvexConjugateValue H φ (InnerProductSpace.toDual ℝ H w)

def UniqueMinimizer : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      ∃! u, Spec.IsProximalMinimizerValue H φ μ f u

def FiniteEnvelope : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      ∃ r : ℝ, Spec.MoreauEnvelopeValue H φ μ f = (r : EReal)

def ProximalMapMinimizes : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      Spec.IsProximalMinimizerValue H φ μ f (Spec.ProximalMapValue H φ μ f)

def MinimizerIffVariational : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H), P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f u : H,
      Spec.IsProximalMinimizerValue H φ μ f u ↔ VariationalSpec.VariationalInequalityValue H φ μ f u

def VariationalIffSubgradient : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H) (μ : ℝ), 0 < μ → ∀ f u : H,
      VariationalSpec.VariationalInequalityValue H φ μ f u ↔
        μ⁻¹ • (f - u) ∈ Spec.HilbertSubdifferentialValue H φ u

def ProximalCharacterization : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f u : H,
      (u = Spec.ProximalMapValue H φ μ f ↔ VariationalSpec.VariationalInequalityValue H φ μ f u) ∧
      (u = Spec.ProximalMapValue H φ μ f ↔
        μ⁻¹ • (f - u) ∈ Spec.HilbertSubdifferentialValue H φ u)

def FirmBound : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f g : H,
      let u := Spec.ProximalMapValue H φ μ f
      let z := Spec.ProximalMapValue H φ μ g
      ‖u - z‖ ^ 2 ≤ ⟪f - g, u - z⟫_ℝ

def Nonexpansive : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f g : H,
      ‖Spec.ProximalMapValue H φ μ f - Spec.ProximalMapValue H φ μ g‖ ≤ ‖f - g‖

def IndicatorProjection : Prop := by
  classical
  exact ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (K : Set H) (hne : K.Nonempty) (hclosed : IsClosed K) (hc : Convex ℝ K)
    (μ : ℝ), 0 < μ →
    Spec.ProximalMapValue H (fun v => if v ∈ K then 0 else ⊤) μ =
      Hilbert.Projection.Spec.ConvexProjectionValue ℝ H K hne hclosed hc

def ConjugateIdentification : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H), P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    ∀ w, P1.C06Conjugates.Spec.ExtendedRealValueValue (MoreauSpec.ConjugateFunctionValue H φ w) =
      Spec.HilbertConjugateValue H φ w

def ConjugateRegularity : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
      P1.ExtendedConvexFunctions.Spec.ProperValue H (MoreauSpec.ConjugateFunctionValue H φ) ∧
      P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H (MoreauSpec.ConjugateFunctionValue H φ) ∧
      P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H (MoreauSpec.ConjugateFunctionValue H φ)

def Decomposition : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      let u := Spec.ProximalMapValue H φ μ f
      let w := Spec.ProximalMapValue H (MoreauSpec.ConjugateFunctionValue H φ) μ⁻¹ (μ⁻¹ • f)
      u + μ • w = f ∧
      ∃ r s a b : ℝ,
        φ u = (r : WithTop ℝ) ∧
        Spec.HilbertConjugateValue H φ w = (s : EReal) ∧
        MoreauSpec.ConjugateFunctionValue H φ w = (s : WithTop ℝ) ∧
        r + s = ⟪u, w⟫_ℝ ∧
        Spec.MoreauEnvelopeValue H φ μ f = (a : EReal) ∧
        Spec.MoreauEnvelopeValue H (MoreauSpec.ConjugateFunctionValue H φ) μ⁻¹ (μ⁻¹ • f) = (b : EReal) ∧
        a + b = ‖f‖ ^ 2 / (2 * μ)

def UnitParameter : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ → ∀ f : H,
      Spec.ProximalMapValue H φ 1 f +
        Spec.ProximalMapValue H (MoreauSpec.ConjugateFunctionValue H φ) 1 f = f ∧
      Spec.MoreauEnvelopeValue H φ 1 f +
        Spec.MoreauEnvelopeValue H (MoreauSpec.ConjugateFunctionValue H φ) 1 f =
          ((‖f‖ ^ 2 / 2 : ℝ) : EReal)

def Regularity : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ μ : ℝ, 0 < μ →
      (∀ f, Spec.MoreauEnvelopeValue H φ μ f = (EnvelopeSpec.RealEnvelopeValue H φ μ f : EReal)) ∧
      ContDiff ℝ 1 (EnvelopeSpec.RealEnvelopeValue H φ μ) ∧
      (∀ f, HasFDerivAt (EnvelopeSpec.RealEnvelopeValue H φ μ)
        (InnerProductSpace.toDual ℝ H (EnvelopeSpec.GradientValue H φ μ f)) f) ∧
      (∀ f, fderiv ℝ (EnvelopeSpec.RealEnvelopeValue H φ μ) f =
        InnerProductSpace.toDual ℝ H (EnvelopeSpec.GradientValue H φ μ f)) ∧
      Continuous (fun f => fderiv ℝ (EnvelopeSpec.RealEnvelopeValue H φ μ) f) ∧
      Continuous (EnvelopeSpec.GradientValue H φ μ)

def DualIdentification : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ μ : ℝ, 0 < μ → ∀ f : H,
      let u := Spec.ProximalMapValue H φ μ f
      let w := EnvelopeSpec.GradientValue H φ μ f
      w = Spec.ProximalMapValue H (MoreauSpec.ConjugateFunctionValue H φ) μ⁻¹ (μ⁻¹ • f) ∧
      ∃ r s : ℝ, φ u = (r : WithTop ℝ) ∧
        Spec.HilbertConjugateValue H φ w = (s : EReal) ∧
        r + s = ⟪u, w⟫_ℝ ∧
        EnvelopeSpec.RealEnvelopeValue H φ μ f = ⟪w, f⟫_ℝ - s - μ * ‖w‖ ^ 2 / 2 ∧
        ∀ z : H,
          (⟪z, f⟫_ℝ : EReal) - Spec.HilbertConjugateValue H φ z -
            ((μ * ‖z‖ ^ 2 / 2 : ℝ) : EReal) ≤ Spec.MoreauEnvelopeValue H φ μ f

def SmallParameterLimit : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ f : H, Tendsto (fun μ : ℝ => Spec.ProximalMapValue H φ μ f)
      (𝓝[>] (0 : ℝ)) (𝓝 (SmallParameterSpec.DomainProjectionValue H φ f))

def MinimizerSetGeometry : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    (LargeParameterSpec.ArgminValue H φ).Nonempty →
    (LargeParameterSpec.ArgminValue H φ).Nonempty ∧ IsClosed (LargeParameterSpec.ArgminValue H φ) ∧ Convex ℝ (LargeParameterSpec.ArgminValue H φ)

def LargeParameterLimit : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ hne : (LargeParameterSpec.ArgminValue H φ).Nonempty,
      ∃ (hclosed : IsClosed (LargeParameterSpec.ArgminValue H φ)) (hc : Convex ℝ (LargeParameterSpec.ArgminValue H φ)),
        ∀ f : H, Tendsto (fun μ : ℝ => Spec.ProximalMapValue H φ μ f) atTop
          (𝓝 (Hilbert.Projection.Spec.ConvexProjectionValue ℝ H
            (LargeParameterSpec.ArgminValue H φ) hne hclosed hc f))

def EmptyMinimizerDivergence : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    LargeParameterSpec.ArgminValue H φ = ∅ →
    ∀ f : H, Tendsto (fun μ : ℝ => ‖Spec.ProximalMapValue H φ μ f‖) atTop atTop

def ScaledLimit : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ f : H, Tendsto (fun μ : ℝ => μ⁻¹ • Spec.ProximalMapValue H φ μ f)
      atTop (𝓝 (-SmallParameterSpec.DomainProjectionValue H
        (MoreauSpec.ConjugateFunctionValue H φ) 0))

/-- The derivative acts on a REAL direction by the real part of the complex
pairing with the residual gradient. No complex Fréchet derivative is asserted. -/
def GradientPairing : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
    letI := Hilbert.Conventions.Spec.RealificationValue ℂ H
    ∀ (φ : ExtendedFunction H),
      P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
      P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
      P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
      ∀ μ : ℝ, 0 < μ → ∀ f v : H,
        fderiv ℝ (EnvelopeSpec.RealEnvelopeValue H φ μ) f v =
          (inner ℂ (μ⁻¹ • (f - Spec.ProximalMapValue H φ μ f)) v).re

end ExpandedFA.Proximal.ComplexSpec
