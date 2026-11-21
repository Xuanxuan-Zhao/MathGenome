import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
Independent statements for paper.tex:18150–18179. The input and output measures
are arbitrary positive measures. The scalar field may be real or complex.
All norm bounds use extended norms until finiteness has been established.
In particular infinity is never converted to zero by `ENNReal.toReal`.
-/
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
universe u v w

namespace ExpandedFA.Interpolation.MarcinkiewiczSpec

/-- Distribution function of the modulus; sets are measured by outer measure,
so this definition is also meaningful for an a.e. measurable representative. -/
def distribution {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (f : X → E) (t : ℝ) : ℝ≥0∞ := μ {x | t < ‖f x‖}

/-- The common domain `Lᵖ⁰ + Lᵖ¹`, represented by functions modulo a.e. equality. -/
def sumDomain {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (p₀ p₁ : ℝ≥0∞) (f : X → E) : Prop :=
  ∃ g h : X → E, MemLp g p₀ μ ∧ MemLp h p₁ μ ∧ f =ᵐ[μ] g + h

/-- Sublinearity is required only on the operator's common domain. An operator
on a.e. classes is represented by a total function with congruence on that domain.
The norm formulation also applies to the modulus of a linear operator. -/
structure SublinearOn {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) (D : (X → 𝕜) → Prop)
    (T : (X → 𝕜) → Y → 𝕜) : Prop where
  measurable : ∀ f, D f → AEStronglyMeasurable (T f) ν
  congr : ∀ f g, D f → D g → f =ᵐ[μ] g → T f =ᵐ[ν] T g
  add_le : ∀ f g, D f → D g → ∀ᵐ y ∂ν, ‖T (f + g) y‖ ≤ ‖T f y‖ + ‖T g y‖
  smul_norm : ∀ (c : 𝕜) f, D f → ∀ᵐ y ∂ν, ‖T (c • f) y‖ = ‖c‖ * ‖T f y‖

/-- Standard weak `(r,r)` estimate for a single input/output pair.
For finite positive `r`, taking the `r`th power gives the usual distribution
estimate. For `r = ∞` the definition is explicitly the strong supremum bound. -/
def endpointEstimate {X Y E F : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (μ : Measure X) (ν : Measure Y) (r : ℝ≥0∞) (C : ℝ≥0)
    (f : X → E) (g : Y → F) : Prop :=
  if r = ∞ then eLpNorm g ∞ ν ≤ (C : ℝ≥0∞) * eLpNorm f ∞ μ
  else ∀ t : ℝ, 0 < t →
    ENNReal.ofReal t * distribution ν g t ^ (1 / r.toReal) ≤
      (C : ℝ≥0∞) * eLpNorm f r μ

/-- Endpoint estimates apply to every member of each endpoint space,
with the *same* operator at the two endpoints. -/
def endpointBound {X Y 𝕜 : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [RCLike 𝕜] (μ : Measure X) (ν : Measure Y) (r : ℝ≥0∞)
    (C : ℝ≥0) (T : (X → 𝕜) → Y → 𝕜) : Prop :=
  ∀ f, MemLp f r μ → endpointEstimate μ ν r C f (T f)

/-- The constant is uniform over measure spaces and operators, depending only
on the three exponents and the two weak constants. Both endpoints here are
finite. Membership and the full norm bound are required for every intermediate
input, without restricting it to the initial intersection. -/
def FiniteInterpolation : Prop :=
  ∀ (r₀ r₁ p : ℝ) (C₀ C₁ : ℝ≥0), 1 ≤ r₀ → r₀ < p → p < r₁ →
  ∃ K : ℝ≥0,
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type w}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    (μ : Measure X) (ν : Measure Y) (T : (X → 𝕜) → Y → 𝕜),
    SublinearOn μ ν (sumDomain μ (ENNReal.ofReal r₀) (ENNReal.ofReal r₁)) T →
    endpointBound μ ν (ENNReal.ofReal r₀) C₀ T →
    endpointBound μ ν (ENNReal.ofReal r₁) C₁ T →
    ∀ f, MemLp f (ENNReal.ofReal p) μ →
      MemLp (T f) (ENNReal.ofReal p) ν ∧
      eLpNorm (T f) (ENNReal.ofReal p) ν ≤ (K : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) μ

/-- The upper endpoint is the *strong* essential supremum bound. Only the
strictly intermediate, finite exponents are asserted. -/
def InfinityInterpolation : Prop :=
  ∀ (r₀ p : ℝ) (C₀ C₁ : ℝ≥0), 1 ≤ r₀ → r₀ < p →
  ∃ K : ℝ≥0,
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type w}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    (μ : Measure X) (ν : Measure Y) (T : (X → 𝕜) → Y → 𝕜),
    SublinearOn μ ν (sumDomain μ (ENNReal.ofReal r₀) ∞) T →
    endpointBound μ ν (ENNReal.ofReal r₀) C₀ T →
    endpointBound μ ν ∞ C₁ T →
    ∀ f, MemLp f (ENNReal.ofReal p) μ →
      MemLp (T f) (ENNReal.ofReal p) ν ∧
      eLpNorm (T f) (ENNReal.ofReal p) ν ≤ (K : ℝ≥0∞) * eLpNorm f (ENNReal.ofReal p) μ

/-- The full endpoint intersection, inside the intermediate a.e. quotient.
Using the full intersection permits measurable truncation; an arbitrary dense
linear subspace of it would not justify the source's truncation argument. -/
def intersectionCore {X 𝕜 : Type*} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p₀ p₁ p : ℝ≥0∞) [Fact (1 ≤ p)] : Submodule 𝕜 (Lp 𝕜 p μ) where
  carrier := {f | MemLp (f : X → 𝕜) p₀ μ ∧ MemLp (f : X → 𝕜) p₁ μ}
  zero_mem' := by
    constructor <;> exact (memLp_congr_ae (Lp.coeFn_zero 𝕜 p μ)).2 (MemLp.zero)
  add_mem' := by
    intro f g hf hg
    constructor
    · exact (memLp_congr_ae (Lp.coeFn_add f g)).2 (hf.1.add hg.1)
    · exact (memLp_congr_ae (Lp.coeFn_add f g)).2 (hf.2.add hg.2)
  smul_mem' := by
    intro c f hf
    constructor
    · exact (memLp_congr_ae (Lp.coeFn_smul c f)).2 (hf.1.const_smul c)
    · exact (memLp_congr_ae (Lp.coeFn_smul c f)).2 (hf.2.const_smul c)

/-- Linear operators initially given on the endpoint intersection extend
uniquely to a bounded linear operator on the intermediate space. Agreement is
as functions a.e., and the operator norm is bounded by a uniform finite constant.
The upper endpoint can be infinity, interpreted by `endpointEstimate` above. -/
def LinearExtension : Prop :=
  ∀ (p₀ p₁ p : ℝ≥0∞) [Fact (1 ≤ p)], 1 ≤ p₀ → p₀ < p → p < p₁ →
  ∀ (C₀ C₁ : ℝ≥0), ∃ K : ℝ≥0,
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type w}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    (μ : Measure X) (ν : Measure Y)
    (T : intersectionCore μ p₀ p₁ p →ₗ[𝕜] (Y → 𝕜)),
    (∀ f, AEStronglyMeasurable (T f) ν) →
    (∀ f, endpointEstimate μ ν p₀ C₀ (f.1 : X → 𝕜) (T f)) →
    (∀ f, endpointEstimate μ ν p₁ C₁ (f.1 : X → 𝕜) (T f)) →
    ∃! S : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p ν,
      ‖S‖ ≤ (K : ℝ) ∧ ∀ f, (S f.1 : Y → 𝕜) =ᵐ[ν] T f

/-! Auxiliary statements expose the completed parts of the implementation;
none of them assumes either interpolation theorem. -/

def MomentLayercake : Prop :=
  ∀ {X : Type u} {E : Type v} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) {f : X → E} (hf : AEStronglyMeasurable f μ)
    {p : ℝ} (hp : 0 < p),
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) = ENNReal.ofReal p *
      ∫⁻ t in Ioi 0, distribution μ f t * ENNReal.ofReal (t ^ (p - 1))

def IntersectionDense : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] {𝕜 : Type v} [RCLike 𝕜]
    (μ : Measure X) (p₀ p₁ p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ∞),
    Dense (intersectionCore (𝕜 := 𝕜) μ p₀ p₁ p : Set (Lp 𝕜 p μ))

/-- A conditional completion lemma: the strong bound is an explicit premise,
not a substitute for the weak-to-strong interpolation obligation above. -/
def ExtensionOfBound : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {𝕜 : Type w} [RCLike 𝕜] (μ : Measure X) (ν : Measure Y)
    (p₀ p₁ p : ℝ≥0∞) [Fact (1 ≤ p)] (hptop : p ≠ ∞) (C : ℝ≥0)
    (T : intersectionCore μ p₀ p₁ p →ₗ[𝕜] (Y → 𝕜))
    (hb : ∀ f, MemLp (T f) p ν ∧
      eLpNorm (T f) p ν ≤ (C : ℝ≥0∞) * eLpNorm (f.1 : X → 𝕜) p μ),
    ∃! S : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p ν,
      ‖S‖ ≤ (C : ℝ) ∧ ∀ f, (S f.1 : Y → 𝕜) =ᵐ[ν] T f

end ExpandedFA.Interpolation.MarcinkiewiczSpec
