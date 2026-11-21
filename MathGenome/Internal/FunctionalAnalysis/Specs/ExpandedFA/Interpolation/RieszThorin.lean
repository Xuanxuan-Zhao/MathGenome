import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.SimpleFunc

/-!
Independent interface for paper.tex:18115–18162, fa2:p4:riesz-thorin.
The common domain is the algebraic sum inside the ordinary a.e. quotient.
Endpoint bounds refer to this same complex-linear map, so compatibility is
part of the object, rather than a condition on unrelated extensions.

The nonnegative constants are bounds, not necessarily exact operator norms.
Extended norms are used in EndpointBound so finiteness is not hidden by toReal.
The conclusion supplies sum-domain membership for every intermediate Lp class,
and a finite target norm with the manuscript's real quantitative estimate.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v

namespace ExpandedFA.Interpolation.RieszThorinSpec

/-- Algebraic sum of the two Lp subspaces of measurable functions modulo a.e. equality. -/
abbrev SumSpace {X : Type u} [MeasurableSpace X] (μ : Measure X) (p₀ p₁ : ℝ≥0∞) :=
  Lp.LpSubmodule ℂ ℂ p₀ μ ⊔ Lp.LpSubmodule ℂ ℂ p₁ μ

/-- Reciprocal infinity is zero. This extended-real formula is the usual
real reciprocal convex interpolation formula for exponents at least one. -/
def Interpolates (r₀ r₁ r : ℝ≥0∞) (θ : ℝ) : Prop :=
  r⁻¹ = ENNReal.ofReal (1 - θ) * r₀⁻¹ + ENNReal.ofReal θ * r₁⁻¹

/-- A compatible endpoint restriction of the single common-domain operator. -/
def EndpointBound {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ : ℝ≥0∞}
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ)) (p q : ℝ≥0∞) (M : ℝ) : Prop :=
  ∀ f : SumSpace μ p₀ p₁, MemLp (f : X →ₘ[μ] ℂ) p μ →
    MemLp (T f) q ν ∧
      eLpNorm (T f) q ν ≤ ENNReal.ofReal M * eLpNorm (f : X →ₘ[μ] ℂ) p μ

/-- Full Riesz–Thorin statement, including both p=∞ and q=1 configurations.
The witness hf ensures the conclusion evaluates the original operator. -/
def RieszThorin : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (p₀ p₁ q₀ q₁ p q : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (θ M₀ M₁ : ℝ),
    0 < θ → θ < 1 → 0 ≤ M₀ → 0 ≤ M₁ →
    Interpolates p₀ p₁ p θ → Interpolates q₀ q₁ q θ →
    ∀ T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ),
      EndpointBound T p₀ q₀ M₀ → EndpointBound T p₁ q₁ M₁ →
      ∀ f : Lp ℂ p μ, ∃ hf : (f : X →ₘ[μ] ℂ) ∈ SumSpace μ p₀ p₁,
        MemLp (T ⟨f, hf⟩) q ν ∧
          (eLpNorm (T ⟨f, hf⟩) q ν).toReal ≤
            M₀ ^ (1 - θ) * M₁ ^ θ * ‖f‖

/-- Scalar log convexity, valid also when either or both exponents are infinity. -/
def NormInterpolation : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (r₀ r₁ r : ℝ≥0∞) (θ : ℝ), 0 < θ → θ < 1 →
    Interpolates r₀ r₁ r θ → ∀ f : X → ℂ,
    AEStronglyMeasurable f μ →
    eLpNorm f r μ ≤ eLpNorm f r₀ μ ^ (1 - θ) * eLpNorm f r₁ μ ^ θ

/-- The p=∞ case for the actual common-domain operator. No density in L∞ is used. -/
def InfinityDomain : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (q₀ q₁ q : ℝ≥0∞)
    (θ M₀ M₁ : ℝ), 0 < θ → θ < 1 → 0 ≤ M₀ → 0 ≤ M₁ →
    Interpolates q₀ q₁ q θ →
    ∀ T : SumSpace μ ∞ ∞ →ₗ[ℂ] (Y →ₘ[ν] ℂ),
      EndpointBound T ∞ q₀ M₀ → EndpointBound T ∞ q₁ M₁ →
      ∀ f : Lp ℂ ∞ μ, ∃ hf : (f : X →ₘ[μ] ℂ) ∈ SumSpace μ ∞ ∞,
        MemLp (T ⟨f, hf⟩) q ν ∧
          (eLpNorm (T ⟨f, hf⟩) q ν).toReal ≤
            M₀ ^ (1 - θ) * M₁ ^ θ * ‖f‖

/-- Intermediate Lp classes lie in the common sum domain, with no measure-size assumption. -/
def IntermediateDomain : Prop :=
  ∀ {X : Type u} [MeasurableSpace X] (μ : Measure X)
    (p₀ p₁ p : ℝ≥0∞) (θ : ℝ), 0 < θ → θ < 1 → p ≠ 0 →
    Interpolates p₀ p₁ p θ → ∀ f : Lp ℂ p μ,
      (f : X →ₘ[μ] ℂ) ∈ SumSpace μ p₀ p₁

/-- Sharp estimate on simple functions of finite-measure support. The common
operator and its a.e. quotient domain are kept explicit. -/
def SimpleInputBound {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} {p₀ p₁ : ℝ≥0∞}
    (T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ)) (p q : ℝ≥0∞) (C : ℝ) : Prop :=
  ∀ s : SimpleFunc X ℂ, s.FinMeasSupp μ →
    ∀ hs : AEEqFun.mk s s.aestronglyMeasurable ∈ SumSpace μ p₀ p₁,
      eLpNorm (T ⟨AEEqFun.mk s s.aestronglyMeasurable, hs⟩) q ν ≤
        ENNReal.ofReal C * eLpNorm s p μ

/-- Density transfers a simple-input estimate to the original sum-domain
operator. This is a conditional proof lemma, not an assumption in RieszThorin. -/
def DensityTransfer : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (p₀ p₁ q₀ q₁ p q : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ p)]
    (θ M₀ M₁ C : ℝ), 0 < θ → θ < 1 → Interpolates p₀ p₁ p θ → p ≠ ∞ →
    ∀ T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ),
      EndpointBound T p₀ q₀ M₀ → EndpointBound T p₁ q₁ M₁ →
      SimpleInputBound T p q C →
      ∀ f : Lp ℂ p μ, ∃ hf : (f : X →ₘ[μ] ℂ) ∈ SumSpace μ p₀ p₁,
        MemLp (T ⟨f, hf⟩) q ν ∧
          eLpNorm (T ⟨f, hf⟩) q ν ≤ ENNReal.ofReal C * eLpNorm f p μ

/-- The remaining analytic step: the sharp estimate for finite-measure-support
simple inputs. This statement has all the original endpoint configurations. -/
def SimpleEstimate : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (p₀ p₁ q₀ q₁ p q : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (θ M₀ M₁ : ℝ), 0 < θ → θ < 1 → 0 ≤ M₀ → 0 ≤ M₁ →
    Interpolates p₀ p₁ p θ → Interpolates q₀ q₁ q θ → p ≠ ∞ →
    ∀ T : SumSpace μ p₀ p₁ →ₗ[ℂ] (Y →ₘ[ν] ℂ),
      EndpointBound T p₀ q₀ M₀ → EndpointBound T p₁ q₁ M₁ →
      SimpleInputBound T p q (M₀ ^ (1 - θ) * M₁ ^ θ)

end ExpandedFA.Interpolation.RieszThorinSpec
