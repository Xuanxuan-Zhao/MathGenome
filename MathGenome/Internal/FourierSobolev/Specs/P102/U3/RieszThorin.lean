import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Interpolation.RieszThorin

/-! Independent statement of paper.tex:1106–1124. The initial domain contains
exactly the complex simple functions with support of finite measure. The
operator is not assumed to act on the sum of endpoint Lp spaces. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u v
namespace P102.U3.RieszThorinSpec

abbrev Initial {X : Type u} [MeasurableSpace X] (μ : Measure X) :=
  ExpandedFA.Interpolation.finiteSimpleSubmodule μ

abbrev Interpolates := ExpandedFA.Interpolation.RieszThorinSpec.Interpolates

/-- The canonical a.e. class of an initial simple function, at any exponent. -/
def initialToLp {X : Type u} [MeasurableSpace X] (μ : Measure X) (p : ℝ≥0∞) :
    Initial μ →ₗ[ℂ] Lp ℂ p μ where
  toFun s := ⟨AEEqFun.mk s.val s.val.aestronglyMeasurable,
    Lp.mem_Lp_iff_memLp.mpr
      ((ExpandedFA.Interpolation.finiteSimple_memLp μ s p).ae_eq
        (AEEqFun.coeFn_mk _ _).symm)⟩
  map_add' _s _t := Subtype.ext (AEEqFun.mk_add_mk _ _ _ _).symm
  map_smul' c _s := Subtype.ext (AEEqFun.smul_mk c _ _).symm

/-- An endpoint bound on the original initial domain, using the extended norm
so that no finiteness assumption is hidden by conversion to real numbers. -/
def EndpointBound {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y}
    (T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ)) (p q : ℝ≥0∞) (M : ℝ) : Prop :=
  ∀ s : Initial μ, eLpNorm (T s) q ν ≤ ENNReal.ofReal M * eLpNorm s.val p μ

/-- The sharp bound on all initial functions, including infinite exponents
and zero endpoint constants. -/
def SimpleEstimate : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (p₀ p₁ q₀ q₁ p q : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (θ M₀ M₁ : ℝ), 0 < θ → θ < 1 → 0 ≤ M₀ → 0 ≤ M₁ →
    Interpolates p₀ p₁ p θ → Interpolates q₀ q₁ q θ →
    ∀ T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ),
      EndpointBound T p₀ q₀ M₀ → EndpointBound T p₁ q₁ M₁ →
      ∀ s : Initial μ,
        eLpNorm (T s) q ν ≤
          ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm s.val p μ

/-- Finite input exponents give a unique continuous linear extension, with
its quantitative norm bound and agreement as a measurable a.e. class. -/
def FiniteExtension : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (p₀ p₁ q₀ q₁ p q : ℝ≥0∞)
    [Fact (1 ≤ p₀)] [Fact (1 ≤ p₁)] [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)]
    [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (θ M₀ M₁ : ℝ), 0 < θ → θ < 1 → 0 ≤ M₀ → 0 ≤ M₁ →
    Interpolates p₀ p₁ p θ → Interpolates q₀ q₁ q θ → p ≠ ∞ →
    ∀ T : Initial μ →ₗ[ℂ] (Y →ₘ[ν] ℂ),
      EndpointBound T p₀ q₀ M₀ → EndpointBound T p₁ q₁ M₁ →
      ∃ S : Lp ℂ p μ →L[ℂ] Lp ℂ q ν,
        ‖S‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ ∧
        (∀ s, (S (initialToLp μ p s) : Y →ₘ[ν] ℂ) = T s) ∧
        ∀ R : Lp ℂ p μ →L[ℂ] Lp ℂ q ν,
          (∀ s, (R (initialToLp μ p s) : Y →ₘ[ν] ℂ) = T s) → R = S

/-- The full infinite-input assertion uses a single operator already defined
on all L∞ and both endpoint bounds for that operator. -/
def InfinityAction : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SigmaFinite μ] [SigmaFinite ν]
    (q₀ q₁ q : ℝ≥0∞) [Fact (1 ≤ q₀)] [Fact (1 ≤ q₁)] [Fact (1 ≤ q)]
    (θ M₀ M₁ : ℝ), 0 < θ → θ < 1 → 0 ≤ M₀ → 0 ≤ M₁ →
    Interpolates q₀ q₁ q θ →
    ∀ T : Lp ℂ ∞ μ →ₗ[ℂ] (Y →ₘ[ν] ℂ),
      (∀ f, eLpNorm (T f) q₀ ν ≤ ENNReal.ofReal M₀ * eLpNorm f ∞ μ) →
      (∀ f, eLpNorm (T f) q₁ ν ≤ ENNReal.ofReal M₁ * eLpNorm f ∞ μ) →
      ∀ f, MemLp (T f) q ν ∧
        eLpNorm (T f) q ν ≤
          ENNReal.ofReal (M₀ ^ (1 - θ) * M₁ ^ θ) * eLpNorm f ∞ μ

end P102.U3.RieszThorinSpec
