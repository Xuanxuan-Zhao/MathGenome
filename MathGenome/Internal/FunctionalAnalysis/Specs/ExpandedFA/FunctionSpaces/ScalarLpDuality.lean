import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarLpIntegralPairing

/-!
Independent statements for `fa2:p4:lp-duality`, paper.tex:16788–16825.

The scalar field is real or complex (`RCLike`). These are native ordinary
μ-a.e. Lp classes and the continuous scalar-linear dual. The fixed upstream
pairing is g ↦ (f ↦ ∫ f*g); no conjugation is inserted. The finite-exponent
condition is `p ≠ ∞` together with `Fact (1 ≤ p)`, and Hölder conjugacy
specifies q. No measure-size assumption occurs at strictly interior p.
The endpoint p=1 retains sigma-finiteness and ordinary L∞.

Uniqueness is for ordinary μ-a.e. equality, with no norm hypothesis on a
competing density. The last statement also supplies a measurable raw density.
-/

open MeasureTheory
open scoped ENNReal

universe u
noncomputable section

namespace ExpandedFA.FunctionSpaces.ScalarLpDualitySpec

/-- Existence, uniqueness in the ordinary quotient, product integrability,
the representation formula, and the exact norm for sigma-finite measures. -/
def SigmaFiniteRepresentation : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    p ≠ ∞ → ∀ L : Lp 𝕜 p μ →L[𝕜] 𝕜,
    ∃! g : Lp 𝕜 q μ,
      (∀ f : Lp 𝕜 p μ, Integrable (fun x => f x * g x) μ ∧
        L f = ∫ x, f x * g x ∂μ) ∧ ‖g‖ = ‖L‖

/-- The same complete representation for arbitrary positive measures and
strictly interior exponents. -/
def ArbitraryMeasureRepresentation : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    1 < p → p ≠ ∞ → ∀ L : Lp 𝕜 p μ →L[𝕜] 𝕜,
    ∃! g : Lp 𝕜 q μ,
      (∀ f : Lp 𝕜 p μ, Integrable (fun x => f x * g x) μ ∧
        L f = ∫ x, f x * g x ∂μ) ∧ ‖g‖ = ‖L‖

/-- The already scalar-linear continuous pairing is an isometric bijection
onto the continuous linear dual, for every finite p on sigma-finite measures. -/
def SigmaFiniteIsometricBijection : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    p ≠ ∞ →
    Isometry (ScalarLpIntegralPairingSpec.IntegralPairingValue (𝕜 := 𝕜) μ p q) ∧
      Function.Bijective (ScalarLpIntegralPairingSpec.IntegralPairingValue (𝕜 := 𝕜) μ p q)

/-- No sigma-finiteness, semifiniteness, or localizability is assumed. -/
def ArbitraryMeasureIsometricBijection : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    1 < p → p ≠ ∞ →
    Isometry (ScalarLpIntegralPairingSpec.IntegralPairingValue (𝕜 := 𝕜) μ p q) ∧
      Function.Bijective (ScalarLpIntegralPairingSpec.IntegralPairingValue (𝕜 := 𝕜) μ p q)

/-- Uniqueness means ordinary a.e. equality on the original measure. No norm
equality is assumed for the competing densities. This includes p=1 on a
sigma-finite measure, and all interior p on an arbitrary measure. -/
def OrdinaryAeUniqueness : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    p ≠ ∞ → (SigmaFinite μ ∨ 1 < p) → ∀ g h : Lp 𝕜 q μ,
    (∀ f : Lp 𝕜 p μ, (∫ x, f x * g x ∂μ) = ∫ x, f x * h x ∂μ) ↔
      (g : X → 𝕜) =ᵐ[μ] (h : X → 𝕜)

/-- Explicit endpoint specialization, retaining the ordinary L-infinity
class and exact norm. The preceding uniqueness statement also applies here. -/
def OneInfinityRepresentation : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) [SigmaFinite μ] (L : Lp 𝕜 1 μ →L[𝕜] 𝕜),
    ∃! g : Lp 𝕜 ∞ μ,
      (∀ f : Lp 𝕜 1 μ, Integrable (fun x => f x * g x) μ ∧
        L f = ∫ x, f x * g x ∂μ) ∧ ‖g‖ = ‖L‖

/-- The exact operator norm of the fixed integral functional. -/
def PairingExactNorm : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    p ≠ ∞ → (SigmaFinite μ ∨ 1 < p) → ∀ g : Lp 𝕜 q μ,
      ‖ScalarLpIntegralPairingSpec.IntegralPairingValue μ p q g‖ = ‖g‖

/-- A measurable ordinary representative exists, and all competing Lq
representatives agree μ-a.e.; its norm is the original integral-power norm
(or essential-supremum norm at infinity). -/
def MeasurableDensityRepresentation : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞)
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q],
    p ≠ ∞ → (SigmaFinite μ ∨ 1 < p) → ∀ L : Lp 𝕜 p μ →L[𝕜] 𝕜,
    ∃ g : X → 𝕜, Measurable g ∧ MemLp g q μ ∧
      (∀ f : Lp 𝕜 p μ, Integrable (fun x => f x * g x) μ ∧
        L f = ∫ x, f x * g x ∂μ) ∧
      (eLpNorm g q μ).toReal = ‖L‖ ∧
      ∀ h : X → 𝕜, MemLp h q μ →
        (∀ f : Lp 𝕜 p μ, L f = ∫ x, f x * h x ∂μ) → h =ᵐ[μ] g

end ExpandedFA.FunctionSpaces.ScalarLpDualitySpec
