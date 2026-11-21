import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Analysis.RCLike.Basic

/-!
Independent specification of the native ordinary a.e. scalar Lp pairing.
Source: paper.tex, conventions at 16700–16715 and fa2:p4:lp-duality.
No sigma-finiteness or finite mass is required for this construction, including
(p,q) = (1,∞) and (∞,1). Surjectivity and isometry belong to later duality goals.
-/

open MeasureTheory
open scoped ENNReal

universe u
noncomputable section

namespace ExpandedFA.FunctionSpaces.ScalarLpIntegralPairingSpec

/-- Native Lp, whose equality relation is ordinary equality μ-a.e. -/
def ScalarLpType :=
  ∀ {X : Type u} (𝕜 : Type) [MeasurableSpace X] [RCLike 𝕜], ℝ≥0∞ → Measure X → Type u

def ScalarLpValue : ScalarLpType.{u} := fun 𝕜 _ _ p μ => Lp 𝕜 p μ

def IntegralPairingType :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q],
    Lp 𝕜 q μ →L[𝕜] (Lp 𝕜 p μ →L[𝕜] 𝕜)

/-- Multiplication followed by the L¹ integral, with the density first.
Multiplication is bilinear over ℂ as well as ℝ: there is no conjugation. -/
def IntegralPairingValue : IntegralPairingType.{u} :=
  fun μ p q => ((ContinuousLinearMap.mul _ _).lpPairing μ p q).flip

/-- Equality of raw representatives is ordinary μ-null equality. -/
def OrdinaryAEIdentification : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (f g : X → 𝕜) (hf : MemLp f p μ) (hg : MemLp g p μ),
    hf.toLp f = hg.toLp g ↔ μ {x | f x ≠ g x} = 0

/-- Every native class has a measurable representative of finite Lp norm. -/
def MeasurableRepresentative : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (F : Lp 𝕜 p μ),
    ∃ (f : X → 𝕜) (hf : MemLp f p μ), Measurable f ∧ hf.toLp f = F

/-- The norm is the native integral-power norm, or ordinary essential supremum
at infinity, on every representative. -/
def SourceNorm : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p : ℝ≥0∞) (f : X → 𝕜) (hf : MemLp f p μ),
    ‖hf.toLp f‖ = (eLpNorm f p μ).toReal

def ProductIntegrable : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (f g : X → 𝕜),
    MemLp f p μ → MemLp g q μ → Integrable (fun x => f x * g x) μ

def PairingIntegral : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (g : Lp 𝕜 q μ) (f : Lp 𝕜 p μ),
    Integrable (fun x => f x * g x) μ ∧
      IntegralPairingValue μ p q g f = ∫ x, f x * g x ∂μ

def PairingOnRepresentatives : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (f g : X → 𝕜) (hf : MemLp f p μ) (hg : MemLp g q μ),
    IntegralPairingValue μ p q (hg.toLp g) (hf.toLp f) = ∫ x, f x * g x ∂μ

def PairingApplyBound : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (g : Lp 𝕜 q μ) (f : Lp 𝕜 p μ),
    ‖IntegralPairingValue μ p q g f‖ ≤ ‖g‖ * ‖f‖

def PairingNormBound : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (g : Lp 𝕜 q μ),
    ‖IntegralPairingValue μ p q g‖ ≤ ‖g‖

def PairingOperatorNormBound : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], ‖IntegralPairingValue (𝕜 := 𝕜) μ p q‖ ≤ 1

/-- Explicit scalar linearity in both slots, including the complex case. -/
def PairingScalarLinear : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (c : 𝕜) (g : Lp 𝕜 q μ) (f : Lp 𝕜 p μ),
    IntegralPairingValue μ p q (c • g) f = c * IntegralPairingValue μ p q g f ∧
    IntegralPairingValue μ p q g (c • f) = c * IntegralPairingValue μ p q g f

end ExpandedFA.FunctionSpaces.ScalarLpIntegralPairingSpec
