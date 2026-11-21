import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.Normed.Operator.Mul

/-! Independent statements for paper.tex:5645–5652.

The pairing is bilinear, including over ℂ: there is no conjugation. Exponents
are extended nonnegative reals, so the single conjugacy condition includes
(1,∞) and (∞,1). No hypothesis is placed on the positive measure.

Native Lp is used through the previously specified ordinary measurable
quotient. The last statement constructs the pairing on that literal quotient,
with linear isometries identifying the two presentations on every measurable
representative. Product integrability is a separate assertion in the source
sense (actual measurability and finite absolute integral).
-/
open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch20.IntegralPairing
open Specs.D11.Ch10.QuotientConstruction
open Specs.D11.Ch06.ScalarIntegral

def pairing_type :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q],
    Lp 𝕜 q μ →L[𝕜] Lp 𝕜 p μ →L[𝕜] 𝕜

/-- The outer argument is g; evaluation at f is the integral of f*g. -/
def pairing_value : pairing_type.{u} := fun {X} {𝕜} _ _ μ p q _ _ _ =>
  ((ContinuousLinearMap.mul 𝕜 𝕜).lpPairing μ p q).flip

def product_integrable : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [ENNReal.HolderConjugate p q]
    (f : Raw (𝕜 := 𝕜) μ p) (g : Raw (𝕜 := 𝕜) μ q),
    scalarIntegrable_value μ (fun x => f.val x * g.val x)

def pairing_eq_integral : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (g : Lp 𝕜 q μ) (f : Lp 𝕜 p μ),
    Integrable (fun x => f x * g x) μ ∧
      pairing_value μ p q g f = ∫ x, f x * g x ∂μ

/-- This applies to every actual measurable representative, rather than only
Mathlib's chosen strongly measurable versions. -/
def pairing_on_raw : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q]
    (f : Raw (𝕜 := 𝕜) μ p) (g : Raw (𝕜 := 𝕜) μ q),
    ∃ h : scalarIntegrable_value μ (fun x => f.val x * g.val x),
      pairing_value μ p q (g.property.2.toLp g.val) (f.property.2.toLp f.val) =
        scalarIntegral_value μ (fun x => f.val x * g.val x) h

def pairing_norm_bound : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q] (g : Lp 𝕜 q μ),
    ‖pairing_value μ p q g‖ ≤ ‖g‖

/-- A bounded bilinear pairing on the literal ordinary a.e. quotient, with
its original pointwise operations and source norm, as identified by the
representative-preserving linear isometries. All structures are conclusions. -/
def pairing_on_ordinary_quotient : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q],
    ∃ Gp : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ p), letI := Gp
    ∃ Vp : NormedSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ p), letI := Vp
    ∃ Gq : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ q), letI := Gq
    ∃ Vq : NormedSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ q), letI := Vq
    ∃ Fp : QuotientLp (𝕜 := 𝕜) μ p ≃ₗᵢ[𝕜] Lp 𝕜 p μ,
    ∃ Fq : QuotientLp (𝕜 := 𝕜) μ q ≃ₗᵢ[𝕜] Lp 𝕜 q μ,
    ∃ B : QuotientLp (𝕜 := 𝕜) μ q →L[𝕜] QuotientLp (𝕜 := 𝕜) μ p →L[𝕜] 𝕜,
      (∀ f : Raw (𝕜 := 𝕜) μ p, Fp (classOf f) = f.property.2.toLp f.val) ∧
      (∀ g : Raw (𝕜 := 𝕜) μ q, Fq (classOf g) = g.property.2.toLp g.val) ∧
      (∀ f : Raw (𝕜 := 𝕜) μ p, ‖classOf f‖ = (sourceNorm μ p f.val).toReal) ∧
      (∀ g : Raw (𝕜 := 𝕜) μ q, ‖classOf g‖ = (sourceNorm μ q g.val).toReal) ∧
      (∀ (f : Raw (𝕜 := 𝕜) μ p) (g : Raw (𝕜 := 𝕜) μ q),
        ∃ h : scalarIntegrable_value μ (fun x => f.val x * g.val x),
          B (classOf g) (classOf f) =
            scalarIntegral_value μ (fun x => f.val x * g.val x) h) ∧
      (∀ g, ‖B g‖ ≤ ‖g‖)

end Specs.D11.Ch20.IntegralPairing
