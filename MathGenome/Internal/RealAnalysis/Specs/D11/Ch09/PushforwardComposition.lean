import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.TransportNonnegative
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch09.TransportIntegrable
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.QuotientConstruction
import Mathlib.MeasureTheory.MeasurableSpace.Instances
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-! Independent scope for paper.tex:3022–3038. All measurable spaces and
positive measures are arbitrary. The exponent is ENNReal, so `1 ≤ p` includes
infinity. The native Lp statement is supplemented by the actual ordinary
measurable-function quotient and its representative formula. The normed
structures and bridges in that statement are conclusions, not assumptions.
The final statement is the displayed two-point probability counterexample.
-/
open Set MeasureTheory
open scoped ENNReal
universe u v w
noncomputable section
namespace Specs.D11.Ch09.PushforwardComposition
open Specs.D11.Ch09.Pushforward Specs.D11.Ch06.ScalarIntegral
open Specs.D11.Ch10.QuotientConstruction

def functoriality : Prop :=
  ∀ {X : Type u} {Y : Type v} {Z : Type w}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (u : X → Y) (v : Y → Z) (hu : Measurable u) (hv : Measurable v) (μ : Measure X),
    pushforward_value (v ∘ u) (hv.comp hu) μ =
      pushforward_value v hv (pushforward_value u hu μ)

def preserves_nonnegative : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y),
    pushforward_value u hu μ = ν → ∀ h : Y → ℝ≥0∞, Measurable h →
    Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value ν h =
      Specs.D11.Ch05.NonnegativeIntegral.nonnegativeIntegral_value μ (h ∘ u)

def preserves_scalar : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y),
    pushforward_value u hu μ = ν → ∀ h : Y → 𝕜, Measurable h →
    (scalarIntegrable_value ν h ↔ scalarIntegrable_value μ (h ∘ u)) ∧
    (∀ hh : scalarIntegrable_value ν h,
      ∃ hc : scalarIntegrable_value μ (h ∘ u),
        scalarIntegral_value ν h hh = scalarIntegral_value μ (h ∘ u) hc)

/-- Native isometry with the exact pullback formula on all measurable raw
representatives. This determines the map on every class. -/
def pullback_isometry : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y),
    pushforward_value u hu μ = ν → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ T : Lp 𝕜 p ν →ₗᵢ[𝕜] Lp 𝕜 p μ,
      ∀ (h : Y → 𝕜) (_hh : Measurable h) (hm : MemLp h p ν),
        ∃ hc : MemLp (h ∘ u) p μ, T (hm.toLp h) = hc.toLp (h ∘ u)

/-- The same map on the canonical ordinary quotient. The representative
formulas for Fμ and Fν identify its operations and norm with the previously
specified Lp construction. No local-null quotient is used. -/
def quotient_pullback : Prop :=
  ∀ {X : Type u} {Y : Type v} {𝕜 : Type}
    [MeasurableSpace X] [MeasurableSpace Y] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (u : X → Y) (hu : Measurable u) (μ : Measure X) (ν : Measure Y),
    pushforward_value u hu μ = ν → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)],
    ∃ Gμ : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) μ p), letI := Gμ
    ∃ Vμ : NormedSpace 𝕜 (QuotientLp (𝕜 := 𝕜) μ p), letI := Vμ
    ∃ Gν : NormedAddCommGroup (QuotientLp (𝕜 := 𝕜) ν p), letI := Gν
    ∃ Vν : NormedSpace 𝕜 (QuotientLp (𝕜 := 𝕜) ν p), letI := Vν
    ∃ Fμ : QuotientLp (𝕜 := 𝕜) μ p ≃ₗᵢ[𝕜] Lp 𝕜 p μ,
    ∃ Fν : QuotientLp (𝕜 := 𝕜) ν p ≃ₗᵢ[𝕜] Lp 𝕜 p ν,
    ∃ T : QuotientLp (𝕜 := 𝕜) ν p →ₗᵢ[𝕜] QuotientLp (𝕜 := 𝕜) μ p,
      (∀ h : Raw (𝕜 := 𝕜) μ p, Fμ (classOf h) = h.property.2.toLp h.val) ∧
      (∀ h : Raw (𝕜 := 𝕜) ν p, Fν (classOf h) = h.property.2.toLp h.val) ∧
      (∀ h : Raw (𝕜 := 𝕜) ν p, ∃ hc : MemLp (h.val ∘ u) p μ,
        T (classOf h) = classOf ⟨h.val ∘ u, h.property.1.comp hu, hc⟩)

/-- Exactly the two half-masses in the source counterexample. -/
def twoPointMeasure : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac false + (1 / 2 : ℝ≥0∞) • Measure.dirac true

def two_point_not_onto : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)],
    twoPointMeasure {false} = 1 / 2 ∧ twoPointMeasure {true} = 1 / 2 ∧
    twoPointMeasure univ = 1 ∧
    pushforward_value (fun _ : Bool => ()) measurable_const twoPointMeasure =
      Measure.dirac () ∧
    ∃ T : Lp 𝕜 p (Measure.dirac ()) →ₗᵢ[𝕜] Lp 𝕜 p twoPointMeasure,
      (∀ h, (T h : Bool → 𝕜) =ᵐ[twoPointMeasure] (fun _ => h ())) ∧
      (∀ f : Lp 𝕜 p twoPointMeasure,
        f ∈ Set.range T ↔ ∃ c : 𝕜, (f : Bool → 𝕜) =ᵐ[twoPointMeasure] (fun _ => c)) ∧
      (∃ hm : MemLp (fun b : Bool => if b then (1 : 𝕜) else 0) p twoPointMeasure,
        hm.toLp (fun b : Bool => if b then (1 : 𝕜) else 0) ∉ Set.range T)

end Specs.D11.Ch09.PushforwardComposition
