import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch04.EssentialBounds
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch01.ExhaustionRestriction
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Independent statements for paper.tex:1841–1876. All scalar functions
are finite valued; integrability includes measurability on the original
sigma-algebra. Norm is real absolute value or complex modulus. Absolute
integrals use the shared nonnegative integral in ℝ≥0∞. The finite bound M
is real; `ofReal M` also handles a negative M (possible only on a null
space under the asserted a.e. norm bound). No completeness or mass
hypothesis on the ambient measure is imposed. -/
open Set MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch06.DominationInvariance
open ScalarIntegral
open Specs.D11.Ch05.NonnegativeIntegral
open Specs.D11.Ch04.AeCommonException
open Specs.D11.Ch04.EssentialBounds
open Specs.D11.Ch01.ExhaustionRestriction

/-- Domination gives both integrability and the absolute-integral estimate. -/
def integrable_domination : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜) (g : X → ℝ),
    Measurable f → scalarIntegrable_value μ g → (∀ x, 0 ≤ g x) →
    almostEverywhere_value μ (fun x => ‖f x‖ ≤ g x) →
    scalarIntegrable_value μ f ∧
      nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x‖) ≤
        nonnegativeIntegral_value μ (fun x => ENNReal.ofReal (g x))

def finite_support_bound : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜)
    (E : Set X) (M : ℝ), Measurable f → MeasurableSet E → μ E < ∞ →
    (∀ x, x ∉ E → f x = 0) →
    almostEverywhere_value μ (fun x => ‖f x‖ ≤ M) →
    scalarIntegrable_value μ f ∧
      nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x‖) ≤
        ENNReal.ofReal M * μ E

def bounded_multiplier : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f h : X → 𝕜),
    scalarIntegrable_value μ f → Measurable h → essentiallyBounded_value μ h →
    scalarIntegrable_value μ (fun x => h x * f x) ∧
      nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖h x * f x‖) ≤
        essentialSupNorm_value μ h *
          nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x‖)

def ae_integrable_iff : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f g : X → 𝕜),
    Measurable f → Measurable g → aeEq_value μ f g →
    (scalarIntegrable_value μ f ↔ scalarIntegrable_value μ g)

def ae_integral_eq : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f g : X → 𝕜)
    (hf : scalarIntegrable_value μ f) (hg : scalarIntegrable_value μ g),
    aeEq_value μ f g →
    scalarIntegral_value μ f hf = scalarIntegral_value μ g hg ∧
    nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x‖) =
      nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖g x‖)

/-- Restriction and extension by zero are both integrable and agree in value. -/
def restriction : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    scalarIntegrable_value μ f → ∀ E : Set X, MeasurableSet E →
    ∃ (hr : scalarIntegrable_value (restrictOnSpace_value μ E) f)
      (hi : scalarIntegrable_value μ (E.indicator f)),
      scalarIntegral_value (restrictOnSpace_value μ E) f hr =
        scalarIntegral_value μ (E.indicator f) hi ∧
      nonnegativeIntegral_value (restrictOnSpace_value μ E) (fun x => ENNReal.ofReal ‖f x‖) =
        nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖E.indicator f x‖)

/-- The restriction is also the scalar integral on the canonical trace space. -/
def restriction_subtype : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜),
    scalarIntegrable_value μ f → ∀ E : Set X, MeasurableSet E →
    ∃ (hs : scalarIntegrable_value (restrictToSubtype_value μ E) (fun x : E => f x))
      (hr : scalarIntegrable_value (restrictOnSpace_value μ E) f),
      scalarIntegral_value (restrictToSubtype_value μ E) (fun x : E => f x) hs =
        scalarIntegral_value (restrictOnSpace_value μ E) f hr ∧
      nonnegativeIntegral_value (restrictToSubtype_value μ E)
          (fun x : E => ENNReal.ofReal ‖f x‖) =
        nonnegativeIntegral_value (restrictOnSpace_value μ E) (fun x => ENNReal.ofReal ‖f x‖)

def null_removal : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f : X → 𝕜)
    (hf : scalarIntegrable_value μ f) (N : Set X),
    MeasurableSet N → μ N = 0 →
    ∃ (hr : scalarIntegrable_value (restrictOnSpace_value μ Nᶜ) f)
      (hi : scalarIntegrable_value μ (Nᶜ.indicator f)),
      scalarIntegral_value (restrictOnSpace_value μ Nᶜ) f hr = scalarIntegral_value μ f hf ∧
      scalarIntegral_value μ (Nᶜ.indicator f) hi = scalarIntegral_value μ f hf ∧
      nonnegativeIntegral_value (restrictOnSpace_value μ Nᶜ) (fun x => ENNReal.ofReal ‖f x‖) =
        nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x‖) ∧
      nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖Nᶜ.indicator f x‖) =
        nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x‖)

end Specs.D11.Ch06.DominationInvariance
