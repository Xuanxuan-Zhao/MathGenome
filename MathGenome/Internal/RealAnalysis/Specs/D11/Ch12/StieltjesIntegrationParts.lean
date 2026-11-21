import MathGenome.Internal.RealAnalysis.Specs.D11.Ch12.NormalizedStieltjes
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch14.ScalarIntegration
import Mathlib.MeasureTheory.VectorMeasure.SetIntegral
import Mathlib.MeasureTheory.Measure.Prod

/-! Stieltjes integration by parts, paper.tex:4157–4182.
The measures and NBV functions are the shared canonical Borel objects.
The scalar conclusions use the upstream Jordan integrals, with absolute
integrability established before an integral is evaluated. -/
open Set MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace Specs.D11.Ch12.StieltjesIntegrationParts
open Specs.D11.Ch12.ScalarStieltjesCorrespondence
open Specs.D11.Ch14.ScalarIntegration

def bounded_borel : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (F : ℝ → 𝕜), NBV_value F →
      Measurable F ∧ (∃ C : ℝ, ∀ x, ‖F x‖ ≤ C) ∧
      IsFiniteMeasure (stieltjesMeasure_value F).variation

def continuous_atomless : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (F : ℝ → 𝕜), NBV_value F → Continuous F →
    (∀ x : ℝ, stieltjesMeasure_value F {x} = 0) ∧
    NullSingletonClass (stieltjesMeasure_value F).variation

def diagonal_null : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (F G : ℝ → 𝕜), NBV_value F → NBV_value G →
    (Continuous F ∨ Continuous G) →
    ((stieltjesMeasure_value F).variation.prod
      (stieltjesMeasure_value G).variation) (diagonal ℝ) = 0

/-- Bilinear multiplication; no complex conjugation. -/
def native_integration_parts : Prop :=
  ∀ {𝕜 : Type} [RCLike 𝕜] (F G : ℝ → 𝕜), NBV_value F → NBV_value G →
    (Continuous F ∨ Continuous G) → ∀ a b : ℝ, a < b →
    (∫ᵛ x in Ioc a b, F x ∂[ContinuousLinearMap.lsmul ℝ 𝕜; stieltjesMeasure_value G]) +
    (∫ᵛ x in Ioc a b, G x ∂[ContinuousLinearMap.lsmul ℝ 𝕜; stieltjesMeasure_value F]) =
      F b * G b - F a * G a

def signed_integration_parts : Prop :=
  ∀ (F G : ℝ → ℝ), NBV_value F → NBV_value G →
    (Continuous F ∨ Continuous G) → ∀ a b : ℝ, a < b →
    ∃ hFG : signedIntegrable_value (stieltjesMeasure_value G) ((Ioc a b).indicator F),
    ∃ hGF : signedIntegrable_value (stieltjesMeasure_value F) ((Ioc a b).indicator G),
      signedIntegral_value (stieltjesMeasure_value G) ((Ioc a b).indicator F) hFG +
      signedIntegral_value (stieltjesMeasure_value F) ((Ioc a b).indicator G) hGF =
        F b * G b - F a * G a

def complex_integration_parts : Prop :=
  ∀ (F G : ℝ → ℂ), NBV_value F → NBV_value G →
    (Continuous F ∨ Continuous G) → ∀ a b : ℝ, a < b →
    ∃ hFG : complexIntegrable_value (stieltjesMeasure_value G) ((Ioc a b).indicator F),
    ∃ hGF : complexIntegrable_value (stieltjesMeasure_value F) ((Ioc a b).indicator G),
      complexIntegral_value (stieltjesMeasure_value G) ((Ioc a b).indicator F) hFG +
      complexIntegral_value (stieltjesMeasure_value F) ((Ioc a b).indicator G) hGF =
        F b * G b - F a * G a

end Specs.D11.Ch12.StieltjesIntegrationParts
