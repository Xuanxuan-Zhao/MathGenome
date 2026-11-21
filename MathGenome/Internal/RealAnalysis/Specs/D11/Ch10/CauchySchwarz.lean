import MathGenome.Internal.RealAnalysis.Specs.D11.Ch10.LpDefinition
import MathGenome.Internal.RealAnalysis.Specs.D11.Ch06.ScalarIntegral

/-! Independent statements for paper.tex:3334–3343.
Square integrability uses the shared raw space, including ordinary
measurability. The nonnegative integral and the scalar integral are the
shared source constructions. The existential supplies integrability before
the scalar integral is evaluated. Finite ENNReal norms are converted to their
real values in the scalar bound. No completeness or mass assumption is used.
-/
open Set MeasureTheory
open scoped ENNReal ComplexConjugate
universe u
noncomputable section
namespace Specs.D11.Ch10.CauchySchwarz
open LpDefinition Specs.D11.Ch05.NonnegativeIntegral Specs.D11.Ch06.ScalarIntegral

def product_bound : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f g : X → 𝕜),
    f ∈ rawLp_value μ 2 → g ∈ rawLp_value μ 2 →
    scalarIntegrable_value μ (fun x => f x * g x) ∧
      nonnegativeIntegral_value μ (fun x => ENNReal.ofReal ‖f x * g x‖) ≤
        powerNorm_value μ 2 f * powerNorm_value μ 2 g

def integral_bound : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] (μ : Measure X) (f g : X → 𝕜),
    f ∈ rawLp_value μ 2 → g ∈ rawLp_value μ 2 →
    ∃ h : scalarIntegrable_value μ (fun x => f x * conj (g x)),
      ‖scalarIntegral_value μ (fun x => f x * conj (g x)) h‖ ≤
        (powerNorm_value μ 2 f).toReal * (powerNorm_value μ 2 g).toReal

end Specs.D11.Ch10.CauchySchwarz
