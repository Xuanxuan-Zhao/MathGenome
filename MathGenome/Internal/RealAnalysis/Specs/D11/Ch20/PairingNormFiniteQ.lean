import MathGenome.Internal.RealAnalysis.Specs.D11.Ch20.IntegralPairing

/-! Independent statements for paper.tex:5653–5661.
The pairing is the already fixed bilinear integral of f*g, over ℝ or ℂ.
Native Lp has been identified with the ordinary measurable a.e. quotient by
Ch10.QuotientConstruction; no local-null quotient or measure-size hypothesis
is used here. The top exponent is allowed for p, so q=1 is included.
-/
open MeasureTheory
open scoped ENNReal
universe u
noncomputable section
namespace Specs.D11.Ch20.PairingNormFiniteQ

def norm_pairing : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], q ≠ ∞ → ∀ g : Lp 𝕜 q μ,
      ‖Specs.D11.Ch20.IntegralPairing.pairing_value μ p q g‖ = ‖g‖

/-- The canonical scalar-linear map g ↦ T_g is an isometric injection. -/
def isometric_injection : Prop :=
  ∀ {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    (μ : Measure X) (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    [ENNReal.HolderConjugate p q], q ≠ ∞ →
      Isometry (Specs.D11.Ch20.IntegralPairing.pairing_value (𝕜 := 𝕜) μ p q) ∧
      Function.Injective (Specs.D11.Ch20.IntegralPairing.pairing_value (𝕜 := 𝕜) μ p q)

end Specs.D11.Ch20.PairingNormFiniteQ
