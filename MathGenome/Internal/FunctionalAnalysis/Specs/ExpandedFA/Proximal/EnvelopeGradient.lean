import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.MoreauDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Real Hilbert Moreau envelopes, for every positive real parameter.
The real-valued representative is tied to the actual EReal infimum by
`Regularity`, so the total `toReal` default cannot affect the conclusion. -/
noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Proximal.EnvelopeSpec
open P1.ExtendedConvexFunctions
universe u

def RealEnvelopeType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → ℝ → H → ℝ

def RealEnvelopeValue : RealEnvelopeType.{u} :=
  fun H _ _ φ μ f => (Spec.MoreauEnvelopeValue H φ μ f).toReal

def GradientType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → ℝ → H → H

def GradientValue : GradientType.{u} :=
  fun H _ _ φ μ f => μ⁻¹ • (f - Spec.ProximalMapValue H φ μ f)

def Regularity : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ μ : ℝ, 0 < μ →
      (∀ f, Spec.MoreauEnvelopeValue H φ μ f = (RealEnvelopeValue H φ μ f : EReal)) ∧
      ContDiff ℝ 1 (RealEnvelopeValue H φ μ) ∧
      (∀ f, HasFDerivAt (RealEnvelopeValue H φ μ)
        (InnerProductSpace.toDual ℝ H (GradientValue H φ μ f)) f) ∧
      (∀ f, fderiv ℝ (RealEnvelopeValue H φ μ) f =
        InnerProductSpace.toDual ℝ H (GradientValue H φ μ f)) ∧
      Continuous (fun f => fderiv ℝ (RealEnvelopeValue H φ μ) f) ∧
      Continuous (GradientValue H φ μ)

/-- The Riesz gradient is the conjugate proximal point and attains the
Fenchel dual maximum. All finite-energy identities are in real arithmetic;
the global dual comparison includes infinite conjugate values. -/
def DualIdentification : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ μ : ℝ, 0 < μ → ∀ f : H,
      let u := Spec.ProximalMapValue H φ μ f
      let w := GradientValue H φ μ f
      w = Spec.ProximalMapValue H (MoreauSpec.ConjugateFunctionValue H φ) μ⁻¹ (μ⁻¹ • f) ∧
      ∃ r s : ℝ, φ u = (r : WithTop ℝ) ∧
        Spec.HilbertConjugateValue H φ w = (s : EReal) ∧
        r + s = ⟪u, w⟫_ℝ ∧
        RealEnvelopeValue H φ μ f = ⟪w, f⟫_ℝ - s - μ * ‖w‖ ^ 2 / 2 ∧
        ∀ z : H,
          (⟪z, f⟫_ℝ : EReal) - Spec.HilbertConjugateValue H φ z -
            ((μ * ‖z‖ ^ 2 / 2 : ℝ) : EReal) ≤ Spec.MoreauEnvelopeValue H φ μ f

end ExpandedFA.Proximal.EnvelopeSpec
