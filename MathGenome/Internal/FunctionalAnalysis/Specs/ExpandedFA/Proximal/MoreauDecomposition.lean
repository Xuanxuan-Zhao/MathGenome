import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.Definitions

/-! Independent statements for paper.tex:8523–8572, fa2:p2:prox-moreau.
The conjugate is initially EReal-valued. `ConjugateFunctionValue` removes
only the bottom constructor, using +∞ as a total default; the identification
below proves that this default is never used for proper inputs. -/
noncomputable section
open scoped InnerProductSpace
namespace ExpandedFA.Proximal.MoreauSpec
open P1.ExtendedConvexFunctions
universe u

def ConjugateFunctionType :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    ExtendedFunction H → ExtendedFunction H

def ConjugateFunctionValue : ConjugateFunctionType.{u} :=
  fun H _ _ φ w => (Spec.HilbertConjugateValue H φ w).unbotD ⊤

def ConjugateIdentification : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H), P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    ∀ w, P1.C06Conjugates.Spec.ExtendedRealValueValue (ConjugateFunctionValue H φ w) =
      Spec.HilbertConjugateValue H φ w

def ConjugateRegularity : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
      P1.ExtendedConvexFunctions.Spec.ProperValue H (ConjugateFunctionValue H φ) ∧
      P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H (ConjugateFunctionValue H φ) ∧
      P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H (ConjugateFunctionValue H φ)

/-- The witnesses explicitly record finiteness of both function values and
both envelopes. The equalities are in ordinary real arithmetic. -/
def Decomposition : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ →
    ∀ (μ : ℝ), 0 < μ → ∀ f : H,
      let u := Spec.ProximalMapValue H φ μ f
      let w := Spec.ProximalMapValue H (ConjugateFunctionValue H φ) μ⁻¹ (μ⁻¹ • f)
      u + μ • w = f ∧
      ∃ r s a b : ℝ,
        φ u = (r : WithTop ℝ) ∧
        Spec.HilbertConjugateValue H φ w = (s : EReal) ∧
        ConjugateFunctionValue H φ w = (s : WithTop ℝ) ∧
        r + s = ⟪u, w⟫_ℝ ∧
        Spec.MoreauEnvelopeValue H φ μ f = (a : EReal) ∧
        Spec.MoreauEnvelopeValue H (ConjugateFunctionValue H φ) μ⁻¹ (μ⁻¹ • f) = (b : EReal) ∧
        a + b = ‖f‖ ^ 2 / (2 * μ)

/-- The final sentence of the source, at the same datum and unit parameter. -/
def UnitParameter : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (φ : ExtendedFunction H),
    P1.ExtendedConvexFunctions.Spec.ProperValue H φ →
    P1.ExtendedConvexFunctions.Spec.ExtendedConvexValue H φ →
    P1.ExtendedConvexFunctions.Spec.LowerSemicontinuousValue H φ → ∀ f : H,
      Spec.ProximalMapValue H φ 1 f +
        Spec.ProximalMapValue H (ConjugateFunctionValue H φ) 1 f = f ∧
      Spec.MoreauEnvelopeValue H φ 1 f +
        Spec.MoreauEnvelopeValue H (ConjugateFunctionValue H φ) 1 f =
          ((‖f‖ ^ 2 / 2 : ℝ) : EReal)

end ExpandedFA.Proximal.MoreauSpec
