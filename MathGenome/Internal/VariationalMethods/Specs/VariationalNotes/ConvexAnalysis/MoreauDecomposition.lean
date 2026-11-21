import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.EnvelopeGradient
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.ConvexAnalysis.Conjugates
import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Existence.HilbertProjection

/-! Independent statements for paper.tex §v02-08, Theorem `thm:moreau`
and its indicator specialization (1276–1332). The continuous-dual conjugate
is transported through the real Riesz equivalence. Removing the bottom
constructor is justified by the identification theorem for proper inputs.
All spaces below are arbitrary real Hilbert spaces, including the zero space.
-/
noncomputable section
universe u
namespace VariationalNotes.ConvexAnalysis.Specs

def hilbertConjugateFunctionType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H],
    (H → WithTop ℝ) → H → WithTop ℝ

def hilbertConjugateFunction : hilbertConjugateFunctionType.{u} :=
  fun f w => (conjugate f (InnerProductSpace.toDual ℝ _ w)).unbotD ⊤

def hilbertConjugateFunction_identification : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → ∀ w : H,
      toEReal (hilbertConjugateFunction f w) =
        conjugate f (InnerProductSpace.toDual ℝ H w)

def hilbertConjugateFunction_regular : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
      Proper (hilbertConjugateFunction f) ∧ IsConvex (hilbertConjugateFunction f) ∧
        IsLowerSemicontinuous (hilbertConjugateFunction f)

def moreau_decomposition : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ → ∀ x : H,
      x = proximalMap f μ x +
        μ • proximalMap (hilbertConjugateFunction f) μ⁻¹ (μ⁻¹ • x) ∧
      moreauEnvelope f μ x +
        moreauEnvelope (hilbertConjugateFunction f) μ⁻¹ (μ⁻¹ • x) =
          ((‖x‖ ^ 2 / (2 * μ) : ℝ) : EReal)

def proximalMap_indicator_eq_projection : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (C : Set H) (hne : C.Nonempty) (hclosed : IsClosed C) (hconv : Convex ℝ C),
    ∀ μ : ℝ, 0 < μ → ∀ x : H,
      proximalMap (indicator C) μ x =
        VariationalNotes.Existence.Specs.realProjection C hne hclosed hconv x

/-- The full envelope-gradient and decomposition theorem, with the original
parameter and scaling conventions. The real envelope is the real value of
the actual extended-real infimum, as recorded by the first conjunct. -/
def moreau_theorem : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → WithTop ℝ), Proper f → IsConvex f → IsLowerSemicontinuous f →
    ∀ μ : ℝ, 0 < μ →
      (∀ x : H, moreauEnvelope f μ x = (realMoreauEnvelope f μ x : EReal)) ∧
      ConvexOn ℝ Set.univ (realMoreauEnvelope f μ) ∧
      (∀ x : H, HasFDerivAt (realMoreauEnvelope f μ)
        (InnerProductSpace.toDual ℝ H (moreauGradient f μ x)) x) ∧
      (∀ x y : H, ‖moreauGradient f μ x - moreauGradient f μ y‖ ≤ ‖x - y‖ / μ) ∧
      (∀ x : H,
        x = proximalMap f μ x +
          μ • proximalMap (hilbertConjugateFunction f) μ⁻¹ (μ⁻¹ • x) ∧
        moreauEnvelope f μ x +
          moreauEnvelope (hilbertConjugateFunction f) μ⁻¹ (μ⁻¹ • x) =
            ((‖x‖ ^ 2 / (2 * μ) : ℝ) : EReal))

end VariationalNotes.ConvexAnalysis.Specs
