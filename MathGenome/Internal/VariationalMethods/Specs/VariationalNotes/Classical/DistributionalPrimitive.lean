import MathGenome.Internal.VariationalMethods.Specs.VariationalNotes.Classical.FundamentalLemma
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Independent statements for paper.tex:3109–3140 and its continuous-data
consequence at paper.tex:3157–3173. Ambient functions encode functions on (a,b).
All tests, hypotheses and conclusions are restricted to the open interval;
no boundary values or regularity outside it are imposed. -/

open MeasureTheory Set Filter
open scoped ContDiff

namespace VariationalNotes.Classical

/-- Absolute continuity is required on every compact interior interval only. -/
def LocallyACInterval {E : Type*} [PseudoMetricSpace E]
    (f : ℝ → E) (a b : ℝ) : Prop :=
  ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, AbsolutelyContinuousOnInterval f c d

/-- A representative of the given class, with the specified classical a.e. derivative. -/
def PrimitiveRepresentative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a b : ℝ) (p q f : ℝ → E) : Prop :=
  p =ᵐ[volume.restrict (Ioo a b)] f ∧ LocallyACInterval f a b ∧
    ∀ᵐ t ∂volume.restrict (Ioo a b), HasDerivAt f (q t) t

/-- The sign convention in the paper is p′ = q. -/
def WeakDerivativeInterval (m : ℕ) (a b : ℝ)
    (p q : ℝ → EuclideanSpace ℝ (Fin m)) : Prop :=
  ∀ φ : ℝ → EuclideanSpace ℝ (Fin m), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ Ioo a b →
    ∫ t in Ioo a b, inner ℝ (p t) (deriv φ t) + inner ℝ (q t) (φ t) = 0

end VariationalNotes.Classical

namespace Specs.VariationalNotes.Classical
open _root_.VariationalNotes.Classical

/-- Scalar version retained as an independently usable interface. -/
def distributionalPrimitiveScalar : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (p q : ℝ → ℝ),
    LocallyIntegrableOn p (Ioo a b) → LocallyIntegrableOn q (Ioo a b) →
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∫ t in Ioo a b, p t * deriv φ t + q t * φ t = 0) →
    ∃ f, PrimitiveRepresentative a b p q f

def distributionalPrimitive : Prop :=
  ∀ (m : ℕ) (a b : ℝ), a < b → ∀ (p q : ℝ → EuclideanSpace ℝ (Fin m)),
    LocallyIntegrableOn p (Ioo a b) → LocallyIntegrableOn q (Ioo a b) →
    WeakDerivativeInterval m a b p q → ∃ f, PrimitiveRepresentative a b p q f

/-- Agreement on overlaps is for the original class, with no arbitrary normalization. -/
def primitiveRepresentativesAgree : Prop :=
  ∀ (m : ℕ) (a b c d : ℝ) (p q f g : ℝ → EuclideanSpace ℝ (Fin m)),
    PrimitiveRepresentative a b p q f → PrimitiveRepresentative c d p q g →
    EqOn f g (Ioo a b ∩ Ioo c d)

def distributionalPrimitiveContinuous : Prop :=
  ∀ (m : ℕ) (a b : ℝ), a < b → ∀ (p q : ℝ → EuclideanSpace ℝ (Fin m)),
    LocallyIntegrableOn p (Ioo a b) → LocallyIntegrableOn q (Ioo a b) →
    WeakDerivativeInterval m a b p q →
    ContinuousOn p (Ioo a b) → ContinuousOn q (Ioo a b) →
    ContDiffOn ℝ 1 p (Ioo a b) ∧ ∀ t ∈ Ioo a b, HasDerivAt p (q t) t

def distributionalPrimitiveScalarContinuous : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (p q : ℝ → ℝ),
    LocallyIntegrableOn p (Ioo a b) → LocallyIntegrableOn q (Ioo a b) →
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b →
      ∫ t in Ioo a b, p t * deriv φ t + q t * φ t = 0) →
    ContinuousOn p (Ioo a b) → ContinuousOn q (Ioo a b) →
    ContDiffOn ℝ 1 p (Ioo a b) ∧ ∀ t ∈ Ioo a b, HasDerivAt p (q t) t

/-- The entire fundamental lemma, including the original upstream hypotheses. -/
def fundamentalLemmaAndDistributionalDerivative : Prop :=
  fundamentalLemmaAE ∧ fundamentalLemmaContinuous ∧
  fundamentalLemmaVectorAE ∧ fundamentalLemmaVectorContinuous ∧
  distributionalPrimitiveScalar ∧ distributionalPrimitive ∧
  primitiveRepresentativesAgree ∧ distributionalPrimitiveContinuous ∧
  distributionalPrimitiveScalarContinuous

end Specs.VariationalNotes.Classical
