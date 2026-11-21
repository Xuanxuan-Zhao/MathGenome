import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.GaussianLaws

/-!
Independent specifications for the projection characterization in Theorem 7.7,
paper.tex:2610–2611 and 2626–2633. The domain has its specified sigma algebra,
without completion. All natural dimensions and zero variances are included.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped RealInnerProductSpace NNReal

namespace Specs.ProbabilityFoundations.Ch07.GaussianProjectionCriterion

open _root_.ProbabilityFoundations.Ch07
open Specs.ProbabilityFoundations.Ch07.GaussianLaws

def gaussianVectorType :=
  {Ω : Type*} → [MeasurableSpace Ω] → {d : ℕ} → Measure Ω → (Ω → Euclidean d) → Prop

/-- Gaussianity uses the canonical Gaussian predicate on the pushforward law.
Its equivalence with belonging to the family N(m,S) is required below. -/
def gaussianVectorValue : gaussianVectorType :=
  fun {_Ω} [_] {_d} P X => IsGaussian (P.map X)

def gaussianProjectionsType :=
  {Ω : Type*} → [MeasurableSpace Ω] → {d : ℕ} → Measure Ω → (Ω → Euclidean d) → Prop

def gaussianProjectionsValue : gaussianProjectionsType :=
  fun {_Ω} [_] {d} P X => ∀ t : Euclidean d,
    ∃ (a : ℝ) (v : ℝ≥0), P.map (fun ω => inner ℝ t (X ω)) = gaussianReal a v

def vectorMeanType :=
  {Ω : Type*} → [MeasurableSpace Ω] → {d : ℕ} → Measure Ω → (Ω → Euclidean d) → Euclidean d

noncomputable def vectorMeanValue : vectorMeanType :=
  fun {_Ω} [_] {_d} P X => ∫ ω, X ω ∂P

def vectorCovarianceType :=
  {Ω : Type*} → [MeasurableSpace Ω] → {d : ℕ} → Measure Ω →
    (Ω → Euclidean d) → Matrix (Fin d) (Fin d) ℝ

noncomputable def vectorCovarianceValue : vectorCovarianceType :=
  fun {_Ω} [_] {_d} P X i j => covariance (fun ω => X ω i) (fun ω => X ω j) P

def projectionCriterion : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Euclidean d), Measurable X →
    (gaussianVectorValue P X ↔ gaussianProjectionsValue P X)

def gaussianLawCriterion : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Euclidean d), Measurable X →
    (gaussianVectorValue P X ↔ ∃ (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ),
      S.PosSemidef ∧ P.map X = gaussianLawValue m S)

def projectionMoments : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Euclidean d), Measurable X → gaussianProjectionsValue P X →
    Integrable X P ∧ MemLp X 2 P ∧ Integrable (fun ω => ‖X ω‖ ^ 2) P

/-- The parameters are the actual expectation and centered coordinate covariances. -/
def projectionParameters : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Euclidean d), Measurable X → gaussianProjectionsValue P X →
    (vectorCovarianceValue P X).PosSemidef ∧
      P.map X = gaussianLawValue (vectorMeanValue P X) (vectorCovarianceValue P X)

def gaussianLawProjection : Prop :=
  ∀ {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ), S.PosSemidef →
    ∀ t : Euclidean d, (gaussianLawValue m S).map (fun x => inner ℝ t x) =
      gaussianReal (inner ℝ t m) (t ⬝ᵥ S *ᵥ t).toNNReal

def projectedLaw : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Euclidean d), Measurable X →
    ∀ (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ), S.PosSemidef →
    P.map X = gaussianLawValue m S → ∀ t : Euclidean d,
    P.map (fun ω => inner ℝ t (X ω)) =
      gaussianReal (inner ℝ t m) (t ⬝ᵥ S *ᵥ t).toNNReal

def projectionParametersLaw : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Euclidean d), Measurable X → gaussianProjectionsValue P X →
    ∀ t : Euclidean d, P.map (fun ω => inner ℝ t (X ω)) =
      gaussianReal (inner ℝ t (vectorMeanValue P X))
        (t ⬝ᵥ vectorCovarianceValue P X *ᵥ t).toNNReal

def zeroVarianceProjection : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Euclidean d), Measurable X →
    ∀ (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ), S.PosSemidef →
    P.map X = gaussianLawValue m S → ∀ t : Euclidean d, t ⬝ᵥ S *ᵥ t = 0 →
    P.map (fun ω => inner ℝ t (X ω)) = Measure.dirac (inner ℝ t m)

end Specs.ProbabilityFoundations.Ch07.GaussianProjectionCriterion
