import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.GaussianProjectionCriterion
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Independence.Basic

/-!
The i.i.d. central limit theorem, paper.tex:3076–3098.
The sequence is indexed starting at zero; `range n` comprises its first n terms.
Finite second moment is integrability of the squared Euclidean norm. The limit
is the Borel Gaussian with the actual covariance, including singular covariance
and dimension zero. `TendstoInDistribution` is weak convergence of probability
laws, with the canonical identity variable on the limiting Gaussian space.
No completeness of the source probability space is assumed.
-/

open MeasureTheory ProbabilityTheory Filter
open _root_.ProbabilityFoundations.Ch07
open Specs.ProbabilityFoundations.Ch07.GaussianLaws
open Specs.ProbabilityFoundations.Ch07.GaussianProjectionCriterion

namespace Specs.ProbabilityFoundations.Ch09.IidCentralLimitTheorem

instance {d : ℕ} (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ) :
    IsProbabilityMeasure (gaussianLawValue m S) := by
  unfold gaussianLawValue
  infer_instance

/-- The real theorem retains variance zero and only a finite second moment. -/
def scalarClt : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ), (∀ k, Measurable (X k)) →
    iIndepFun X P → (∀ k, IdentDistrib (X k) (X 0) P P) →
    Integrable (fun ω => (X 0 ω) ^ 2) P →
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, (X k ω - ∫ ω, X 0 ω ∂P))
      atTop id (fun _ => P) (gaussianReal 0 (Var[X 0; P]).toNNReal)

/-- The covariance is the matrix of centered coordinate product integrals. -/
def vectorClt : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → Euclidean d),
    (∀ k, Measurable (X k)) → iIndepFun X P →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    Integrable (fun ω => ‖X 0 ω‖ ^ 2) P →
    TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ •
        ∑ k ∈ Finset.range n, (X k ω - vectorMeanValue P (X 0)))
      atTop id (fun _ => P) (gaussianLawValue 0 (vectorCovarianceValue P (X 0)))

/-- A common probability-one set works for all summands and all partial sums.
Independence is not needed for this consequence of identical distributions. -/
def zeroVariance : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ), (∀ k, Measurable (X k)) →
    (∀ k, IdentDistrib (X k) (X 0) P P) →
    Integrable (fun ω => (X 0 ω) ^ 2) P → Var[X 0; P] = 0 →
    ∀ᵐ ω ∂P,
      (∀ k, X k ω - ∫ ω, X 0 ω ∂P = 0) ∧
      (∀ n, ∑ k ∈ Finset.range n, (X k ω - ∫ ω, X 0 ω ∂P) = 0) ∧
      (∀ (n : ℕ), (Real.sqrt n)⁻¹ *
        ∑ k ∈ Finset.range n, (X k ω - ∫ ω, X 0 ω ∂P) = 0)

end Specs.ProbabilityFoundations.Ch09.IidCentralLimitTheorem
