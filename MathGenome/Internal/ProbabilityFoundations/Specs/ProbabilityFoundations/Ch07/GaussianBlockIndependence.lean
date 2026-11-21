import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch07.GaussianLaws
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
Independent specifications for the block criterion in paper.tex, Theorem 7.7,
lines 2613–2615 and 2634–2638. Blocks are arbitrary disjoint finite subsets,
with no covering or nonemptiness requirement. `HasGaussianLaw X P` asserts
Gaussianity of the whole pushforward law, not just of its coordinates.
Covariance is Mathlib's integral of the product of centered real variables.
The explicit-law version identifies it with the given matrix entries.
-/

open MeasureTheory ProbabilityTheory Matrix

namespace Specs.ProbabilityFoundations.Ch07.GaussianBlockIndependence

open _root_.ProbabilityFoundations.Ch07
open Specs.ProbabilityFoundations.Ch07.GaussianLaws

def blocksIndependentIffCovarianceZero : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d), HasGaussianLaw X P →
    ∀ (I J : Finset (Fin d)), Disjoint I J →
      (IndepFun (fun ω (i : I) => X ω i) (fun ω (j : J) => X ω j) P ↔
        ∀ (i : I) (j : J), covariance (fun ω => X ω i) (fun ω => X ω j) P = 0)

def coordinateCovarianceIntegrable : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d), HasGaussianLaw X P →
    ∀ i j : Fin d,
      Integrable (fun ω => (X ω i - ∫ a, X a i ∂P) *
        (X ω j - ∫ a, X a j ∂P)) P

def coordinateCovarianceEq : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d), Measurable X →
    ∀ (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ), S.PosSemidef →
    P.map X = gaussianLawValue m S →
    ∀ i j : Fin d, covariance (fun ω => X ω i) (fun ω => X ω j) P = S i j

def blocksIndependentIffCrossMatrixZero : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {d : ℕ} (X : Ω → Euclidean d), Measurable X →
    ∀ (m : Euclidean d) (S : Matrix (Fin d) (Fin d) ℝ), S.PosSemidef →
    P.map X = gaussianLawValue m S →
    ∀ (I J : Finset (Fin d)), Disjoint I J →
      (IndepFun (fun ω (i : I) => X ω i) (fun ω (j : J) => X ω j) P ↔
        ∀ (i : I) (j : J), S i j = 0)

end Specs.ProbabilityFoundations.Ch07.GaussianBlockIndependence
