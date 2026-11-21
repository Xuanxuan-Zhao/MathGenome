import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.FourierHilbertScale
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.DistributionPaleyWiener

/-! The remaining clauses of `fa2:p4:sobolev-hilbert`, paper.tex:17996–17999.
The spaces and their distribution realization are the shared Fourier scale.
All dimensions, including zero, and all real orders are retained. -/

noncomputable section
open MeasureTheory TopologicalSpace
open scoped SchwartzMap ContDiff

namespace ExpandedFA.Sobolev.LocalOperations
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

/-- Iterated distributional coordinate differentiation, including order zero. -/
def wordDerivative {d : ℕ} : List (Fin d) → Tempered ℂ d → Tempered ℂ d
  | [], T => T
  | i :: w, T => wordDerivative w (temperedPartial i T)

/-- Multi-index differentiation is the usual iteration of negative transposes. -/
def multiDerivative {d : ℕ} (α : Fin d → ℕ) (T : Tempered ℂ d) : Tempered ℂ d :=
  wordDerivative (ExpandedFA.Distributions.multiIndexWord α) T

end ExpandedFA.Sobolev.LocalOperations

namespace Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.Sobolev.FourierScale
open _root_.ExpandedFA.Sobolev.LocalOperations
open _root_.ExpandedFA.Distributions

/-- The original LF distribution is the restriction of an actual H^{-N}
element. Compactness of its support is the only additional assumption. -/
def compactSupportType : Prop := ∀ (d : ℕ)
    (T : ScalarDistribution ℂ (⊤ : Opens (Domain d))),
  IsCompact (distributionSupport T) →
  ∃ (N : ℕ) (u : Hs d (-(N : ℝ))),
    ∀ φ : Tests ℂ (⊤ : Opens (Domain d)),
      realization u (Examples.testSchwartz ℂ φ) = T φ

/-- Every compactly supported smooth coefficient is a bounded multiplier on
every H^s, with its actual action on distributions and a uniform norm estimate.
A smooth function with compact support is a Schwartz function; no decay
condition is imposed separately on the coefficient. -/
def multiplicationType : Prop := ∀ (d : ℕ) (s : ℝ)
    (a : Euclidean d → ℂ), ContDiff ℝ ∞ a → HasCompactSupport a →
  ∃ (A : Hs d s →L[ℂ] Hs d s) (C : ℝ), 0 ≤ C ∧
    ∀ u : Hs d s,
      realization (A u) = TemperedDistribution.smulLeftCLM ℂ a (realization u) ∧
      ‖A u‖ ≤ C * ‖u‖

/-- All multi-indices, at every real starting order. The normalization of the
weight makes the derivative map contractive. -/
def derivativesType : Prop := ∀ (d : ℕ) (s : ℝ) (α : Fin d → ℕ),
  ∃ A : Hs d s →L[ℂ] Hs d (s - (∑ i, α i : ℕ)),
    ∀ u : Hs d s,
      realization (A u) = multiDerivative α (realization u) ∧ ‖A u‖ ≤ ‖u‖

/-- A C^k representative of the actual distribution, with a bound uniform in
u and x for every derivative of order at most k. Continuity of these derivatives
is included by ContDiff. The integral is the bilinear distribution pairing. -/
def embeddingType : Prop := ∀ (d k : ℕ) (s : ℝ), (k : ℝ) + (d : ℝ) / 2 < s →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Hs d s,
    ∃ f : Euclidean d → ℂ, ContDiff ℝ k f ∧
      (∀ φ : Schwartz ℂ d, Integrable (fun x => φ x * f x) ∧
        realization u φ = ∫ x, φ x * f x) ∧
      ∀ (j : ℕ), j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C * ‖u‖

end Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations

namespace ExpandedFA.Sobolev.LocalOperations
open ExpandedFA.Fourier ExpandedFA.Sobolev.FourierScale

/-- Ordinary real distributional differentiation, the negative transpose of
coordinate differentiation on real Schwartz tests. -/
def realTemperedPartial {d : ℕ} (i : Fin d) (T : Tempered ℝ d) : Tempered ℝ d :=
  -T.comp (LineDeriv.lineDerivOpCLM ℝ (Schwartz ℝ d) (basisVector i))

def realWordDerivative {d : ℕ} : List (Fin d) → Tempered ℝ d → Tempered ℝ d
  | [], T => T
  | i :: w, T => realWordDerivative w (realTemperedPartial i T)

def realMultiDerivative {d : ℕ} (α : Fin d → ℕ) (T : Tempered ℝ d) : Tempered ℝ d :=
  realWordDerivative (ExpandedFA.Distributions.multiIndexWord α) T

/-- Multiplication of a real distribution by a real coefficient is defined by
its ordinary transpose action on real tests. -/
def realTemperedMultiply {d : ℕ} (a : Euclidean d → ℝ) (T : Tempered ℝ d) :
    Tempered ℝ d :=
  T.comp (SchwartzMap.smulLeftCLM ℝ a)

end ExpandedFA.Sobolev.LocalOperations

namespace Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations
open _root_.ExpandedFA.Fourier _root_.ExpandedFA.Sobolev.FourierScale
open _root_.ExpandedFA.Sobolev.LocalOperations
open _root_.ExpandedFA.Distributions

/-- The original real LF distribution is represented in the genuine real
Sobolev subspace, with compactness of its actual support as the only assumption. -/
def realCompactSupportType : Prop := ∀ (d : ℕ)
    (T : ScalarDistribution ℝ (⊤ : Opens (Domain d))),
  IsCompact (distributionSupport T) →
  ∃ (N : ℕ) (u : RealHs d (-(N : ℝ))),
    ∀ φ : Tests ℝ (⊤ : Opens (Domain d)),
      realRealization u (Examples.testSchwartz ℝ φ) = T φ

/-- Real smooth coefficients act boundedly on the real form of every H^s. -/
def realMultiplicationType : Prop := ∀ (d : ℕ) (s : ℝ)
    (a : Euclidean d → ℝ), ContDiff ℝ ∞ a → HasCompactSupport a →
  ∃ (A : RealHs d s →L[ℝ] RealHs d s) (C : ℝ), 0 ≤ C ∧
    ∀ u : RealHs d s,
      realRealization (A u) = realTemperedMultiply a (realRealization u) ∧
      ‖A u‖ ≤ C * ‖u‖

/-- Real distributional derivatives restrict the complex Fourier operations to
the Hermitian subspace and retain the same contractive bound. -/
def realDerivativesType : Prop := ∀ (d : ℕ) (s : ℝ) (α : Fin d → ℕ),
  ∃ A : RealHs d s →L[ℝ] RealHs d (s - (∑ i, α i : ℕ)),
    ∀ u : RealHs d s,
      realRealization (A u) = realMultiDerivative α (realRealization u) ∧ ‖A u‖ ≤ ‖u‖

/-- The real distribution has a real-valued C^k representative, with bounds
uniform over the element, point, and all derivatives through order k. -/
def realEmbeddingType : Prop := ∀ (d k : ℕ) (s : ℝ), (k : ℝ) + (d : ℝ) / 2 < s →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : RealHs d s,
    ∃ f : Euclidean d → ℝ, ContDiff ℝ k f ∧
      (∀ φ : Schwartz ℝ d, Integrable (fun x => φ x * f x) ∧
        realRealization u φ = ∫ x, φ x * f x) ∧
      ∀ (j : ℕ), j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ C * ‖u‖

end Specs.ExpandedFA.Sobolev.HilbertScaleLocalOperations
