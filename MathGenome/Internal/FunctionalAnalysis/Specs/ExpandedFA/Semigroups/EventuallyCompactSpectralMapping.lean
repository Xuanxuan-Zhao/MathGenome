import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.PointSpectralMapping
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Semigroups.SpectralInclusion
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.RieszSchauder
import Mathlib.Analysis.Normed.Operator.Banach

/-! Independent statements for the spectral part of
`fa2:p3:semigroup-spectral-mapping`, paper.tex:14557–14625.
Growth/spectral bound equality and the exponential-polynomial asymptotics
are assigned to `EventuallyCompactAsymptotics` separately.
No compact-resolvent hypothesis or conclusion is used here. -/
noncomputable section
open scoped NNReal

namespace ExpandedFA.Semigroups.EventuallyCompactSpectralMappingSpec

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- Some strictly positive time operator has compact unit-ball image closure
in the original Banach space. The zero Banach space is included. -/
def EventuallyCompact [CompleteSpace X] (T : C0Semigroup ℂ X) : Prop :=
  ∃ t₀ : ℝ≥0, 0 < t₀ ∧
    Compactness.DefinitionsSpec.IsCompactLinearMapValue (T.operators t₀).toLinearMap

/-- The exact-domain shift ζI−A, on the original operator domain. -/
def generatorShift (A : Unbounded.Operator ℂ X X) (ζ : ℂ) : A.domain →ₗ[ℂ] X :=
  ζ • A.domain.subtype - A.toFun

/-- Power kernels for an unbounded operator, respecting the domain at every
iteration. At stage zero the kernel is {0}. -/
def generatorRootSpace (A : Unbounded.Operator ℂ X X) (ζ : ℂ) : ℕ → Submodule ℂ X
  | 0 => ⊥
  | n + 1 => ((generatorRootSpace A ζ n).comap (generatorShift A ζ)).map A.domain.subtype

/-- All generalized eigenvectors, with no fixed bound on chain length. -/
def generatorGeneralizedEigenspace (A : Unbounded.Operator ℂ X X) (ζ : ℂ) :
    Submodule ℂ X := ⨆ n : ℕ, generatorRootSpace A ζ n

/-- Auxiliary bounded-operator assertion: having a compact positive power
makes every nonzero spectral value an actual eigenvalue. -/
def PowerCompactSpectrumEigenvalue : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (B : X →L[ℂ] X) (n : ℕ), 0 < n →
    Compactness.DefinitionsSpec.IsCompactLinearMapValue (B ^ n).toLinearMap →
    ∀ μ : ℂ, μ ≠ 0 →
      (μ ∈ _root_.spectrum ℂ B ↔ ∃ x : X, x ≠ 0 ∧ B x = μ • x)

/-- Full spectral mapping at every positive time, not just at a time where
the semigroup operator is itself compact. -/
def FullSpectralMapping : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : C0Semigroup ℂ X), EventuallyCompact T →
    ∀ t : ℝ≥0, 0 < t →
      _root_.spectrum ℂ (T.operators t) \ {0} =
        (fun ζ : ℂ => Complex.exp ((t : ℂ) * ζ)) ''
          C0SemigroupSpec.spectrumValue (C0SemigroupSpec.generatorValue T)

/-- A genuine finite spectral summand, not just a bound on the dimension of
chains of eigenvectors. Both subspace semigroups agree with the original
operators at every time, their sum is a topological direct sum, the finite
part lies in the original exact generator domain, and the complementary
generator has a bounded two-sided resolvent at ζ. In particular an isolated
spectral point cannot hide an infinite-dimensional quasinilpotent part. -/
def LocalFiniteSpectralDecomposition [CompleteSpace X] (T : C0Semigroup ℂ X)
    (ζ : ℂ) : Prop :=
  ∃ (V W : Submodule ℂ X) (cV : CompleteSpace V) (cW : CompleteSpace W),
    letI : CompleteSpace V := cV
    letI : CompleteSpace W := cW
    ∃ (S : C0Semigroup ℂ V) (U : C0Semigroup ℂ W),
      Submodule.IsTopCompl V W ∧ FiniteDimensional ℂ V ∧
      (∀ t (x : V), (S.operators t x : X) = T.operators t x) ∧
      (∀ t (x : W), (U.operators t x : X) = T.operators t x) ∧
      (∀ x : V, (x : X) ∈ (C0SemigroupSpec.generatorValue T).domain) ∧
      Nonempty (Unbounded.ResolventInverse (C0SemigroupSpec.generatorValue U) ζ)

/-- Every logarithmic fiber can be separated by a finite compact Riesz
space and a complement whose generator is resolvent at that fiber. -/
def FiniteRieszDecompositions : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : C0Semigroup ℂ X), EventuallyCompact T →
    ∀ ζ : ℂ, LocalFiniteSpectralDecomposition T ζ

/-- The complete generator spectral conclusion: actual eigenvectors,
isolation in the full spectrum, finite algebraic (not only geometric)
multiplicity, and finitely many spectral values in each closed right
half-plane. Empty spectrum is allowed throughout. -/
def GeneratorSpectralStructure : Prop :=
  ∀ {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    (T : C0Semigroup ℂ X), EventuallyCompact T →
    let A := C0SemigroupSpec.generatorValue T
    (∀ ζ ∈ C0SemigroupSpec.spectrumValue A,
      ζ ∈ PointSpectralMappingSpec.generatorPointSpectrum A ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ η ∈ C0SemigroupSpec.spectrumValue A,
        dist η ζ < ε → η = ζ) ∧
      FiniteDimensional ℂ (generatorGeneralizedEigenspace A ζ) ∧
      LocalFiniteSpectralDecomposition T ζ) ∧
    ∀ a : ℝ, {ζ : ℂ | ζ ∈ C0SemigroupSpec.spectrumValue A ∧ a ≤ ζ.re}.Finite

end ExpandedFA.Semigroups.EventuallyCompactSpectralMappingSpec
