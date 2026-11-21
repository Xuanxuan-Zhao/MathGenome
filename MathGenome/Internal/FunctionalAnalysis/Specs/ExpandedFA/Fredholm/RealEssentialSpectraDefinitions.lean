import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fredholm.Definitions
import Mathlib.Algebra.Algebra.Spectrum.Basic

/-!
Independent real spectral definitions for paper.tex:10690–10728 and the
left/right essential sets used at 10751. Spectra are native spectra over ℝ
in the actual algebra of real bounded endomorphisms. The compact ideal is
the canonical ideal of all compact operators, with compactness in the original
space. No complexification, completeness, nonzero-space or dimension hypothesis
is imposed on these definitions or elementary identities.
-/

namespace ExpandedFA.Fredholm.RealEssentialSpectraDefinitionsSpec

universe u

/-- A set of real scalars for each bounded real Hilbert-space endomorphism. -/
def RealOperatorSpectrumType :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H],
    (H →L[ℝ] H) → Set ℝ

def realEssentialSpectrumValue : RealOperatorSpectrumType.{u} :=
  fun {H} _ _ T =>
    {z | ¬ DefinitionsSpec.IsFredholmValue (T - z • (1 : H →L[ℝ] H))}

/-- Intersection over every compact real-linear perturbation. -/
def realWeylSpectrumValue : RealOperatorSpectrumType.{u} :=
  fun {H} _ _ T =>
    ⋂ K : ↥(DefinitionsSpec.compactIdealValue ℝ H), spectrum ℝ (T + K.val)

def realLeftEssentialSpectrumValue : RealOperatorSpectrumType.{u} :=
  fun {H} _ _ T =>
    {z | ¬ DefinitionsSpec.IsLeftSemiFredholmValue (T - z • (1 : H →L[ℝ] H))}

def realRightEssentialSpectrumValue : RealOperatorSpectrumType.{u} :=
  fun {H} _ _ T =>
    {z | ¬ DefinitionsSpec.IsRightSemiFredholmValue (T - z • (1 : H →L[ℝ] H))}

def RealEssentialMembership : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (z : ℝ),
    z ∈ realEssentialSpectrumValue T ↔
      ¬ DefinitionsSpec.IsFredholmValue (T - z • (1 : H →L[ℝ] H))

/-- The intersection uses exactly the original compact-unit-ball predicate. -/
def RealWeylMembership : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (z : ℝ),
    z ∈ realWeylSpectrumValue T ↔
      ∀ K : H →L[ℝ] H,
        Compactness.DefinitionsSpec.IsCompactLinearMapValue K.toLinearMap →
        z ∈ spectrum ℝ (T + K)

def RealLeftEssentialMembership : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (z : ℝ),
    z ∈ realLeftEssentialSpectrumValue T ↔
      ¬ DefinitionsSpec.IsLeftSemiFredholmValue (T - z • (1 : H →L[ℝ] H))

def RealRightEssentialMembership : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) (z : ℝ),
    z ∈ realRightEssentialSpectrumValue T ↔
      ¬ DefinitionsSpec.IsRightSemiFredholmValue (T - z • (1 : H →L[ℝ] H))

def RealEssentialUnion : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H),
    realEssentialSpectrumValue T =
      realLeftEssentialSpectrumValue T ∪ realRightEssentialSpectrumValue T

end ExpandedFA.Fredholm.RealEssentialSpectraDefinitionsSpec
