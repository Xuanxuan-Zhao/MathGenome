import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.OpenPos

open MeasureTheory Set Filter
open scoped ContDiff

/-! Independent statements for paper.tex, Lemma `variation-fundamental`, first assertion.
The ambient functions encode functions on the open interval; neither local integrability,
tests nor conclusions constrain their values outside that interval. Smooth tests with compact
support contained in the interval encode precisely its compactly supported smooth tests.
The vector pairing is the usual real Euclidean inner product. -/

namespace Specs.VariationalNotes.Classical

def fundamentalLemmaAE : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (h : ℝ → ℝ),
    LocallyIntegrableOn h (Ioo a b) →
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ t in Ioo a b, h t * φ t = 0) →
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), h t = 0

def fundamentalLemmaContinuous : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (h : ℝ → ℝ),
    LocallyIntegrableOn h (Ioo a b) →
    (∀ φ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ t in Ioo a b, h t * φ t = 0) →
    ContinuousOn h (Ioo a b) → ∀ t ∈ Ioo a b, h t = 0

def fundamentalLemmaVectorAE : Prop :=
  ∀ (m : ℕ) (a b : ℝ), a < b → ∀ (h : ℝ → EuclideanSpace ℝ (Fin m)),
    LocallyIntegrableOn h (Ioo a b) →
    (∀ φ : ℝ → EuclideanSpace ℝ (Fin m), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ t in Ioo a b, inner ℝ (h t) (φ t) = 0) →
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), h t = 0

def fundamentalLemmaVectorContinuous : Prop :=
  ∀ (m : ℕ) (a b : ℝ), a < b → ∀ (h : ℝ → EuclideanSpace ℝ (Fin m)),
    LocallyIntegrableOn h (Ioo a b) →
    (∀ φ : ℝ → EuclideanSpace ℝ (Fin m), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ Ioo a b → ∫ t in Ioo a b, inner ℝ (h t) (φ t) = 0) →
    ContinuousOn h (Ioo a b) → ∀ t ∈ Ioo a b, h t = 0

end Specs.VariationalNotes.Classical
