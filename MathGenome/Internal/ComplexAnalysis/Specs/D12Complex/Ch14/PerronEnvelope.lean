import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch14.SubharmonicMaximum
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Perron's envelope, paper.tex:2625–2633. A total representative of the
boundary datum is used; only its restriction to `frontier Ω` is relevant.
No boundary extension of a class member or continuity of the supremum is assumed. -/
noncomputable section
open Set Metric

namespace D12Complex

/-- Continuous subharmonic minorants with the prescribed boundary upper limits. -/
def perronClass (Ω : Set ℂ) (φ : ℂ → ℝ) : Set (ℂ → ℝ) :=
  {u | SubharmonicOn Ω u ∧ ∀ ξ ∈ frontier Ω, ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Ω, dist z ξ < δ → u z ≤ φ ξ + ε}

/-- The actual pointwise supremum of all values in the Perron class. -/
def perronEnvelope (Ω : Set ℂ) (φ : ℂ → ℝ) (z : ℂ) : ℝ :=
  sSup ((fun u : ℂ → ℝ => u z) '' perronClass Ω φ)

end D12Complex

namespace Specs.D12Complex.Ch14.PerronEnvelope
open _root_.D12Complex

def perronClass_type := Set ℂ → (ℂ → ℝ) → Set (ℂ → ℝ)
def perronClass_value : perronClass_type := fun Ω φ =>
  {u | SubharmonicOn Ω u ∧ ∀ ξ ∈ frontier Ω, ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ Ω, dist z ξ < δ → u z ≤ φ ξ + ε}

def perronEnvelope_type := Set ℂ → (ℂ → ℝ) → ℂ → ℝ
def perronEnvelope_value : perronEnvelope_type := fun Ω φ z =>
  sSup ((fun u : ℂ → ℝ => u z) '' perronClass Ω φ)

/-- Nonemptiness and boundedness ensure that the real supremum is finite
and genuine. The extrema are taken over the compact, nonempty boundary. -/
def perron_envelope_type : Prop :=
  ∀ (Ω : Set ℂ) (φ : ℂ → ℝ), IsDomain Ω → Bornology.IsBounded Ω →
    ContinuousOn φ (frontier Ω) →
    (perronClass Ω φ).Nonempty ∧
    (∀ z ∈ Ω, (((fun u : ℂ → ℝ => u z) '' perronClass Ω φ).Nonempty ∧
      BddAbove ((fun u : ℂ → ℝ => u z) '' perronClass Ω φ))) ∧
    (∀ z ∈ Ω, sInf (φ '' frontier Ω) ≤ perronEnvelope Ω φ z ∧
      perronEnvelope Ω φ z ≤ sSup (φ '' frontier Ω)) ∧
    HarmonicOn Ω (perronEnvelope Ω φ)

end Specs.D12Complex.Ch14.PerronEnvelope
