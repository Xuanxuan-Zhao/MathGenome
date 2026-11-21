import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Set MeasureTheory
open scoped ContDiff

namespace SardFlatJet

/-- Points of the open domain where ambient derivatives of orders `1,…,k` vanish. -/
def vanishingJets {m n : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (k : ℕ) : Set (Fin m → ℝ) :=
  {x | x ∈ U ∧ ∀ i : ℕ, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0}

end SardFlatJet

namespace SardFlatJetSpecs

/-- The terminal flat-jet stratum has null image; no measurability is required. -/
def flatJetImageNull : Prop :=
  ∀ (m n k : ℕ), 0 < n → m < (k + 1) * n →
    ∀ (U : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → (Fin n → ℝ)),
      IsOpen U → ContDiffOn ℝ ∞ f U →
      volume (f '' SardFlatJet.vanishingJets U f k) = 0

end SardFlatJetSpecs
