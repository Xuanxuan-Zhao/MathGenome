import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Independent interface for the hypersurface step in the Euclidean Sard proof,
paper.tex, Theorem 4.1, paragraph beginning “Near a point of B_j”. -/

open scoped ContDiff

namespace SmoothManifolds.Ch04.SardVanishingLayer

/-- Vanishing of the actual ambient derivatives of orders one through `j`. -/
def vanishingJets {m n : ℕ} (U : Set (Fin m → ℝ))
    (f : (Fin m → ℝ) → (Fin n → ℝ)) (j : ℕ) : Set (Fin m → ℝ) :=
  {x | x ∈ U ∧ ∀ i : ℕ, 1 ≤ i → i ≤ j → iteratedFDeriv ℝ i f x = 0}

/-- The induction hypothesis, with every target dimension and no measurability
assumptions. This is used only in source dimension `m - 1`. -/
def sardIn (d : ℕ) : Prop :=
  ∀ (q : ℕ) (V : Set (Fin d → ℝ))
    (g : (Fin d → ℝ) → (Fin q → ℝ)),
    IsOpen V → ContDiffOn ℝ ∞ g V →
      MeasureTheory.volume
        (g '' {x | x ∈ V ∧ ¬ Function.Surjective (fderiv ℝ g x)}) = 0

namespace Specs

/-- The complete layer step, with arbitrary open domain, including the empty set. -/
def vanishingLayer : Prop :=
  ∀ (m n j : ℕ), 0 < m → 0 < n → 1 ≤ j →
    ∀ (U : Set (Fin m → ℝ)) (f : (Fin m → ℝ) → (Fin n → ℝ)),
    IsOpen U → ContDiffOn ℝ ∞ f U → sardIn (m - 1) →
      MeasureTheory.volume
        (f '' (vanishingJets U f j \ vanishingJets U f (j + 1))) = 0

end Specs
end SmoothManifolds.Ch04.SardVanishingLayer
