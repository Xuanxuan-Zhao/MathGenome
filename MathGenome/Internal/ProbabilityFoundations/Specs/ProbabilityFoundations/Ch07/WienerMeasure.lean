import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch05.ContinuousProcessLaw
import Mathlib.Probability.BrownianMotion.GaussianProjectiveFamily
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic

/-! Theorem `thm:wiener`, paper.tex §7.6. The path space has its canonical
uniform metric and Borel sigma-algebra. Finite lists may be empty, unordered,
or contain repeated times. The marginal below is the image of the centered
Gaussian with covariance `min(s,t)` on the finite set of distinct times. -/
open MeasureTheory ProbabilityTheory
open ProbabilityFoundations.Ch05
open scoped NNReal

namespace ProbabilityFoundations.Ch07

/-- A time in the compact interval, regarded as a nonnegative real. -/
def nonnegativeTime {T : ℝ} (t : Time T) : ℝ≥0 := ⟨t.1, t.2.1⟩

/-- The centered Gaussian law of an arbitrary finite time list. Its distinct-time
covariance matrix is `BrownianReal.covMatrix`, defined entrywise as `min(s,t)`.
Projection permits repeated times and preserves singular covariances. -/
noncomputable def wienerMarginal {T : ℝ} {n : ℕ} (τ : Fin n → Time T) :
    Measure (Fin n → ℝ) := by
  classical
  let I := Finset.univ.image (fun i => nonnegativeTime (τ i))
  exact (BrownianReal.projectiveFamily I).map
    (fun x i => x ⟨nonnegativeTime (τ i), Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)

/-- All assertions concern the actual coordinate maps on `C([0,T],ℝ)`.
The integral of the product is included explicitly, as in the source. -/
structure IsWienerMeasure (T : ℝ) (W : Measure C(Time T, ℝ)) : Prop where
  probability : IsProbabilityMeasure W
  marginals : ∀ (n : ℕ) (τ : Fin n → Time T),
    W.map (fun f i => f (τ i)) = wienerMarginal τ
  gaussian : ∀ (n : ℕ) (τ : Fin n → Time T),
    HasGaussianLaw (fun f i => f (τ i)) W
  starts_zero : ∀ t : Time T, (t : ℝ) = 0 → ∀ᵐ f ∂W, f t = 0
  centered : ∀ t : Time T, Integrable (fun f => f t) W ∧ (∫ f, f t ∂W) = 0
  covariance : ∀ s t : Time T,
    Integrable (fun f => f s * f t) W ∧
      (∫ f, f s * f t ∂W) = min (s : ℝ) (t : ℝ)
  independent_increments : HasIndepIncrements (fun t (f : C(Time T, ℝ)) => f t) W
  normal_increments : ∀ s t : Time T, s ≤ t →
    HasLaw (fun f => f t - f s)
      (gaussianReal 0 (Real.toNNReal ((t : ℝ) - (s : ℝ)))) W

end ProbabilityFoundations.Ch07

namespace Specs.ProbabilityFoundations.Ch07.WienerMeasure

def wienerMeasureType : Prop :=
  ∀ T : ℝ, 0 < T → ∃! W : Measure C(Time T, ℝ),
    _root_.ProbabilityFoundations.Ch07.IsWienerMeasure T W

end Specs.ProbabilityFoundations.Ch07.WienerMeasure
