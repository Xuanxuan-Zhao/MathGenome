import MathGenome.Internal.FourierSobolev.Specs.P102.U3.LittlewoodPaleyUpper

/-! Independent statement of the complete Basic Littlewood--Paley inequality,
paper.tex:1248--1271. All projections, exponents, measures, and square functions
are exactly those in the upper-bound interface. The square-function norm is an
extended norm; it cannot hide divergence through `ENNReal.toReal`.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal FourierTransform SchwartzMap

namespace P102.U3.LittlewoodPaley
open P102.Specs.U3 (Euclidean)
open P102.U3.Mihlin
open P102.U2.CZLpData (Exponent)

/-- The physical-space pairing at one integer scale, with arbitrary finite
interior exponents for the two canonical multiplier extensions. -/
def pairingTerm {d : ℕ} (p q : Exponent) (χ : Euclidean d → ℝ)
    (f g : SchwartzMap (Euclidean d) ℂ) (j : ℤ) : ℂ :=
  ∫ x, projection p (annulus χ) j (f.toLp p.val volume) x *
    star (projection q (enlargedCutoff χ) j (g.toLp q.val volume) x)

end P102.U3.LittlewoodPaley

namespace P102.Specs.U3.LittlewoodPaley
open P102.U3.Mihlin P102.U3.LittlewoodPaley
open P102.U2.CZLpData (Exponent)

/-- Absolute summability and the reconstruction identity for Schwartz inputs.
The exponents need not be conjugate for this identity; on Schwartz inputs all
extensions agree with the same L² multiplier. -/
def reconstructionType : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ χ : Euclidean d → ℝ, IsCutoff χ → IsPartition χ →
    ∀ (p q : Exponent) (f g : SchwartzMap (Euclidean d) ℂ),
      Summable (fun j : ℤ => ‖pairingTerm p q χ f g j‖) ∧
      HasSum (pairingTerm p q χ f g) (∫ x, f x * star (g x))

/-- The full two-sided estimate, uniformly in the Lᵖ input, for every cutoff
partition allowed by the original upper-bound interface and every 1<p<∞. -/
def theoremType : Prop :=
  ∀ (d : ℕ), 1 ≤ d → ∀ χ : Euclidean d → ℝ, IsCutoff χ → IsPartition χ →
    ∀ p : Exponent, ∃ c C : ℝ≥0, 0 < c ∧ c ≤ C ∧
      UpperBound p (annulus χ) C ∧
      ∀ f : Lp (α := Euclidean d) ℂ p.val volume,
        (c : ℝ≥0∞) * ‖f‖ₑ ≤ eLpNorm (infiniteSquare p (annulus χ) f) p.val volume

end P102.Specs.U3.LittlewoodPaley
