import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.ExactRectangle
import Mathlib.Analysis.SpecialFunctions.Exp

/-! Independent specification of paper.tex, Proposition d13:02:integrating-factor.
All regularity and nonvanishing conditions refer to the actual open rectangle.
The coefficients h and k are not assumed continuous: that follows from the
C¹ coefficients and the nonvanishing denominator on a fixed slice. -/
noncomputable section
open Set

namespace D13Unified.IntegratingFactors
open Specs.D13Unified.Ch02.ExactRectangle

/-- The prescribed oriented exponential primitive. -/
def exponentialPrimitive (h : ℝ → ℝ) (s t : ℝ) : ℝ :=
  Real.exp (∫ r in s..t, h r)

/-- A factor for the implicit equation on exactly the recorded rectangle. -/
def IsIntegratingFactor (I J : OpenTimeInterval) (P Q μ : ℝ × ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 1 μ (I.carrier ×ˢ J.carrier) ∧
  (∀ p ∈ I.carrier ×ˢ J.carrier, μ p ≠ 0) ∧
  ∀ p ∈ I.carrier ×ˢ J.carrier,
    statePartial (fun q => μ q * P q) p = timePartial (fun q => μ q * Q q) p
end D13Unified.IntegratingFactors

namespace Specs.D13Unified.Ch02.IntegratingFactors
open _root_.D13Unified _root_.D13Unified.IntegratingFactors
open Specs.D13Unified.Ch02.ExactRectangle

/-- Pointwise cancellation retains the nonzero-set restriction even in local
applications, independently of the shape of the graph domain. -/
def equationIffExpected : Prop :=
  ∀ (P Q μ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) (v : ℝ), μ p ≠ 0 →
    (μ p * P p + (μ p * Q p) * v = 0 ↔ P p + Q p * v = 0)

/-- The weighted coefficients are C¹ and admit the prescribed potential with
both correct partials. Its constant graphs are exactly the original solutions.
The interval version includes ordinary classical graphs and the one-sided
endpoint convention on every nondegenerate interval. -/
def exactEquationExpected : Prop :=
  ∀ (I J : OpenTimeInterval) (P Q μ : ℝ × ℝ → ℝ),
    ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier) →
    ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier) →
    IsIntegratingFactor I J P Q μ →
    ContDiffOn ℝ 1 (fun p => μ p * P p) (I.carrier ×ˢ J.carrier) ∧
    ContDiffOn ℝ 1 (fun p => μ p * Q p) (I.carrier ×ˢ J.carrier) ∧
    ∀ s ∈ I.carrier, ∀ ξ ∈ J.carrier,
      (∀ t ∈ I.carrier, ∀ x ∈ J.carrier,
        HasDerivAt (fun r => potentialValue (fun p => μ p * P p)
          (fun p => μ p * Q p) s ξ (r, x)) (μ (t, x) * P (t, x)) t ∧
        HasDerivAt (fun v => potentialValue (fun p => μ p * P p)
          (fun p => μ p * Q p) s ξ (t, v)) (μ (t, x) * Q (t, x)) x) ∧
      ∀ (K : TimeInterval) (x : ℝ → ℝ), K.carrier.Nontrivial →
        ContDiffOn ℝ 1 x K.carrier →
        (∀ t ∈ K.carrier, (t, x t) ∈ I.carrier ×ˢ J.carrier) →
        (((∀ t ∈ K.carrier, μ (t, x t) * P (t, x t) +
            (μ (t, x t) * Q (t, x t)) * derivWithin x K.carrier t = 0) ↔
          ∀ t ∈ K.carrier, P (t, x t) + Q (t, x t) * derivWithin x K.carrier t = 0) ∧
         ((∀ t ∈ K.carrier, P (t, x t) + Q (t, x t) * derivWithin x K.carrier t = 0) ↔
          ∃ c : ℝ, ∀ t ∈ K.carrier, potentialValue (fun p => μ p * P p)
            (fun p => μ p * Q p) s ξ (t, x t) = c))

/-- The source's classical open-interval statement, with ordinary derivatives. -/
def classicalGraphExpected : Prop :=
  ∀ (I J : OpenTimeInterval) (P Q μ : ℝ × ℝ → ℝ),
    ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier) →
    ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier) →
    IsIntegratingFactor I J P Q μ →
    ∀ s ∈ I.carrier, ∀ ξ ∈ J.carrier,
    ∀ (K : OpenTimeInterval) (x : ℝ → ℝ), ContDiffOn ℝ 1 x K.carrier →
      (∀ t ∈ K.carrier, (t, x t) ∈ I.carrier ×ˢ J.carrier) →
      (((∀ t ∈ K.carrier, μ (t, x t) * P (t, x t) +
          (μ (t, x t) * Q (t, x t)) * deriv x t = 0) ↔
        ∀ t ∈ K.carrier, P (t, x t) + Q (t, x t) * deriv x t = 0) ∧
       ((∀ t ∈ K.carrier, P (t, x t) + Q (t, x t) * deriv x t = 0) ↔
        ∃ c : ℝ, ∀ t ∈ K.carrier, potentialValue (fun p => μ p * P p)
          (fun p => μ p * Q p) s ξ (t, x t) = c))

/-- No additional continuity hypothesis on h: it is the stated ratio, on the
whole actual rectangle, whose nonvanishing denominator is retained. -/
def timeFactorExpected : Prop :=
  ∀ (I J : OpenTimeInterval) (P Q : ℝ × ℝ → ℝ) (h : ℝ → ℝ),
    ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier) →
    ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier) →
    (∀ p ∈ I.carrier ×ˢ J.carrier, Q p ≠ 0) →
    (∀ p ∈ I.carrier ×ˢ J.carrier,
      (statePartial P p - timePartial Q p) / Q p = h p.1) →
    ∀ s ∈ I.carrier,
      IsIntegratingFactor I J P Q (fun p => exponentialPrimitive h s p.1)

/-- The symmetric state-only formula, with its own required nonzero set. -/
def stateFactorExpected : Prop :=
  ∀ (I J : OpenTimeInterval) (P Q : ℝ × ℝ → ℝ) (k : ℝ → ℝ),
    ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier) →
    ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier) →
    (∀ p ∈ I.carrier ×ˢ J.carrier, P p ≠ 0) →
    (∀ p ∈ I.carrier ×ˢ J.carrier,
      (timePartial Q p - statePartial P p) / P p = k p.2) →
    ∀ ξ ∈ J.carrier,
      IsIntegratingFactor I J P Q (fun p => exponentialPrimitive k ξ p.2)

end Specs.D13Unified.Ch02.IntegratingFactors
