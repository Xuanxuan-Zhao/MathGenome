import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.SolutionConcepts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Independent specification of paper.tex, Proposition d13:02:exact.
Ambient representatives are used only on the actual open rectangle. -/
noncomputable section
open Set
open scoped Interval

namespace Specs.D13Unified.Ch02.ExactRectangle
open _root_.D13Unified

/-- The two coordinate partials, obtained from the real Fréchet derivative. -/
def timePartial (P : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ P p (1, 0)
def statePartial (P : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := fderiv ℝ P p (0, 1)

/-- The specified oriented, two-segment integral, on precisely the rectangle. -/
def potentialValue (P Q : ℝ × ℝ → ℝ) (s ξ : ℝ) (p : ℝ × ℝ) : ℝ :=
  (∫ r in s..p.1, P (r, ξ)) + ∫ v in ξ..p.2, Q (p.1, v)

def potentialType := (ℝ × ℝ → ℝ) → (ℝ × ℝ → ℝ) → ℝ → ℝ → ℝ × ℝ → ℝ

/-- Both asserted partial derivatives of the actual integral formula. -/
def potentialPartialsExpected : Prop :=
  ∀ (I J : OpenTimeInterval) (P Q : ℝ × ℝ → ℝ),
    ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier) →
    ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier) →
    (∀ p ∈ I.carrier ×ˢ J.carrier, statePartial P p = timePartial Q p) →
    ∀ s ∈ I.carrier, ∀ ξ ∈ J.carrier, ∀ t ∈ I.carrier, ∀ x ∈ J.carrier,
      HasDerivAt (fun r => potentialValue P Q s ξ (r, x)) (P (t, x)) t ∧
      HasDerivAt (fun v => potentialValue P Q s ξ (t, v)) (Q (t, x)) x

/-- Classical graphs have the nonempty open interval convention of Chapter 1.
There is no requirement that their time interval be the whole of I. -/
def graphIffExpected : Prop :=
  ∀ (I J : OpenTimeInterval) (P Q : ℝ × ℝ → ℝ),
    ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier) →
    ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier) →
    (∀ p ∈ I.carrier ×ˢ J.carrier, statePartial P p = timePartial Q p) →
    ∀ s ∈ I.carrier, ∀ ξ ∈ J.carrier,
    ∀ (K : OpenTimeInterval) (x : ℝ → ℝ), ContDiffOn ℝ 1 x K.carrier →
      (∀ t ∈ K.carrier, (t, x t) ∈ I.carrier ×ˢ J.carrier) →
      ((∀ t ∈ K.carrier, P (t, x t) + Q (t, x t) * deriv x t = 0) ↔
        ∃ c : ℝ, ∀ t ∈ K.carrier, potentialValue P Q s ξ (t, x t) = c)

/-- Division is equivalent precisely at points where Q is nonzero. -/
def normalFormExpected : Prop :=
  ∀ (P Q v : ℝ), Q ≠ 0 → (P + Q * v = 0 ↔ v = -P / Q)

/-- The normal-form equation along any classical graph in the nonzero set. -/
def graphNormalFormExpected : Prop :=
  ∀ (I J : OpenTimeInterval) (P Q : ℝ × ℝ → ℝ),
    ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier) →
    ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier) →
    (∀ p ∈ I.carrier ×ˢ J.carrier, statePartial P p = timePartial Q p) →
    ∀ s ∈ I.carrier, ∀ ξ ∈ J.carrier,
    ∀ (K : OpenTimeInterval) (x : ℝ → ℝ), ContDiffOn ℝ 1 x K.carrier →
      (∀ t ∈ K.carrier, (t, x t) ∈ I.carrier ×ˢ J.carrier) →
      (∀ t ∈ K.carrier, Q (t, x t) ≠ 0) →
      ((∀ t ∈ K.carrier, deriv x t = -P (t, x t) / Q (t, x t)) ↔
        ∃ c : ℝ, ∀ t ∈ K.carrier, potentialValue P Q s ξ (t, x t) = c)

/-- Endpoint-aware version on every nondegenerate interval, including compact,
half-open and unbounded intervals. At included endpoints the curve derivative
is the corresponding one-sided derivative. -/
def graphOnIntervalIffExpected : Prop :=
  ∀ (I J : OpenTimeInterval) (P Q : ℝ × ℝ → ℝ),
    ContDiffOn ℝ 1 P (I.carrier ×ˢ J.carrier) →
    ContDiffOn ℝ 1 Q (I.carrier ×ˢ J.carrier) →
    (∀ p ∈ I.carrier ×ˢ J.carrier, statePartial P p = timePartial Q p) →
    ∀ s ∈ I.carrier, ∀ ξ ∈ J.carrier,
    ∀ (K : TimeInterval) (x : ℝ → ℝ), K.carrier.Nontrivial →
      ContDiffOn ℝ 1 x K.carrier →
      (∀ t ∈ K.carrier, (t, x t) ∈ I.carrier ×ˢ J.carrier) →
      ((∀ t ∈ K.carrier,
        P (t, x t) + Q (t, x t) * derivWithin x K.carrier t = 0) ↔
        ∃ c : ℝ, ∀ t ∈ K.carrier, potentialValue P Q s ξ (t, x t) = c)

end Specs.D13Unified.Ch02.ExactRectangle
