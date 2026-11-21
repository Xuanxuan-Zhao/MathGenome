import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.IntervalL1Constants
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.Order.ProjIcc

/-! The last clause of `fa2:p4:sharp-interval-poincare`, paper.tex:19948–19992.
Scalars are real or complex. Both exponent parameters include infinity.
The continuous maps below are actual representatives of the accepted Sobolev
derivative graph. The target norm is the ordinary Lebesgue Lq norm on (0,1).
At finite p the zero-trace conclusion includes membership in the original
closure-defined W₀ space. At infinity zero trace means both endpoint values
vanish; no norm-density assertion at infinity is introduced. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal

namespace ExpandedFA.PartIV.IntervalExtremizers
open ExpandedFA.Sobolev.OneDimensional

abbrev Segment := Icc (0 : ℝ) 1
abbrev intervalMeasure : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)

/-- Constant continuation past the two endpoints. Only its restriction to
[0,1] enters the Sobolev representative and Lq norm. -/
def extension {𝕜 : Type} [RCLike 𝕜] (f : C(Segment, 𝕜)) : ℝ → 𝕜 :=
  fun x => f (projIcc 0 1 (by norm_num) x)

/-- The genuine integral-power norm, including essential supremum at q=∞. -/
def normQ {𝕜 : Type} [RCLike 𝕜] (q : ℝ≥0∞) (f : C(Segment, 𝕜)) : ℝ :=
  (eLpNorm (extension f) q intervalMeasure).toReal

abbrev IntervalW1p (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)] :=
  W1p 𝕜 ExpandedFA.PartIV.IntervalL1.unitInterval p

def Realizes {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : IntervalW1p 𝕜 p) (f : C(Segment, 𝕜)) : Prop :=
  PrimitiveRepresentative u (extension f)

inductive Constraint where
  | meanZero
  | zeroTrace
  deriving DecidableEq

/-- Mean zero uses the Bochner integral, and zero trace uses the two actual
endpoint values of the continuous representative. -/
def Satisfies {𝕜 : Type} [RCLike 𝕜] (b : Constraint) (f : C(Segment, 𝕜)) : Prop :=
  match b with
  | .meanZero => ExpandedFA.PartIV.IntervalL1.mean (extension f) = 0
  | .zeroTrace => extension f 0 = 0 ∧ extension f 1 = 0

/-- This conclusion preserves the originally defined W₀ space for every
finite p, while leaving the p=∞ endpoint interpretation explicit above. -/
def FiniteZeroSpace {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (b : Constraint) (u : IntervalW1p 𝕜 p) : Prop :=
  b = .zeroTrace → ∀ hp : p ≠ ∞,
    u ∈ Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces.ZeroSpaceValue
      𝕜 1 (lineDomain ExpandedFA.PartIV.IntervalL1.unitInterval) 1 p hp

/-- The derivative unit ball with the constraint imposed. Compactness is
required in the uniform topology on continuous functions, not the W1p norm. -/
def derivativeBall (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (b : Constraint) : Set C(Segment, 𝕜) :=
  {f | Satisfies b f ∧ ∃ u : IntervalW1p 𝕜 p, Realizes u f ∧ ‖derivativeLp u‖ ≤ 1}

/-- A finite positive best constant, a nonzero optimizer with positive
weak derivative norm, exact equality, and the bound on the entire original
constraint class. Equality and the universal bound express bestness without
an auxiliary assumed supremum or existence certificate. -/
def Attained (𝕜 : Type) [RCLike 𝕜] (p q : ℝ≥0∞) [Fact (1 ≤ p)]
    (b : Constraint) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ (u : IntervalW1p 𝕜 p) (f : C(Segment, 𝕜)),
    Realizes u f ∧ Satisfies b f ∧ FiniteZeroSpace b u ∧
      f ≠ 0 ∧ 0 < ‖derivativeLp u‖ ∧ 0 < normQ q f ∧
      normQ q f = C * ‖derivativeLp u‖ ∧
      ∀ (v : IntervalW1p 𝕜 p) (g : C(Segment, 𝕜)),
        Realizes v g → Satisfies b g → normQ q g ≤ C * ‖derivativeLp v‖

end ExpandedFA.PartIV.IntervalExtremizers

namespace Specs.ExpandedFA.PartIV.IntervalExtremizers
open _root_.ExpandedFA.PartIV.IntervalExtremizers

/-- The complete assigned attainment assertion, including p=∞ and q=∞,
for both constraints and both scalar fields. -/
def Extremizers : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p →
    ∀ (q : ℝ≥0∞) [Fact (1 ≤ q)] (b : Constraint), Attained 𝕜 p q b

/-- The endpoint result is independently recorded for continuation/review. -/
def TopExtremizers : Prop := ∀ (𝕜 : Type) [RCLike 𝕜]
    (q : ℝ≥0∞) [Fact (1 ≤ q)] (b : Constraint), Attained 𝕜 ∞ q b

end Specs.ExpandedFA.PartIV.IntervalExtremizers
