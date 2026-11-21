import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Independent specification of the example at paper.tex:2427–2440.
The product probability space realizes a nonnegative magnitude and a fair sign.
The first moment is an extended nonnegative integral, so infinity is meaningful.
No finite first moment is assumed. -/

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace ProbabilityFoundations.Ch07.InfiniteMomentExample

/-- The specified strict tail, including the value at `exp 1`. Only
nonnegative thresholds are used to specify the magnitude law. -/
noncomputable def magnitudeTail (r : ℝ) : ℝ :=
  if r < Real.exp 1 then (Real.exp 1)⁻¹ else 1 / (r * Real.log r)

/-- CDF with its jump at zero and continuous tail beyond zero. -/
noncomputable def magnitudeCDF (r : ℝ) : ℝ :=
  if r < 0 then 0 else 1 - magnitudeTail r

/-- A fair sign taking the real values -1 and 1. -/
noncomputable def fairSignLaw : Measure ℝ :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac (-1) + (2 : ℝ≥0∞)⁻¹ • Measure.dirac 1

/-- Independent multiplication by the fair sign on the product space. -/
noncomputable def signedLaw (ν : Measure ℝ) : Measure ℝ :=
  Measure.map (fun p : ℝ × ℝ => p.1 * p.2) (fairSignLaw.prod ν)

/-- The truncated second absolute moment, using the non-strict endpoint. -/
noncomputable def truncatedSecondMoment (μ : Measure ℝ) (R : ℝ) : ℝ :=
  ∫ x in {x : ℝ | |x| ≤ R}, |x| ^ 2 ∂μ

/-- Exactly the right side of the displayed inequality in the source. -/
noncomputable def truncationBound (μ : Measure ℝ) (h : ℝ) : ℝ :=
  (h / 2) * truncatedSecondMoment μ (1 / h) +
    (2 / h) * (μ {x : ℝ | 1 / h < |x|}).toReal

end ProbabilityFoundations.Ch07.InfiniteMomentExample

namespace Specs.ProbabilityFoundations.Ch07.DifferentiableWithoutFirstMoment

open _root_.ProbabilityFoundations.Ch07.InfiniteMomentExample

/-- All parts of the magnitude construction, including support, strict tail,
the junction at e, and the atom at zero. -/
def magnitudeLawType : Prop :=
  ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Iio 0) = 0 ∧
    (∀ r : ℝ, 0 ≤ r → ν (Ioi r) = ENNReal.ofReal (magnitudeTail r)) ∧
    ν {0} = ENNReal.ofReal (1 - (Real.exp 1)⁻¹)

/-- General estimate, stated for a real part. For a symmetric law the
characteristic function is real, so this is the source's displayed estimate. -/
def truncationEstimateType : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ), 0 < |t| →
    0 ≤ (1 - (charFun μ t).re) / |t| ∧
    (1 - (charFun μ t).re) / |t| ≤ truncationBound μ |t|

/-- Full existence statement: the law is obtained from the independent fair
sign and the specified nonnegative magnitude, not merely from an unspecified
symmetric heavy-tailed distribution. -/
def exampleType : Prop :=
  ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Iio 0) = 0 ∧
    (∀ r : ℝ, 0 ≤ r → ν (Ioi r) = ENNReal.ofReal (magnitudeTail r)) ∧
    ν {0} = ENNReal.ofReal (1 - (Real.exp 1)⁻¹) ∧
    IsProbabilityMeasure fairSignLaw ∧
    fairSignLaw {-1} = (2 : ℝ≥0∞)⁻¹ ∧ fairSignLaw {1} = (2 : ℝ≥0∞)⁻¹ ∧
    ProbabilityTheory.IndepFun (Prod.fst : ℝ × ℝ → ℝ) Prod.snd (fairSignLaw.prod ν) ∧
    Measure.map Prod.fst (fairSignLaw.prod ν) = fairSignLaw ∧
    Measure.map Prod.snd (fairSignLaw.prod ν) = ν ∧
    IsProbabilityMeasure (signedLaw ν) ∧
    Measure.map (fun x : ℝ => |x|) (signedLaw ν) = ν ∧
    Measure.map (fun x : ℝ => -x) (signedLaw ν) = signedLaw ν ∧
    (∫⁻ x : ℝ, ENNReal.ofReal |x| ∂(signedLaw ν)) = ∞ ∧
    (∀ t : ℝ, (charFun (signedLaw ν) t).im = 0) ∧
    (∀ t : ℝ, 0 < |t| →
      0 ≤ (1 - (charFun (signedLaw ν) t).re) / |t| ∧
      (1 - (charFun (signedLaw ν) t).re) / |t| ≤ truncationBound (signedLaw ν) |t|) ∧
    Tendsto (truncationBound (signedLaw ν)) (𝓝[>] 0) (𝓝 0) ∧
    HasDerivAt (charFun (signedLaw ν)) 0 0

end Specs.ProbabilityFoundations.Ch07.DifferentiableWithoutFirstMoment
