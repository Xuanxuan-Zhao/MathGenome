import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.GreenKernel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-! Independent statements for the weighted L² inverse in paper.tex,
d13:10:green. All regularity is on the actual closed interval. Values of
ambient functions away from that interval are immaterial. -/
noncomputable section
open MeasureTheory Set

namespace Specs.D13Unified.Ch10.GreenWeakInverse
open _root_.D13Unified.Ch10.GreenKernel
open RegularProblem hiding Problem

/-- The actual integral representative, using the chosen measurable
representative of an L² class. Independence of that choice is a theorem. -/
def representativeValue (P : Problem) (c : ℝ) (f : hilbertValue P) : ℝ → ℂ :=
  applyKernel P c (f : ℝ → ℂ)

/-- The associated L² class. The fallback makes the construction independent
of a proof of regularity; the inverse theorem proves square integrability. -/
def operatorValue (P : Problem) (c : ℝ) (f : hilbertValue P) : hilbertValue P := by
  classical
  exact if h : MemLp (representativeValue P c f) 2 (weightedMeasureValue P) then
    toHilbertValue P (representativeValue P c f) h
  else 0

/-- C¹ regularity uses derivatives within [a,b], including the one-sided
endpoint derivatives. The flux is an actual absolutely continuous function.
The last clause says that its derivative exists and equals Qu−wf almost
everywhere for Lebesgue measure on [a,b]. -/
def weakSolutionValue (P : Problem) (c : ℝ) (f y : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ 1 y (interval P) ∧
  AbsolutelyContinuousOnInterval
    (fun x => (P.p x : ℂ) * derivativeValue P y x) P.a P.b ∧
  y P.a = 0 ∧ y P.b = 0 ∧
  ∀ᵐ x ∂baseMeasureValue P,
    HasDerivAt (fun t => (P.p t : ℂ) * derivativeValue P y t)
      ((Q P c x : ℂ) * y x - (P.w x : ℂ) * f x) x

def representativeType := (P : Problem) → ℝ → hilbertValue P → (ℝ → ℂ)
def operatorType := (P : Problem) → ℝ → hilbertValue P → hilbertValue P
def weakSolutionType := Problem → ℝ → (ℝ → ℂ) → (ℝ → ℂ) → Prop

def WeightedL1 : Prop := ∀ (P : Problem) (f : ℝ → ℂ),
  MemLp f 2 (weightedMeasureValue P) →
  Integrable f (baseMeasureValue P) ∧
  Integrable (fun x => f x * (P.w x : ℂ)) (baseMeasureValue P)

def KernelIntegrable : Prop := ∀ (P : Problem) (c : ℝ) (f : ℝ → ℂ),
  MemLp f 2 (weightedMeasureValue P) → ∀ x ∈ interval P,
  IntervalIntegrable (fun t => (kernel P c x t : ℂ) * f t * (P.w t : ℂ))
    volume P.a P.b

/-- Even values of the output away from [a,b] are independent of the
representative: congruence of Bochner integrals is an AE statement. -/
def RepresentativeIndependent : Prop := ∀ (P : Problem) (c : ℝ) (f g : ℝ → ℂ)
  (hf : MemLp f 2 (weightedMeasureValue P)) (hg : MemLp g 2 (weightedMeasureValue P)),
  toHilbertValue P f hf = toHilbertValue P g hg →
  applyKernel P c f = applyKernel P c g

/-- Existence for arbitrary L² forcing representatives, and uniqueness among
actual functions on [a,b] with exactly the asserted weak regularity. -/
def InverseWeak : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  ∀ (f : ℝ → ℂ), MemLp f 2 (weightedMeasureValue P) →
    weakSolutionValue P c f (applyKernel P c f) ∧
    ∀ y : ℝ → ℂ, weakSolutionValue P c f y →
      EqOn y (applyKernel P c f) (interval P)

/-- The AE flux-derivative formulation gives precisely the shifted
Sturm–Liouville differential expression, with derivatives within [a,b]. -/
def WeakEquation : Prop := ∀ (P : Problem) (c : ℝ) (f y : ℝ → ℂ),
  weakSolutionValue P c f y → ∀ᵐ x ∂baseMeasureValue P,
    -derivativeValue P (fun t => (P.p t : ℂ) * derivativeValue P y t) x +
      (Q P c x : ℂ) * y x = (P.w x : ℂ) * f x

/-- The integral really represents Kf in H; no everywhere differentiable
structure is attributed to an arbitrary representative of an AE class. -/
def ClassRepresentative : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) → ∀ f : hilbertValue P,
  MemLp (representativeValue P c f) 2 (weightedMeasureValue P) ∧
  (operatorValue P c f : ℝ → ℂ) =ᵐ[baseMeasureValue P] representativeValue P c f

/-- Conversely a weak regular Dirichlet solution equals the actual integral
representative on the whole closed interval and equals its L² class in H. -/
def Converse : Prop := ∀ (P : Problem) (c : ℝ),
  0 < c → (∀ x ∈ interval P, 1 ≤ Q P c x) →
  ∀ (f : hilbertValue P) (y : ℝ → ℂ), weakSolutionValue P c f y →
  EqOn y (representativeValue P c f) (interval P) ∧
  ∃ hy : MemLp y 2 (weightedMeasureValue P), toHilbertValue P y hy = operatorValue P c f

end Specs.D13Unified.Ch10.GreenWeakInverse
