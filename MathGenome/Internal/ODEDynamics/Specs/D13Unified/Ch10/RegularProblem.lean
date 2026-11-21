import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! The independent Chapter 10 interface. Functions on a closed interval are
represented by functions on ℝ, with no conditions away from the interval.
Derivatives are within the interval, hence are one-sided at the endpoints.
The canonical coefficient data and all expected values live in this file;
none of the representative or Hilbert bridge propositions is assumed here. -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal ComplexConjugate

namespace Specs.D13Unified.Ch10.RegularProblem

/-- Exactly the regular, real coefficient hypotheses of Chapter 10. -/
structure Problem where
  a : ℝ
  b : ℝ
  a_lt_b : a < b
  p : ℝ → ℝ
  q : ℝ → ℝ
  w : ℝ → ℝ
  p_regular : ContDiffOn ℝ 1 p (Icc a b)
  q_continuous : ContinuousOn q (Icc a b)
  w_continuous : ContinuousOn w (Icc a b)
  p_positive : ∀ x ∈ Icc a b, 0 < p x
  w_positive : ∀ x ∈ Icc a b, 0 < w x

/-- Each endpoint pair is real and nonzero as a pair. -/
structure BoundaryCoefficients where
  alphaA : ℝ
  betaA : ℝ
  alphaB : ℝ
  betaB : ℝ
  left_nonzero : alphaA ≠ 0 ∨ betaA ≠ 0
  right_nonzero : alphaB ≠ 0 ∨ betaB ≠ 0

abbrev problemValue := Problem
abbrev boundaryCoefficientsValue := BoundaryCoefficients
def typeType : Type 1 := Type

def intervalValue (P : Problem) : Set ℝ := Icc P.a P.b
def baseMeasureValue (P : Problem) : Measure ℝ := volume.restrict (intervalValue P)
def weightedMeasureValue (P : Problem) : Measure ℝ :=
  (baseMeasureValue P).withDensity (fun x => ENNReal.ofReal (P.w x))
abbrev hilbertValue (P : Problem) : Type := Lp ℂ 2 (weightedMeasureValue P)
def derivativeValue (P : Problem) (y : ℝ → ℂ) : ℝ → ℂ :=
  derivWithin y (intervalValue P)
def expressionValue (P : Problem) (y : ℝ → ℂ) (x : ℝ) : ℂ :=
  -derivWithin (fun t => (P.p t : ℂ) * derivativeValue P y t) (intervalValue P) x +
    (P.q x : ℂ) * y x

def satisfiesBoundaryValue (P : Problem) (B : BoundaryCoefficients) (y : ℝ → ℂ) : Prop :=
  (B.alphaA : ℂ) * y P.a + (B.betaA : ℂ) * (P.p P.a : ℂ) * derivativeValue P y P.a = 0 ∧
  (B.alphaB : ℂ) * y P.b + (B.betaB : ℂ) * (P.p P.b : ℂ) * derivativeValue P y P.b = 0

def dirichletValue : BoundaryCoefficients :=
  ⟨1, 0, 1, 0, Or.inl one_ne_zero, Or.inl one_ne_zero⟩

def classicalEigenfunctionValue (P : Problem) (B : BoundaryCoefficients)
    (lam : ℂ) (y : ℝ → ℂ) : Prop :=
  ContDiffOn ℝ 2 y (intervalValue P) ∧
  (∃ x ∈ intervalValue P, y x ≠ 0) ∧
  satisfiesBoundaryValue P B y ∧
  ∀ x ∈ intervalValue P, expressionValue P y x = lam * (P.w x : ℂ) * y x

def toHilbertValue (P : Problem) (f : ℝ → ℂ)
    (hf : MemLp f 2 (weightedMeasureValue P)) : hilbertValue P := hf.toLp f

/-- Linear in the first variable, as in the paper. Mathlib is linear in the second. -/
def paperInnerValue (P : Problem) (u v : hilbertValue P) : ℂ := inner ℂ v u

def intervalType := Problem → Set ℝ
def baseMeasureType := Problem → Measure ℝ
def weightedMeasureType := Problem → Measure ℝ
def hilbertType := Problem → Type
def derivativeType := Problem → (ℝ → ℂ) → ℝ → ℂ
def expressionType := Problem → (ℝ → ℂ) → ℝ → ℂ
def satisfiesBoundaryType := Problem → BoundaryCoefficients → (ℝ → ℂ) → Prop
def dirichletType := BoundaryCoefficients
def classicalEigenfunctionType := Problem → BoundaryCoefficients → ℂ → (ℝ → ℂ) → Prop
def toHilbertType := (P : Problem) → (f : ℝ → ℂ) →
  MemLp f 2 (weightedMeasureValue P) → hilbertValue P
def paperInnerType := (P : Problem) → hilbertValue P → hilbertValue P → ℂ

def completeSpaceType : Prop := ∀ P : Problem, CompleteSpace (hilbertValue P)
def innerProductSpaceType : Prop := ∀ P : Problem, Nonempty (InnerProductSpace ℂ (hilbertValue P))
def finiteMeasureType : Prop := ∀ P : Problem, IsFiniteMeasure (weightedMeasureValue P)
def weightedAEType : Prop := ∀ (P : Problem) (R : ℝ → Prop),
  (∀ᵐ x ∂weightedMeasureValue P, R x) ↔ ∀ᵐ x ∂baseMeasureValue P, R x

def representativeType : Prop := ∀ (P : Problem) (f : ℝ → ℂ)
  (hf : MemLp f 2 (weightedMeasureValue P)),
  (toHilbertValue P f hf : ℝ → ℂ) =ᵐ[weightedMeasureValue P] f

def quotientEqualityType : Prop := ∀ (P : Problem) (f g : ℝ → ℂ)
  (hf : MemLp f 2 (weightedMeasureValue P)) (hg : MemLp g 2 (weightedMeasureValue P)),
  toHilbertValue P f hf = toHilbertValue P g hg ↔ f =ᵐ[baseMeasureValue P] g

def hilbertEqualityType : Prop := ∀ (P : Problem) (u v : hilbertValue P),
  u = v ↔ (u : ℝ → ℂ) =ᵐ[baseMeasureValue P] v

def allRepresentedType : Prop := ∀ (P : Problem) (u : hilbertValue P),
  ∃ (f : ℝ → ℂ) (hf : MemLp f 2 (weightedMeasureValue P)), toHilbertValue P f hf = u

def integralDensityType : Prop := ∀ (P : Problem) (f : ℝ → ℂ),
  (∫ x, f x ∂weightedMeasureValue P) = ∫ x in intervalValue P, f x * (P.w x : ℂ)

def innerIntegralType : Prop := ∀ (P : Problem) (u v : hilbertValue P),
  paperInnerValue P u v = ∫ x in intervalValue P, u x * conj (v x) * (P.w x : ℂ)

def innerIntegrableType : Prop := ∀ (P : Problem) (u v : hilbertValue P),
  Integrable (fun x => u x * conj (v x) * (P.w x : ℂ)) (baseMeasureValue P)

def innerIntervalIntegralType : Prop := ∀ (P : Problem) (u v : hilbertValue P),
  paperInnerValue P u v = ∫ x in P.a..P.b, u x * conj (v x) * (P.w x : ℂ)

def innerRepresentativesType : Prop := ∀ (P : Problem) (f g : ℝ → ℂ)
  (hf : MemLp f 2 (weightedMeasureValue P)) (hg : MemLp g 2 (weightedMeasureValue P)),
  paperInnerValue P (toHilbertValue P f hf) (toHilbertValue P g hg) =
    ∫ x in intervalValue P, f x * conj (g x) * (P.w x : ℂ)

def innerLinearFirstType : Prop := ∀ (P : Problem) (c : ℂ) (u v : hilbertValue P),
  paperInnerValue P (c • u) v = c * paperInnerValue P u v

def innerConjugateSecondType : Prop := ∀ (P : Problem) (c : ℂ) (u v : hilbertValue P),
  paperInnerValue P u (c • v) = conj c * paperInnerValue P u v

def innerNormType : Prop := ∀ (P : Problem) (u : hilbertValue P),
  paperInnerValue P u u = (‖u‖ ^ 2 : ℝ)

def continuousMemLpType : Prop := ∀ (P : Problem) (f : ℝ → ℂ),
  ContinuousOn f (intervalValue P) → MemLp f 2 (weightedMeasureValue P)

def continuousEqualityType : Prop := ∀ (P : Problem) (f g : ℝ → ℂ)
  (_hf : ContinuousOn f (intervalValue P)) (_hg : ContinuousOn g (intervalValue P))
  (hf2 : MemLp f 2 (weightedMeasureValue P)) (hg2 : MemLp g 2 (weightedMeasureValue P)),
  toHilbertValue P f hf2 = toHilbertValue P g hg2 ↔ EqOn f g (intervalValue P)

def continuousNonzeroType : Prop := ∀ (P : Problem) (f : ℝ → ℂ)
  (_hf : ContinuousOn f (intervalValue P)) (hf2 : MemLp f 2 (weightedMeasureValue P)),
  toHilbertValue P f hf2 ≠ 0 ↔ ∃ x ∈ intervalValue P, f x ≠ 0

def dirichletBoundaryType : Prop := ∀ (P : Problem) (y : ℝ → ℂ),
  satisfiesBoundaryValue P dirichletValue y ↔ y P.a = 0 ∧ y P.b = 0

def eigenfunctionHilbertType : Prop := ∀ (P : Problem) (B : BoundaryCoefficients)
  (lam : ℂ) (y : ℝ → ℂ), classicalEigenfunctionValue P B lam y →
  ∃ hy : MemLp y 2 (weightedMeasureValue P), toHilbertValue P y hy ≠ 0

end Specs.D13Unified.Ch10.RegularProblem
