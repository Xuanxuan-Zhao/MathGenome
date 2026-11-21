import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch15.RsDarboux
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.TaggedEquivalence

/-! K03.15.rs_ordinary (paper.tex:3718–3728). The integrator is exactly
`id`. Ordinary values below are the proper Darboux values of Chapter 8,
with a minus sign when the endpoints are reversed. No measure integral or
extra regularity of the bounded integrand occurs in these statements. -/
namespace Specs.SingleVariableAnalysis.Ch15.RsOrdinary
open _root_.SingleVariableAnalysis.Riemann

/-- The weighted sums are the actual ordinary closed-cell Darboux sums. -/
def darbouxSums : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}
  (P : PartitionData a b) (hf : Ch08.DarbouxSums.boundedOnIntervalValue f a b),
  RsDarboux.lowerSumValue f id P hf = Ch08.DarbouxSums.lowerSumValue f P hf ∧
  RsDarboux.upperSumValue f id P hf = Ch08.DarbouxSums.upperSumValue f P hf

def realValue : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
  Ch08.DarbouxSums.boundedOnIntervalValue f a b → ∀ I : ℝ,
  RsSums.integralValue a b f id I ↔
    ∃ h : Ch08.Integral.realIntegrableValue f a b,
      Ch08.Integral.realIntegralValue f h = I

/-- Componentwise refinement convergence, including integrator boundedness. -/
def complexComponentwise : Prop := ∀ (a b : ℝ) (f : ℝ → ℂ)
  (α : ℝ → ℝ) (I : ℂ),
  RsSums.integralValue a b f α I ↔
    RsSums.integralValue a b (fun x => (f x).re) α I.re ∧
    RsSums.integralValue a b (fun x => (f x).im) α I.im

def complexValue : Prop := ∀ (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
  RsSums.boundedOnValue a b f → ∀ I : ℂ,
  RsSums.integralValue a b f id I ↔
    ∃ h : Ch08.Integral.complexIntegrableValue f a b,
      Ch08.Integral.complexIntegralValue f h = I

/-- All endpoint orders and equality of oriented real values. -/
def realOrientedValue : Prop := ∀ (f : ℝ → ℝ) (a b : ℝ),
  RsSums.boundedOnValue (min a b) (max a b) f → ∀ I : ℝ,
  RsSums.integralValue a b f id I ↔
    ∃ h : Ch08.Integral.realIntegrableValue f (min a b) (max a b),
      (if a ≤ b then Ch08.Integral.realIntegralValue f h
       else -Ch08.Integral.realIntegralValue f h) = I

def realIntegrability : Prop := ∀ (f : ℝ → ℝ) (a b : ℝ),
  RsSums.boundedOnValue (min a b) (max a b) f →
  ((∃ I, RsSums.integralValue a b f id I) ↔
    Ch08.Integral.realIntegrableValue f (min a b) (max a b))

/-- All endpoint orders and equality of oriented complex values. -/
def complexOrientedValue : Prop := ∀ (f : ℝ → ℂ) (a b : ℝ),
  RsSums.boundedOnValue (min a b) (max a b) f → ∀ I : ℂ,
  RsSums.integralValue a b f id I ↔
    ∃ h : Ch08.Integral.complexIntegrableValue f (min a b) (max a b),
      (if a ≤ b then Ch08.Integral.complexIntegralValue f h
       else -Ch08.Integral.complexIntegralValue f h) = I

def complexIntegrability : Prop := ∀ (f : ℝ → ℂ) (a b : ℝ),
  RsSums.boundedOnValue (min a b) (max a b) f →
  ((∃ I, RsSums.integralValue a b f id I) ↔
    Ch08.Integral.complexIntegrableValue f (min a b) (max a b))

/-- The ordinary mesh interpretation uses the same finite tagged sums. -/
def realMesh : Prop := ∀ (f : ℝ → ℝ) {a b : ℝ}, a ≤ b →
  Ch08.DarbouxSums.boundedOnIntervalValue f a b → ∀ I : ℝ,
  RsSums.integralValue a b f id I ↔ FineTaggedLimit f a b I

def complexMesh : Prop := ∀ (f : ℝ → ℂ) {a b : ℝ}, a ≤ b →
  RsSums.boundedOnValue a b f → ∀ I : ℂ,
  RsSums.integralValue a b f id I ↔ FineTaggedLimit f a b I
end Specs.SingleVariableAnalysis.Ch15.RsOrdinary
