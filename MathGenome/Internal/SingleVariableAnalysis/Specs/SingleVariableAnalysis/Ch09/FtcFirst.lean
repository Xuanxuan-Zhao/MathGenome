import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch08.Integral
import Mathlib.Topology.ContinuousOn
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.Derivative

/-! K03.09.ftc_first, paper.tex:2379–2396.
The integrals are the proper Darboux integrals, not measure integrals.
An ambient function F represents the accumulation precisely on [a,b];
its values outside that interval are arbitrary. Integrability witnesses
in the representation add no assumptions: all initial restrictions exist.
Continuity is relative to [a,b], including at its endpoints. The endpoint
conclusions test real increments only from the available side, and require
a < b. The interior conclusions use the ordinary real-variable derivative,
also for complex-valued functions.
-/
namespace Specs.SingleVariableAnalysis.Ch09.FtcFirst
open Specs.SingleVariableAnalysis.Ch08
open Specs.SingleVariableAnalysis.Ch04.Derivative

/-- The given F is an ambient representation of x ↦ ∫_a^x f. -/
def realAccumulationOn (f F : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b, ∃ hx : Integral.realIntegrableValue f a x,
    F x = Integral.realIntegralValue f hx

def complexAccumulationOn (f F : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∀ x ∈ Set.Icc a b, ∃ hx : Integral.complexIntegrableValue f a x,
    F x = Integral.complexIntegralValue f hx

/-- No extra existence hypothesis is hidden in the accumulation model. -/
def realAccumulationExists : Prop :=
  ∀ (f : ℝ → ℝ) {a b : ℝ}, Integral.realIntegrableValue f a b →
    ∃ F : ℝ → ℝ, realAccumulationOn f F a b

def complexAccumulationExists : Prop :=
  ∀ (f : ℝ → ℂ) {a b : ℝ}, Integral.complexIntegrableValue f a b →
    ∃ F : ℝ → ℂ, complexAccumulationOn f F a b

def realWithin : Prop :=
  ∀ (f F : ℝ → ℝ) {a b : ℝ}, Integral.realIntegrableValue f a b →
    realAccumulationOn f F a b → ∀ x ∈ Set.Icc a b,
    ContinuousWithinAt f (Set.Icc a b) x →
    hasRealIncrementDerivativeWithinValue F (f x) (Set.Icc a b) x

def complexWithin : Prop :=
  ∀ (f F : ℝ → ℂ) {a b : ℝ}, Integral.complexIntegrableValue f a b →
    complexAccumulationOn f F a b → ∀ x ∈ Set.Icc a b,
    ContinuousWithinAt f (Set.Icc a b) x →
    hasRealIncrementDerivativeWithinValue F (f x) (Set.Icc a b) x

def realInterior : Prop :=
  ∀ (f F : ℝ → ℝ) {a b : ℝ}, Integral.realIntegrableValue f a b →
    realAccumulationOn f F a b → ∀ x ∈ Set.Ioo a b,
    ContinuousWithinAt f (Set.Icc a b) x → HasDerivAt F (f x) x

def complexInterior : Prop :=
  ∀ (f F : ℝ → ℂ) {a b : ℝ}, Integral.complexIntegrableValue f a b →
    complexAccumulationOn f F a b → ∀ x ∈ Set.Ioo a b,
    ContinuousWithinAt f (Set.Icc a b) x → HasDerivAt F (f x) x

def realLeftEndpoint : Prop :=
  ∀ (f F : ℝ → ℝ) {a b : ℝ}, a < b → Integral.realIntegrableValue f a b →
    realAccumulationOn f F a b → ContinuousWithinAt f (Set.Icc a b) a →
    hasRealIncrementDerivativeWithinValue F (f a) (Set.Ici a) a

def realRightEndpoint : Prop :=
  ∀ (f F : ℝ → ℝ) {a b : ℝ}, a < b → Integral.realIntegrableValue f a b →
    realAccumulationOn f F a b → ContinuousWithinAt f (Set.Icc a b) b →
    hasRealIncrementDerivativeWithinValue F (f b) (Set.Iic b) b

def complexLeftEndpoint : Prop :=
  ∀ (f F : ℝ → ℂ) {a b : ℝ}, a < b → Integral.complexIntegrableValue f a b →
    complexAccumulationOn f F a b → ContinuousWithinAt f (Set.Icc a b) a →
    hasRealIncrementDerivativeWithinValue F (f a) (Set.Ici a) a

def complexRightEndpoint : Prop :=
  ∀ (f F : ℝ → ℂ) {a b : ℝ}, a < b → Integral.complexIntegrableValue f a b →
    complexAccumulationOn f F a b → ContinuousWithinAt f (Set.Icc a b) b →
    hasRealIncrementDerivativeWithinValue F (f b) (Set.Iic b) b

end Specs.SingleVariableAnalysis.Ch09.FtcFirst
