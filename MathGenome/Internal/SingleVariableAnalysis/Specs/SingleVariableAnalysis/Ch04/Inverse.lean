import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch03.InverseContinuity
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch04.OneSided

/-! Independent specification for K03.04.inverse, paper.tex:706–720.
The canonical `invFunOn` represents the inverse on the exact interval image;
no condition is imposed on its irrelevant values outside the image.
All derivative values are real, hence finite. Included endpoints are expressed
by side availability and a bound on the entire interval on that side. -/
namespace Specs.SingleVariableAnalysis.Ch04.Inverse
open scoped Topology
open Ch03.Continuity Ch03.IntervalImages Ch04.Derivative Ch04.OneSided

def intervalInverseProperties : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), realIntervalValue I → relativeContinuousValue f I →
    (StrictMonoOn f I ∨ StrictAntiOn f I) →
    Set.MapsTo (Function.invFunOn f I) (f '' I) I ∧
    (∀ x ∈ I, Function.invFunOn f I (f x) = x) ∧
    (∀ y ∈ f '' I, f (Function.invFunOn f I y) = y) ∧
    relativeContinuousValue (Function.invFunOn f I) (f '' I)

def inverseDerivative : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ),
    realIntervalValue I → relativeContinuousValue f I →
    (StrictMonoOn f I ∨ StrictAntiOn f I) → a ∈ interior I →
    hasRealIncrementDerivativeWithinValue f L I a → L ≠ 0 →
    f a ∈ interior (f '' I) ∧
    hasRealIncrementDerivativeValue (Function.invFunOn f I) (1 / L) (f a)

def inverseRightDerivativeOfStrictMono : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ),
    realIntervalValue I → relativeContinuousValue f I → StrictMonoOn f I →
    I ⊆ Set.Ici a →
    hasRightRealIncrementDerivativeWithinValue f L I a → L ≠ 0 →
    f '' I ⊆ Set.Ici (f a) ∧
    hasRightRealIncrementDerivativeWithinValue
      (Function.invFunOn f I) (1 / L) (f '' I) (f a)

def inverseRightDerivativeOfStrictAnti : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ),
    realIntervalValue I → relativeContinuousValue f I → StrictAntiOn f I →
    I ⊆ Set.Ici a →
    hasRightRealIncrementDerivativeWithinValue f L I a → L ≠ 0 →
    f '' I ⊆ Set.Iic (f a) ∧
    hasLeftRealIncrementDerivativeWithinValue
      (Function.invFunOn f I) (1 / L) (f '' I) (f a)

def inverseLeftDerivativeOfStrictMono : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ),
    realIntervalValue I → relativeContinuousValue f I → StrictMonoOn f I →
    I ⊆ Set.Iic a →
    hasLeftRealIncrementDerivativeWithinValue f L I a → L ≠ 0 →
    f '' I ⊆ Set.Iic (f a) ∧
    hasLeftRealIncrementDerivativeWithinValue
      (Function.invFunOn f I) (1 / L) (f '' I) (f a)

def inverseLeftDerivativeOfStrictAnti : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ),
    realIntervalValue I → relativeContinuousValue f I → StrictAntiOn f I →
    I ⊆ Set.Iic a →
    hasLeftRealIncrementDerivativeWithinValue f L I a → L ≠ 0 →
    f '' I ⊆ Set.Ici (f a) ∧
    hasRightRealIncrementDerivativeWithinValue
      (Function.invFunOn f I) (1 / L) (f '' I) (f a)

end Specs.SingleVariableAnalysis.Ch04.Inverse
