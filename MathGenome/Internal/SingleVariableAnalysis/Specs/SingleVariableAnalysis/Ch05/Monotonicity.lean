import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch05.Lagrange

/-!
K03.05.monotonicity, paper.tex:844–852. `OrdConnected I` expresses that
I is an arbitrary real interval, including unbounded, open, half-open, empty
and degenerate intervals. Ambient extensions are tested only on I; derivatives
are ordinary real derivatives only at interior points. No endpoint derivative
or continuity of the derivative is required.
-/
namespace Specs.SingleVariableAnalysis.Ch05.Monotonicity

open Set

def nonnegativeDerivativeMonotone : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), OrdConnected I → ContinuousOn f I →
    (∀ x ∈ interior I, DifferentiableAt ℝ f x) →
    (∀ x ∈ interior I, 0 ≤ deriv f x) → MonotoneOn f I

def positiveDerivativeStrictMono : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), OrdConnected I → ContinuousOn f I →
    (∀ x ∈ interior I, DifferentiableAt ℝ f x) →
    (∀ x ∈ interior I, 0 < deriv f x) → StrictMonoOn f I

def nonpositiveDerivativeAntitone : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), OrdConnected I → ContinuousOn f I →
    (∀ x ∈ interior I, DifferentiableAt ℝ f x) →
    (∀ x ∈ interior I, deriv f x ≤ 0) → AntitoneOn f I

def negativeDerivativeStrictAnti : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), OrdConnected I → ContinuousOn f I →
    (∀ x ∈ interior I, DifferentiableAt ℝ f x) →
    (∀ x ∈ interior I, deriv f x < 0) → StrictAntiOn f I

def monotoneDerivativeNonnegative : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ),
    MonotoneOn f I → a ∈ interior I → HasDerivAt f L a → 0 ≤ L

/-- The four criteria in the manuscript's domain-relative increment language. -/
def realIncrementMonotonicity : Prop :=
  ∀ (f d : ℝ → ℝ) (I : Set ℝ), OrdConnected I →
    Ch03.Continuity.relativeContinuousValue f I →
    (∀ x ∈ interior I,
      Ch04.Derivative.hasRealIncrementDerivativeWithinValue f (d x) I x) →
    ((∀ x ∈ interior I, 0 ≤ d x) → MonotoneOn f I) ∧
    ((∀ x ∈ interior I, 0 < d x) → StrictMonoOn f I) ∧
    ((∀ x ∈ interior I, d x ≤ 0) → AntitoneOn f I) ∧
    ((∀ x ∈ interior I, d x < 0) → StrictAntiOn f I)

def realIncrementNecessity : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ) (a L : ℝ), MonotoneOn f I → a ∈ interior I →
    Ch04.Derivative.hasRealIncrementDerivativeWithinValue f L I a → 0 ≤ L

def cubeCounterexample : Prop :=
  StrictMono (fun x : ℝ => x ^ 3) ∧
    (∀ x : ℝ, HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x) ∧
    HasDerivAt (fun x : ℝ => x ^ 3) 0 0

/-- The displayed formula extends the source function arbitrarily outside [0,1]. -/
def endpointCounterexample : Prop :=
  (∀ x ∈ Ioo (0 : ℝ) 1,
    HasDerivAt (fun t : ℝ => if t = 0 then 2 else t) 1 x) ∧
  ¬ MonotoneOn (fun t : ℝ => if t = 0 then 2 else t) (Icc 0 1)

end Specs.SingleVariableAnalysis.Ch05.Monotonicity
