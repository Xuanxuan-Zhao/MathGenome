import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch01.SupInf
import MathGenome.Internal.SingleVariableAnalysis.Specs.SingleVariableAnalysis.Ch02.OneSided
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Order.Interval.Set.OrdConnected

/-! Independent obligations for K03.03.monotone_limits, paper.tex:566–580.
An interval is an order-convex real set, including all open/closed/unbounded
variants. Functions are ambient functions tested only on that set. The finite
limits use the accepted epsilon–delta definitions, which include accumulation.
The extended limits use the order topology on the canonical extended real line;
they apply at excluded as well as included endpoints. The tail clauses also
cover infinite endpoints. Countability concerns relative continuity on I, so
included endpoints are counted. No global monotonicity is imposed. -/

namespace Specs.SingleVariableAnalysis.Ch03.MonotoneLimits

open Set Filter
open scoped Topology
open Specs.SingleVariableAnalysis.Ch02.OneSided

def increasingInterior : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → MonotoneOn f I →
    ∀ x ∈ interior I,
      IsLUB (f '' (I ∩ Iio x)) (sSup (f '' (I ∩ Iio x))) ∧
      IsGLB (f '' (I ∩ Ioi x)) (sInf (f '' (I ∩ Ioi x))) ∧
      leftRelativeLimitValue f I x (sSup (f '' (I ∩ Iio x))) ∧
      rightRelativeLimitValue f I x (sInf (f '' (I ∩ Ioi x))) ∧
      sSup (f '' (I ∩ Iio x)) ≤ f x ∧ f x ≤ sInf (f '' (I ∩ Ioi x))

def decreasingInterior : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → AntitoneOn f I →
    ∀ x ∈ interior I,
      IsGLB (f '' (I ∩ Iio x)) (sInf (f '' (I ∩ Iio x))) ∧
      IsLUB (f '' (I ∩ Ioi x)) (sSup (f '' (I ∩ Ioi x))) ∧
      leftRelativeLimitValue f I x (sInf (f '' (I ∩ Iio x))) ∧
      rightRelativeLimitValue f I x (sSup (f '' (I ∩ Ioi x))) ∧
      sInf (f '' (I ∩ Iio x)) ≥ f x ∧ f x ≥ sSup (f '' (I ∩ Ioi x))

def increasingExtended : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → MonotoneOn f I →
    (∀ a, leftAccumulationValue I a →
      Tendsto (fun t => (f t : EReal)) (𝓝[I ∩ Iio a] a)
        (𝓝 (sSup ((fun t => (f t : EReal)) '' (I ∩ Iio a))))) ∧
    (∀ a, rightAccumulationValue I a →
      Tendsto (fun t => (f t : EReal)) (𝓝[I ∩ Ioi a] a)
        (𝓝 (sInf ((fun t => (f t : EReal)) '' (I ∩ Ioi a))))) ∧
    (domainUnboundedAboveValue I →
      Tendsto (fun t => (f t : EReal)) (atTop ⊓ 𝓟 I)
        (𝓝 (sSup ((fun t => (f t : EReal)) '' I)))) ∧
    (domainUnboundedBelowValue I →
      Tendsto (fun t => (f t : EReal)) (atBot ⊓ 𝓟 I)
        (𝓝 (sInf ((fun t => (f t : EReal)) '' I))))

def decreasingExtended : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → AntitoneOn f I →
    (∀ a, leftAccumulationValue I a →
      Tendsto (fun t => (f t : EReal)) (𝓝[I ∩ Iio a] a)
        (𝓝 (sInf ((fun t => (f t : EReal)) '' (I ∩ Iio a))))) ∧
    (∀ a, rightAccumulationValue I a →
      Tendsto (fun t => (f t : EReal)) (𝓝[I ∩ Ioi a] a)
        (𝓝 (sSup ((fun t => (f t : EReal)) '' (I ∩ Ioi a))))) ∧
    (domainUnboundedAboveValue I →
      Tendsto (fun t => (f t : EReal)) (atTop ⊓ 𝓟 I)
        (𝓝 (sInf ((fun t => (f t : EReal)) '' I)))) ∧
    (domainUnboundedBelowValue I →
      Tendsto (fun t => (f t : EReal)) (atBot ⊓ 𝓟 I)
        (𝓝 (sSup ((fun t => (f t : EReal)) '' I))))

/-- Since the finite limits and bracketing inequalities are asserted above,
this strict inequality says exactly that every interior discontinuity is a jump. -/
def increasingJump : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → MonotoneOn f I →
    ∀ x ∈ interior I,
      (¬ ContinuousWithinAt f I x ↔
        sSup (f '' (I ∩ Iio x)) < sInf (f '' (I ∩ Ioi x)))

def decreasingJump : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → AntitoneOn f I →
    ∀ x ∈ interior I,
      (¬ ContinuousWithinAt f I x ↔
        sSup (f '' (I ∩ Ioi x)) < sInf (f '' (I ∩ Iio x)))

def increasingCountable : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → MonotoneOn f I →
    Set.Countable {x ∈ I | ¬ ContinuousWithinAt f I x}

def decreasingCountable : Prop :=
  ∀ (f : ℝ → ℝ) (I : Set ℝ), I.OrdConnected → AntitoneOn f I →
    Set.Countable {x ∈ I | ¬ ContinuousWithinAt f I x}

/-- The included endpoints are contained in a set of at most two points,
including the empty and singleton interval cases. -/
def includedEndpoints : Prop :=
  ∀ I : Set ℝ, I.OrdConnected → ∃ a b : ℝ, I \ interior I ⊆ {a, b}

end Specs.SingleVariableAnalysis.Ch03.MonotoneLimits
