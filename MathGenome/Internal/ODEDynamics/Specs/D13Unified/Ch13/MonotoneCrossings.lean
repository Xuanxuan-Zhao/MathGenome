import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.Nullclines
import Mathlib.Order.UpperLower.Basic

/-! Independent statements for the successive-intersection part of
paper.tex, d13:13:monotone-crossings (lines 2842–2884).

A meeting is with the whole closed straight segment, including its endpoints.
Succession is a condition on actual times: there is no meeting at any strictly
intermediate time. No ordering or index-barrier certificate is an input.
A lower set K of natural numbers containing 1 parametrizes either a finite
prefix of at least two meetings or an infinite sequence. Thus the main theorem
does not assume infinitely many returns, completeness, or compact confinement.
The omega-limit consequence is allocated to the separate OmegaSection goal. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D13Unified.Ch13.MonotoneCrossings
open Ch13.Nullclines Ch06.StateDerivative

/-- Two chronologically consecutive meetings of the forward maximal orbit. -/
structure Successive (F : AutonomousODE Plane) (S : StraightSegment)
    (x : Plane) (a b : ℝ) : Prop where
  nonneg : 0 ≤ a
  lt : a < b
  first_time : a ∈ (flowInterval F x).carrier
  second_time : b ∈ (flowInterval F x).carrier
  first_hit : flow F a x ∈ Specs.D13Unified.Ch13.Nullclines.segmentCarrierValue S
  second_hit : flow F b x ∈ Specs.D13Unified.Ch13.Nullclines.segmentCarrierValue S
  no_hit : ∀ t ∈ Ioo a b,
    flow F t x ∉ Specs.D13Unified.Ch13.Nullclines.segmentCarrierValue S

end D13Unified.Ch13.MonotoneCrossings

namespace Specs.D13Unified.Ch13.MonotoneCrossings
open _root_.D13Unified _root_.D13Unified.Ch13.Nullclines
open _root_.D13Unified.Ch13.MonotoneCrossings _root_.D13Unified.Ch06.StateDerivative
open Ch01.AutonomousParameters Ch13.Nullclines

/-- Signed, unnormalized normal coordinate relative to the supporting line. -/
def signedHeightValue (S : StraightSegment) (p : Plane) : ℝ :=
  S.direction.1 * (p.2 - S.center.2) - S.direction.2 * (p.1 - S.center.1)

def signedHeightType := StraightSegment → Plane → ℝ

/-- Transversality gives an actual local crossing in the fixed normal
coordinate. The quotient has the sign of the velocity's normal component.
The punctured neighborhood also lies in the recorded time domain and contains
no further meeting of the segment. -/
def LocalCrossing : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, ∀ S : TransverseSegment F,
    ∀ t ∈ (flowInterval F x).carrier,
    flow F t x ∈ segmentCarrierValue S.toStraightSegment →
    ∀ᶠ r in 𝓝[≠] t, r ∈ (flowInterval F x).carrier ∧
      0 < normalComponentValue F S.toStraightSegment (flow F t x) *
        (signedHeightValue S.toStraightSegment (flow F r x) / (r-t)) ∧
      flow F r x ∉ segmentCarrierValue S.toStraightSegment

/-- Any repeated meeting, successive or otherwise, forces a complete
nonconstant periodic orbit, with the actual time difference as a period. -/
def RepeatedIntersection : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, ∀ S : TransverseSegment F,
    ∀ a ∈ (flowInterval F x).carrier, ∀ b ∈ (flowInterval F x).carrier,
      a < b → flow F a x ∈ segmentCarrierValue S.toStraightSegment →
      flow F a x = flow F b x →
      _root_.D13Unified.Ch11.Orbits.HasLeastPeriod F x ∧
      Function.Periodic (fun t => flow F t x) (b-a)

/-- The central planar barrier. Distinct consecutive intersections fix the
order of the next one in the SAME affine coordinate, in either direction.
There is no assumption of an index barrier or a complement classification. -/
def SuccessiveOrder : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, ∀ S : TransverseSegment F, ∀ a b c : ℝ,
      Successive F S.toStraightSegment x a b →
      Successive F S.toStraightSegment x b c →
      let u := fun t => segmentCoordinateValue S.toStraightSegment (flow F t x)
      (u a < u b → u b < u c) ∧ (u b < u a → u c < u b)

/-- One fixed direction for the WHOLE chronological sequence, including
finite sequences. Equality means equality of the points and includes the
periodicity conclusion; it is not merely non-strict monotonicity. -/
def MonotoneIntersections : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, ∀ S : TransverseSegment F,
    ∀ (K : Set ℕ), IsLowerSet K → 1 ∈ K → ∀ t : ℕ → ℝ,
      (∀ n : ℕ, n+1 ∈ K → Successive F S.toStraightSegment x (t n) (t (n+1))) →
      ((∀ n ∈ K, flow F (t n) x = flow F (t 0) x) ∧
        _root_.D13Unified.Ch11.Orbits.HasLeastPeriod F x) ∨
      StrictMonoOn (fun n => segmentCoordinateValue S.toStraightSegment (flow F (t n) x)) K ∨
      StrictAntiOn (fun n => segmentCoordinateValue S.toStraightSegment (flow F (t n) x)) K

/-- Includes empty and singleton lists of meetings. A claim of periodicity
requires an actual return (at least two chronological meetings). -/
def AllIntersections : Prop :=
  ∀ (F : AutonomousODE Plane), ContDiffOn ℝ 1 (autonomousEvalValue F) F.domain →
    ∀ x ∈ F.domain, ∀ S : TransverseSegment F,
    ∀ (K : Set ℕ), IsLowerSet K → ∀ t : ℕ → ℝ,
      (∀ n : ℕ, n+1 ∈ K → Successive F S.toStraightSegment x (t n) (t (n+1))) →
      ((∀ n ∈ K, flow F (t n) x = flow F (t 0) x) ∧
        (1 ∈ K → _root_.D13Unified.Ch11.Orbits.HasLeastPeriod F x)) ∨
      StrictMonoOn (fun n => segmentCoordinateValue S.toStraightSegment (flow F (t n) x)) K ∨
      StrictAntiOn (fun n => segmentCoordinateValue S.toStraightSegment (flow F (t n) x)) K

end Specs.D13Unified.Ch13.MonotoneCrossings
