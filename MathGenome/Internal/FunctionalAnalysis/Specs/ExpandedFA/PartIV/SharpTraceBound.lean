import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.FractionalSobolev
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.SobolevTraceAndKernel
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.HalfSpaceExtension

/-! The half-space boundedness clause of `fa2:p4:sharp-trace`.
The interior space is the existing distributional first-jet graph, with its
sum norm. The boundary space is the existing fractional difference space
with Euclidean distance and its full Lp-plus-difference norm. A half-space
has dimension n+1, including the one-dimensional half-line when n=0.
The constant is uniform over the scalar field, normal coordinate and trace.
-/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.SharpTraceBound
open ExpandedFA.Distributions ExpandedFA.Sobolev
open ExpandedFA.Sobolev.HalfSpace ExpandedFA.Sobolev.Lines
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Reindex the n tangential coordinates by Fin n. This is exactly the
coordinate identification used by the accepted coordinate trace. -/
def boundaryCoordinates {n : ℕ} (i : Fin (n + 1)) : Domain n ≃ᵐ Transverse i :=
  MeasurableEquiv.piCongrLeft (fun _ : {j : Fin (n + 1) // j ≠ i} => ℝ)
    (finSuccAboveEquiv i)

lemma boundaryCoordinates_measurePreserving {n : ℕ} (i : Fin (n + 1)) :
    MeasurePreserving (boundaryCoordinates i) volume volume :=
  volume_measurePreserving_piCongrLeft _ _

/-- Reindexing changes neither the a.e. data nor the Lp norm. -/
def boundaryPullback {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (i : Fin (n + 1))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    Lp 𝕜 p (volume : Measure (Transverse i)) →ₗᵢ[𝕜]
      Lp 𝕜 p (volume : Measure (Domain n)) :=
  Lp.compMeasurePreservingₗᵢ 𝕜 (boundaryCoordinates i)
    (boundaryCoordinates_measurePreserving i)

/-- Smooth agreement for the already existing coordinate Sobolev trace.
It contains no assumed bound in the fractional norm. -/
def CoordinateTraceCondition {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (i : Fin (n + 1)) {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) : Prop :=
  ∀ (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) (f : Domain (n + 1) → 𝕜),
    ContDiff ℝ 1 f →
    u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict (upper i : Set (Domain (n + 1)))] f →
    T u =ᵐ[volume] fun y : Transverse i => f (coordinateLine i y 0)

/-- The original trace, expressed in the Fin n coordinates used by W^{s,p}. -/
def reindexedTrace {𝕜 : Type} [RCLike 𝕜] {n : ℕ} (i : Fin (n + 1))
    {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Transverse i))) :
    SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
      Lp 𝕜 p (volume : Measure (Domain n)) :=
  (boundaryPullback i p).toContinuousLinearMap.comp T

end ExpandedFA.PartIV.SharpTraceBound

namespace Specs.ExpandedFA.PartIV.SharpTraceBound
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.HalfSpace _root_.ExpandedFA.Sobolev.Lines
open _root_.ExpandedFA.PartIV.FractionalSobolev
open _root_.ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The analytic smooth estimate for positive boundary dimension.
Its datum g is an arbitrary Lp class of the actual smooth restriction, and
no fractional membership or trace bound is assumed. -/
def SmoothSeminormEstimate : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1))
      (u : SpaceValue 𝕜 (n + 1) (upper i) 1 p) (f : Domain (n + 1) → 𝕜)
      (g : Lp 𝕜 p (volume : Measure (Domain n))), ContDiff ℝ 1 f →
      u.val (zeroIndex (n + 1) 1) =ᵐ[volume.restrict
        (upper i : Set (Domain (n + 1)))] f →
      g =ᵐ[volume] (fun z => f (i.insertNth 0 z)) →
      differenceEnergy (1 - 1 / p.toReal) p g ^ (1 / p.toReal) ≤
        ENNReal.ofReal (K * ‖u‖)

/-- The endpoint exponent is exactly 1-1/p, and the conclusion uses the
full norm of the canonical fractional subtype. Trace existence is included
to make the universal formulation for the existing trace nonvacuous. -/
def BoundedTrace : Prop :=
  ∀ (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1)),
      (∃! T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
        Lp 𝕜 p (volume : Measure (Transverse i)), CoordinateTraceCondition i T) ∧
      ∀ (T : SpaceValue 𝕜 (n + 1) (upper i) 1 p →L[𝕜]
        Lp 𝕜 p (volume : Measure (Transverse i))), CoordinateTraceCondition i T →
      ∀ u, ∃ h : differenceEnergy (1 - 1 / p.toReal) p (reindexedTrace i T u) < ∞,
        fractionalNorm (1 - 1 / p.toReal) p ⟨reindexedTrace i T u, h⟩ ≤ C * ‖u‖

end Specs.ExpandedFA.PartIV.SharpTraceBound
