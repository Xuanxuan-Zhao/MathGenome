import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceGeometry
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceBound
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceLift

/-! Independent scope of the two-jet assertion in `paper.tex`,
`fa2:p4:second-trace` (19333–19386 in the adopted source).
The shared C² atlas, outward normal and distributional jet definitions are
reused from the component Specs. Both scalar fields, every natural dimension,
and empty boundaries are retained. The Green identities are allocated separately.
-/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions

/-- Correct the inward derivative to prescribe the outward derivative. -/
def correctedNormalDatum {𝕜 : Type} [RCLike 𝕜] {n : ℕ}
    (a : Domain n → ℝ) (b : Fin n → Domain n → ℝ)
    (q : Fin n → Domain n → 𝕜) (h : Domain n → 𝕜) : Domain n → 𝕜 :=
  fun x => (a x)⁻¹ • (h x - ∑ j, b j x • q j x)

end ExpandedFA.PartIV.SecondTrace

namespace Specs.ExpandedFA.PartIV.SecondTrace
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.Trace _root_.ExpandedFA.Sobolev.C1Extension
open _root_.ExpandedFA.Sobolev.HalfSpace _root_.ExpandedFA.Sobolev.Lines
open _root_.ExpandedFA.PartIV.FractionalSobolev _root_.ExpandedFA.PartIV.SecondTrace
open _root_.ExpandedFA.PartIV.SecondTraceFlat _root_.ExpandedFA.PartIV.SharpTraceBound
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The outward flat normal is minus the inward coordinate derivative. -/
def FlatOutwardExtension : Prop :=
  ∀ (n : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜] (i : Fin (n + 1)),
      ∃ E : HigherFractionalSpace 𝕜 n (2 - 1 / p.toReal) p →
          FractionalSpace 𝕜 n (1 - 1 / p.toReal) p →
          SpaceValue 𝕜 (n + 1) (upper i) 2 p,
        (∀ g h, ‖E g h‖ ≤ C *
          (higherFractionalNorm (2 - 1 / p.toReal) p g +
            fractionalNorm (1 - 1 / p.toReal) p h)) ∧
        (∀ T, CoordinateTraceCondition i T → ∀ g h,
          HasBoundaryJets i T (E g h)
            (wholeLp (g.val.val (zeroIndex n 1))) (-h.val))

/-- A genuine bounded scalar-linear jet map to the original surface Lp
classes. No sharp regularity is hidden in this elementary helper. -/
def LpJetMap : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (ν : Domain d → Domain d),
    (∀ j, AEStronglyMeasurable (fun x => ν x j) (surfaceMeasure Ω)) →
    (∀ j, ∀ᵐ x ∂surfaceMeasure Ω, ‖ν x j‖ ≤ 1) →
    ∀ T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p,
    ∃ J : SpaceValue 𝕜 d Ω 2 p →L[𝕜] (BoundaryLp 𝕜 Ω p × BoundaryLp 𝕜 Ω p),
      ∀ u, HasDomainJets ν T u (J u).1 (J u).2

/-- The pointwise coefficient correction, with no nonzero-mean or reality
restriction on the scalar boundary data. -/
def CoefficientCorrection : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (n : ℕ) (a : Domain n → ℝ)
    (b : Fin n → Domain n → ℝ) (q : Fin n → Domain n → 𝕜)
    (h : Domain n → 𝕜), (∀ x, a x ≠ 0) → ∀ x,
    a x • correctedNormalDatum a b q h x + ∑ j, b j x • q j x = h x

/-- Local chart correction is bounded on order 0<s<1. Bounds on a and
its reciprocal are geometric coefficient assumptions here; their derivation
on compact chart supports is part of the domain construction, not assumed
in the complete SecondTrace statement. -/
def BoundedCoefficientCorrection : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (n : ℕ) (s : ℝ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    0 < s → s < 1 → p ≠ ∞ →
    ∀ (a : Domain n → ℝ) (b : Fin n → Domain n → ℝ)
      (M L : ℝ≥0) (Mb Lb : Fin n → ℝ≥0),
    (∀ x, |(a x)⁻¹| ≤ M) →
    (∀ x y, |(a x)⁻¹ - (a y)⁻¹| ≤ L * euclideanLength (x-y)) →
    (∀ j x, |b j x| ≤ Mb j) →
    (∀ j x y, |b j x-b j y| ≤ Lb j * euclideanLength (x-y)) →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (q : Fin n → FractionalSpace 𝕜 n s p) (h : FractionalSpace 𝕜 n s p),
        ∃ k : FractionalSpace 𝕜 n s p,
          k.val =ᵐ[volume] correctedNormalDatum a b (fun j => (q j).val) h.val ∧
          fractionalNorm s p k ≤ C *
            (fractionalNorm s p h + ∑ j, fractionalNorm s p (q j))

/-- Genuine first traces exist at the same exponent. -/
def TraceExists : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
    (∀ x ∈ frontier (Ω : Set (Domain d)),
      ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
        x ∈ Φ.source ∧ Φ x i = 0 ∧
        ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
        ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∃ T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p, IsTrace T

/-- These statements use the shared, surface-faithful geometric definitions.
They construct geometry and sharp membership, rather than assuming them. -/
def GeometryExists : Prop := SecondTraceGeometry.GeometryExists

def HigherAtlasIndependence : Prop := SecondTraceGeometry.HigherAtlasIndependence

def BoundedTrace : Prop := SecondTraceBound.BoundedTrace

def OntoTrace : Prop := SecondTraceLift.OntoTrace

/-- A single scalar-linear map on the original W²,p graph, with values in
the original surface Lp quotient, has exactly the two sharp fractional data
spaces as its range. Its full fractional sum norm is bounded. The first trace,
atlas and outward normal are constructed from the original C² hypothesis. -/
def DomainJetTheorem : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) → IsC2Domain Ω →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∃ (B : C2BoundaryModel 𝕜 Ω p) (ν : Domain d → Domain d)
      (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
      (J : SpaceValue 𝕜 d Ω 2 p →L[𝕜]
        (BoundaryLp 𝕜 Ω p × BoundaryLp 𝕜 Ω p)) (C : ℝ),
      IsOutwardNormal Ω ν ∧ IsTrace T ∧ 0 ≤ C ∧
      (∀ u, HasDomainJets ν T u (J u).1 (J u).2 ∧
        ∃ (g : B.HigherData (2 - 1 / p.toReal))
          (h : B.toBoundaryModel.Data (1 - 1 / p.toReal)),
          g.val = (J u).1 ∧ h.val = (J u).2 ∧
          B.higherDataNorm (2 - 1 / p.toReal) g +
            B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h ≤ C * ‖u‖) ∧
      (∀ (g : B.HigherData (2 - 1 / p.toReal))
        (h : B.toBoundaryModel.Data (1 - 1 / p.toReal)),
        ∃ u, J u = (g.val, h.val))

/-- Complete assigned obligation, with explicit existence and a single bounded
scalar-linear map realizing both jets, and higher-order atlas independence. -/
def SecondTrace : Prop :=
  GeometryExists ∧ TraceExists ∧ HigherAtlasIndependence ∧ BoundedTrace ∧
    OntoTrace ∧ DomainJetTheorem

/-- Component assembly includes construction of the single simultaneous map. -/
def Assembly : Prop :=
  GeometryExists → HigherAtlasIndependence → BoundedTrace → OntoTrace → SecondTrace

end Specs.ExpandedFA.PartIV.SecondTrace
