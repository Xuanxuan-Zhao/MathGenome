import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceGeometry
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceFlat

/-! Independent boundedness statement for the two-jet trace theorem,
`paper.tex`, fa2:p4:second-trace. The data use the original surface measure,
and every interior representative is in the original distributional graph.
No trace-gradient commutation or fractional normal multiplier is assumed.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

namespace Specs.ExpandedFA.PartIV.SecondTraceBound
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.Trace _root_.ExpandedFA.PartIV.SecondTrace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/- These local predicate names avoid redeclaring the independently owned
parent and lifting interfaces. Their bodies are the original geometric and
distributional conditions, so applications to those interfaces reduce directly. -/

/-- The actual C² flattening hypothesis, including dimension zero. -/
def IsC2Domain {d : ℕ} (Ω : Opens (Domain d)) : Prop :=
  ∀ x ∈ frontier (Ω : Set (Domain d)),
    ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
      x ∈ Φ.source ∧ Φ x i = 0 ∧
      ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
      ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i

/-- An outward unit normal specified only by geometry. The sign is fixed by
r < 0 inside Ω. In particular, this predicate has no analytic multiplier field. -/
def GeometricNormal {d : ℕ} (Ω : Opens (Domain d))
    (ν : Domain d → Domain d) : Prop :=
  (∀ j : Fin d, Measurable (fun x => ν x j)) ∧
  (∀ j : Fin d, ∀ᵐ x ∂surfaceMeasure Ω, |ν x j| ≤ 1) ∧
  ∀ x ∈ frontier (Ω : Set (Domain d)),
    ∃ (U : Set (Domain d)) (r : Domain d → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 2 r U ∧ r x = 0 ∧
      (∀ y ∈ U, y ∈ Ω ↔ r y < 0) ∧
      (∑ j : Fin d, (fderiv ℝ r x (coordinateVector j)) ^ 2) ≠ 0 ∧
      ∀ j : Fin d, ν x j = fderiv ℝ r x (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2)

/-- Both jets are taken with the original first trace. The normal jet is
ν · Tr(∇u), using first-order graph representatives of the actual partial
weak derivatives of u. The a.e. identity is on the original surface measure. -/
def HasDomainJets {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (ν : Domain d → Domain d)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (u : SpaceValue 𝕜 d Ω 2 p) (g h : BoundaryLp 𝕜 Ω p) : Prop :=
  ∃ (v : SpaceValue 𝕜 d Ω 1 p) (w : Fin d → SpaceValue 𝕜 d Ω 1 p),
    v.val (zeroIndex d 1) = u.val (zeroIndex d 2) ∧
    (∀ j, (w j).val (zeroIndex d 1) =
      u.val (_root_.ExpandedFA.PartIV.SecondTraceFlat.normalIndex j)) ∧
    T v = g ∧ h =ᵐ[surfaceMeasure Ω] fun x => ∑ j : Fin d, ν x j • T (w j) x

/-- Full bound into W^(2-1/p,p) × W^(1-1/p,p), for every faithful C²
boundary model, geometric normal and original trace, with both membership
witnesses constructed and the sum of the two full atlas norms controlled. -/
def BoundedTrace : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) → IsC2Domain Ω →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ (B : C2BoundaryModel 𝕜 Ω p) (ν : Domain d → Domain d),
      GeometricNormal Ω ν → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
      ∀ u : SpaceValue 𝕜 d Ω 2 p,
        ∃ (g : B.HigherData (2 - 1 / p.toReal))
          (h : B.toBoundaryModel.Data (1 - 1 / p.toReal)),
          HasDomainJets ν T u g.val h.val ∧
          B.higherDataNorm (2 - 1 / p.toReal) g +
            B.toBoundaryModel.dataNorm (1 - 1 / p.toReal) h ≤ C * ‖u‖

end Specs.ExpandedFA.PartIV.SecondTraceBound
