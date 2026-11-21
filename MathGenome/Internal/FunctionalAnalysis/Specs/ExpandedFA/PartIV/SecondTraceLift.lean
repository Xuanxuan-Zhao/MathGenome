import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceGeometry
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SecondTraceFlat

/-! Independent simultaneous domain-jet surjectivity statement for
`paper.tex`, fa2:p4:second-trace. The two data are independent members of
the original surface-measure quotient. No lifting or transport certificate
is a hypothesis, and no assertion at p = 1 is made. -/

noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The original C² flattening condition, before taking a finite atlas. -/
def IsC2Domain {d : ℕ} (Ω : Opens (Domain d)) : Prop :=
  ∀ x ∈ frontier (Ω : Set (Domain d)),
    ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
      x ∈ Φ.source ∧ Φ x i = 0 ∧
      ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
      ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i

/-- Outward is determined by a local defining function negative in Ω.
There are no analytic normal-multiplier or trace assumptions here. -/
def IsOutwardNormal {d : ℕ} (Ω : Opens (Domain d)) (ν : Domain d → Domain d) : Prop :=
  (∀ j : Fin d, Measurable (fun x => ν x j)) ∧
  (∀ j : Fin d, ∀ᵐ x ∂surfaceMeasure Ω, |ν x j| ≤ 1) ∧
  ∀ x ∈ frontier (Ω : Set (Domain d)),
    ∃ (U : Set (Domain d)) (r : Domain d → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 2 r U ∧ r x = 0 ∧
      (∀ y ∈ U, y ∈ Ω ↔ r y < 0) ∧
      (∑ j : Fin d, (fderiv ℝ r x (coordinateVector j)) ^ 2) ≠ 0 ∧
      ∀ j : Fin d, ν x j = fderiv ℝ r x (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2)

/-- The traces are those of u and of its actual first weak derivatives.
The normal trace means the surface-a.e. contraction of the derivative
traces with the geometric outward normal. All graph witnesses are outputs. -/
def HasDomainJets {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {Ω : Opens (Domain d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (ν : Domain d → Domain d)
    (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p)
    (u : SpaceValue 𝕜 d Ω 2 p) (g h : BoundaryLp 𝕜 Ω p) : Prop :=
  ∃ (v : SpaceValue 𝕜 d Ω 1 p) (w : Fin d → SpaceValue 𝕜 d Ω 1 p),
    v.val (zeroIndex d 1) = u.val (zeroIndex d 2) ∧
    (∀ j, (w j).val (zeroIndex d 1) = u.val (SecondTraceFlat.normalIndex j)) ∧
    T v = g ∧
    h =ᵐ[surfaceMeasure Ω] fun x => ∑ j : Fin d, (ν x j : 𝕜) * T (w j) x

end ExpandedFA.PartIV.SecondTrace

namespace Specs.ExpandedFA.PartIV.SecondTraceLift
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.Trace _root_.ExpandedFA.PartIV.SecondTrace
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- Simultaneous surjectivity for all the stated domains, models, normals,
and genuine first trace maps, retaining empty and zero-dimensional cases. -/
def OntoTrace : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) → IsC2Domain Ω →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ (B : C2BoundaryModel 𝕜 Ω p) (ν : Domain d → Domain d),
      IsOutwardNormal Ω ν →
    ∀ (T : SpaceValue 𝕜 d Ω 1 p →L[𝕜] BoundaryLp 𝕜 Ω p), IsTrace T →
    ∀ (g : B.HigherData (2 - 1 / p.toReal))
      (h : B.toBoundaryModel.Data (1 - 1 / p.toReal)),
      ∃ u : SpaceValue 𝕜 d Ω 2 p, HasDomainJets ν T u g.val h.val

end Specs.ExpandedFA.PartIV.SecondTraceLift
