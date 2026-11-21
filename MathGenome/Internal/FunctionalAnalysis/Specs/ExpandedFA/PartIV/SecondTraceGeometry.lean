import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SharpTrace

/-! C² geometry for `fa2:p4:second-trace`, paper.tex:19220–19268.
This file is independent of the candidate implementation and contains no
Sobolev transport, trace, or lifting certificates. The original surface
measure and the actual distributional higher fractional spaces are retained.
-/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal

namespace ExpandedFA.PartIV.SecondTrace
open ExpandedFA.Distributions ExpandedFA.Sobolev ExpandedFA.Sobolev.Trace
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTrace

/-- Remove the inward normal coordinate, including the empty dimension case. -/
def tangentialCoordinates : {d : ℕ} → Fin d → Domain d → Domain (d - 1)
  | 0, i, _ => Fin.elim0 i
  | _ + 1, i, x => i.removeNth x

/-- A faithful surface model whose charts are restrictions of actual ambient
C² flattenings and whose partition consists of smooth ambient test functions.
The chart equality is required on the entire source, not just a.e. -/
structure C2BoundaryModel (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (Ω : Opens (Domain d)) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    extends BoundaryModel 𝕜 Ω p where
  normal : Fin chartCount → Fin d
  ambient : Fin chartCount → OpenPartialHomeomorph (Domain d) (Domain d)
  regular : ∀ j, ContDiffOn ℝ 2 (ambient j) (ambient j).source ∧
    ContDiffOn ℝ 2 (ambient j).symm (ambient j).target
  side : ∀ j y, y ∈ (ambient j).source → (y ∈ Ω ↔ 0 < ambient j y (normal j))
  chart_source : ∀ j, (atlas.chart j).source = Subtype.val ⁻¹' (ambient j).source
  chart_apply : ∀ j x, x ∈ (atlas.chart j).source →
    atlas.chart j x = tangentialCoordinates (normal j) (ambient j x.val)
  test : Fin chartCount → Tests ℝ (⊤ : Opens (Domain d))
  cutoff_eq : ∀ j x, atlas.cutoff j x = test j x.val
  test_subordinate : ∀ j, tsupport (test j) ⊆ (ambient j).source

namespace C2BoundaryModel
variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
  {p : ℝ≥0∞} [Fact (1 ≤ p)] (B : C2BoundaryModel 𝕜 Ω p)

/-- Each local Lp piece has a genuine W¹,p graph representative whose actual
first weak derivatives have finite order-(σ-1) difference energy. -/
def HasHigherEnergy (σ : ℝ) (g : BoundaryLp 𝕜 Ω p) : Prop :=
  ∀ j, ∃ u : HigherFractionalSpace 𝕜 (d - 1) σ p,
    wholeLp (u.val.val (zeroIndex (d - 1) 1)) = B.atlas.localizedLp p j (B.identify g)

abbrev HigherData (σ : ℝ) := {g : BoundaryLp 𝕜 Ω p // B.HasHigherEnergy σ g}

/-- A chosen graph witness. Its independence is a theorem of the implementation. -/
def higherPiece (σ : ℝ) (g : B.HigherData σ) (j : Fin B.chartCount) :
    HigherFractionalSpace 𝕜 (d - 1) σ p := Classical.choose (g.property j)

def higherDataNorm (σ : ℝ) (g : B.HigherData σ) : ℝ :=
  ∑ j, higherFractionalNorm σ p (B.higherPiece σ g j)
end C2BoundaryModel

end ExpandedFA.PartIV.SecondTrace

namespace Specs.ExpandedFA.PartIV.SecondTraceGeometry
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev _root_.ExpandedFA.Sobolev.Trace
open _root_.ExpandedFA.PartIV.SecondTrace _root_.ExpandedFA.PartIV.FractionalSobolev

/-- The written-out C² hypothesis is the original flattening condition,
with no assumed finite atlas, normal, or analytic transport. -/
def FiniteC2Charts : Prop :=
  ∀ (d : ℕ) (Ω : Opens (Domain d)),
    (∀ x ∈ frontier (Ω : Set (Domain d)),
      ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
        x ∈ Φ.source ∧ Φ x i = 0 ∧
        ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
        ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) →
    IsCompact (frontier (Ω : Set (Domain d))) →
    ∃ (N : ℕ) (i : Fin N → Fin d)
      (Φ : Fin N → OpenPartialHomeomorph (Domain d) (Domain d))
      (K L : Fin N → ℝ≥0),
      (∀ j, ContDiffOn ℝ 2 (Φ j) (Φ j).source ∧
        ContDiffOn ℝ 2 (Φ j).symm (Φ j).target ∧
        Bornology.IsBounded (Φ j).source ∧ Bornology.IsBounded (Φ j).target ∧
        (∀ y ∈ (Φ j).source, y ∈ Ω ↔ 0 < Φ j y (i j)) ∧
        LipschitzOnWith (K j) (Φ j) (Φ j).source ∧
        LipschitzOnWith (L j) (Φ j).symm (Φ j).target) ∧
      frontier (Ω : Set (Domain d)) ⊆ ⋃ j, (Φ j).source

/-- Full geometric existence, at all allowed dimensions and exponents. -/
def GeometryExists : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
    (∀ x ∈ frontier (Ω : Set (Domain d)),
      ∃ (i : Fin d) (Φ : OpenPartialHomeomorph (Domain d) (Domain d)),
        x ∈ Φ.source ∧ Φ x i = 0 ∧
        ContDiffOn ℝ 2 Φ Φ.source ∧ ContDiffOn ℝ 2 Φ.symm Φ.target ∧
        ∀ y ∈ Φ.source, y ∈ Ω ↔ 0 < Φ y i) →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
      Nonempty (C2BoundaryModel 𝕜 Ω p) ∧ ∃ ν : Domain d → Domain d,
      (∀ j : Fin d, Measurable (fun x => ν x j)) ∧
  (∀ j : Fin d, ∀ᵐ x ∂surfaceMeasure Ω, |ν x j| ≤ 1) ∧
  ∀ x ∈ frontier (Ω : Set (Domain d)),
    ∃ (U : Set (Domain d)) (r : Domain d → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContDiffOn ℝ 2 r U ∧ r x = 0 ∧
      (∀ y ∈ U, y ∈ Ω ↔ r y < 0) ∧
      (∑ j : Fin d, (fderiv ℝ r x (coordinateVector j)) ^ 2) ≠ 0 ∧
      ∀ j : Fin d, ν x j = fderiv ℝ r x (coordinateVector j) /
        Real.sqrt (∑ k : Fin d, (fderiv ℝ r x (coordinateVector k)) ^ 2)

/-- Membership and two-sided full-norm bounds on the ORIGINAL surface Lp
quotient, for every pair of C² models. Constants are strictly positive. -/
def HigherAtlasIndependence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → p ≠ ∞ →
    ∀ (B D : C2BoundaryModel 𝕜 Ω p),
      (∀ g, B.HasHigherEnergy (2 - 1 / p.toReal) g ↔
        D.HasHigherEnergy (2 - 1 / p.toReal) g) ∧
      ∃ C E : ℝ, 0 < C ∧ 0 < E ∧
        ∀ (g : B.HigherData (2 - 1 / p.toReal))
          (h : D.HigherData (2 - 1 / p.toReal)), g.val = h.val →
          D.higherDataNorm (2 - 1 / p.toReal) h ≤
            C * B.higherDataNorm (2 - 1 / p.toReal) g ∧
          B.higherDataNorm (2 - 1 / p.toReal) g ≤
            E * D.higherDataNorm (2 - 1 / p.toReal) h
end Specs.ExpandedFA.PartIV.SecondTraceGeometry
