import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.C1DomainExtension
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Sobolev.AbsoluteContinuityOnLines
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Independent statements for the subcritical and critical finite-exponent
clauses of paper.tex, fa2:p4:sobolev-embedding (17799–17832).
The Sobolev space is the accepted distributional derivative graph. Its norm
is the sum-component norm; the gradient below has the pointwise Euclidean norm.
All finite exponents ≥ 1, both scalar fields, and empty domains are retained.
The subcritical hypotheses themselves imply d ≥ 2. The critical statement
includes d = p = 1, and does not assert an L∞ endpoint. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal

namespace ExpandedFA.Sobolev.Subcritical
open ExpandedFA.Distributions
open Specs.ExpandedFA.Sobolev.WeakDerivativeSpaces

/-- The usual exponent dp/(d-p), in the range p < d. -/
def criticalExponent (d : ℕ) (p : ℝ≥0) : ℝ≥0 := d * p / (d - p)

/-- The multi-index of the j-th first weak derivative. -/
def firstIndex {d : ℕ} (j : Fin d) : DerivativeIndex d 1 := by
  classical
  exact ⟨fun i => ⟨if i = j then 1 else 0, by split_ifs <;> decide⟩, by simp⟩

/-- The actual Euclidean gradient of a class in the canonical derivative graph. -/
def weakGradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (u : SpaceValue 𝕜 d Ω 1 p) :
    Domain d → EuclideanSpace 𝕜 (Fin d) :=
  fun x => WithLp.toLp 2 (fun j => u.val (firstIndex j) x)

/-- Classical gradient, with the same coordinates and Euclidean norm. -/
def classicalGradient {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (u : Domain d → 𝕜) :
    Domain d → EuclideanSpace 𝕜 (Fin d) :=
  fun x => WithLp.toLp 2 (fun j => fderiv ℝ u x (coordinateVector j))

end ExpandedFA.Sobolev.Subcritical

namespace Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding
open _root_.ExpandedFA.Distributions _root_.ExpandedFA.Sobolev
open _root_.ExpandedFA.Sobolev.Subcritical WeakDerivativeSpaces

/-- A dimension/exponent constant, uniform over compact supports and scalar fields.
The C¹ theorem includes the source's C∞ version. -/
def CompactSmoothInequality : Prop :=
  ∀ (d : ℕ) (p : ℝ≥0), 1 ≤ p → p < d → ∃ C : ℝ≥0,
    ∀ (𝕜 : Type) [RCLike 𝕜] (u : Domain d → 𝕜),
      ContDiff ℝ 1 u → HasCompactSupport u →
      MemLp u (criticalExponent d p) volume ∧
      MemLp (classicalGradient u) p volume ∧
      eLpNorm u (criticalExponent d p) volume ≤
        (C : ℝ≥0∞) * eLpNorm (classicalGradient u) p volume

/-- Coordinate form of the whole-space analytic estimate. Its hypotheses are
exactly membership and weak derivatives in the accepted coordinate model.
This is an intermediate proposition, not an assumed certificate. -/
def CoordinateWholeSpaceInequality : Prop :=
  ∀ (d : ℕ) (p : ℝ≥0), 1 ≤ p → p < d →
    ∃ C : ℝ≥0, ∀ (𝕜 : Type) [RCLike 𝕜] [Fact (1 ≤ (p : ℝ≥0∞))]
      (u : DomainLp 𝕜 (⊤ : Opens (Domain d)) p)
      (g : Fin d → DomainLp 𝕜 (⊤ : Opens (Domain d)) p),
      Lines.HasWeakCoordinateDerivatives u g →
      MemLp u (criticalExponent d p) volume ∧
      eLpNorm u (criticalExponent d p) volume ≤
        (C : ℝ≥0∞) * ∑ j : Fin d, eLpNorm (g j) p volume

/-- The homogeneous inequality for all W¹ᵖ functions on the whole space,
with no compact support or zero-boundary assumption. -/
def WholeSpaceInequality : Prop :=
  ∀ (d : ℕ) (p : ℝ≥0), 1 ≤ p → p < d →
    ∃ C : ℝ≥0, ∀ (𝕜 : Type) [RCLike 𝕜] [Fact (1 ≤ (p : ℝ≥0∞))]
      (u : SpaceValue 𝕜 d ⊤ 1 p),
      MemLp (u.val (zeroIndex d 1)) (criticalExponent d p) volume ∧
      eLpNorm (u.val (zeroIndex d 1)) (criticalExponent d p) volume ≤
        (C : ℝ≥0∞) * eLpNorm (weakGradient u) p volume

/-- Bounded C¹ domains have the full-norm embedding into the critical Lp space. -/
def BoundedDomainInequality : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (Ω : Opens (Domain d)),
    C1Extension.IsC1Domain Ω → Bornology.IsBounded (Ω : Set (Domain d)) →
    ∀ (p : ℝ≥0), 1 ≤ p → p < d →
      ∃ C : ℝ≥0, ∀ [Fact (1 ≤ (p : ℝ≥0∞))] (u : SpaceValue 𝕜 d Ω 1 p),
        MemLp (u.val (zeroIndex d 1)) (criticalExponent d p)
          (volume.restrict (Ω : Set (Domain d))) ∧
        eLpNorm (u.val (zeroIndex d 1)) (criticalExponent d p)
          (volume.restrict (Ω : Set (Domain d))) ≤ (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖

/-- At p=d all finite target exponents ≥1 are allowed, including the
one-dimensional critical case. No nonemptiness assumption is imposed. -/
def CriticalBoundedDomainInequality : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ), 1 ≤ d →
    ∀ (Ω : Opens (Domain d)), C1Extension.IsC1Domain Ω →
      Bornology.IsBounded (Ω : Set (Domain d)) →
      ∀ (q : ℝ≥0), 1 ≤ q →
        ∃ C : ℝ≥0, ∀ [Fact (1 ≤ (d : ℝ≥0∞))] (u : SpaceValue 𝕜 d Ω 1 d),
          MemLp (u.val (zeroIndex d 1)) q (volume.restrict (Ω : Set (Domain d))) ∧
          eLpNorm (u.val (zeroIndex d 1)) q (volume.restrict (Ω : Set (Domain d))) ≤
            (C : ℝ≥0∞) * ENNReal.ofReal ‖u‖

/-- Representation bridge, without assuming the analytic estimate. -/
def WholeSpaceFromCoordinates : Prop :=
  CoordinateWholeSpaceInequality → WholeSpaceInequality

/-- Extension reduction, without assuming the whole-space estimate. -/
def BoundedDomainFromWholeSpace : Prop :=
  WholeSpaceInequality → BoundedDomainInequality

end Specs.ExpandedFA.Sobolev.SubcriticalSobolevEmbedding
