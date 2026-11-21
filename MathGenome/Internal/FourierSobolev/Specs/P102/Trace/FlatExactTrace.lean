import MathGenome.Internal.FourierSobolev.Specs.P102.Trace.FlatTrace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.FractionalSobolev
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.SharpTraceBound

/-! Independent formulation of paper.tex:2462–2522, the case 1 < p < ∞.
The boundary is reindexed by Fin m, with product Lebesgue measure. The library
fractional space uses Euclidean length (the norm of `WithLp.toLp 2 h`), not
the supremum norm on the product coordinates. Its norm is the full Lp norm
plus the Gagliardo seminorm. This is an equivalent coordinate representation
of the fractional space, not a choice of different boundary data.
-/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology

namespace P102.Trace

/-- The defining property of the existing flat trace, including its endpoint.
Values at exceptional raw heights cannot be used to define this map. -/
def IsFlatTrace {m : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (T : HalfSobolev m 𝕜 p →L[𝕜] BoundaryLp m 𝕜 p) : Prop :=
  ∀ u, ∃ F : ℝ → BoundaryLp m 𝕜 p, IsSliceRepresentative u F ∧ F 0 = T u

namespace FlatExactTraceExpected
open ExpandedFA.PartIV.FractionalSobolev ExpandedFA.PartIV.SharpTraceBound

/-- The same slice trace has the sharp full fractional norm bound and a
bounded scalar-linear right inverse. The constants depend only on m and p.
The assertion is universal over slice traces, and their existence is explicit. -/
def ExactFlatTrace : Prop :=
  ∀ (m : ℕ), 1 ≤ m → ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], 1 < p → ∀ hp : p ≠ ∞,
    letI : Fact (p ≠ ∞) := ⟨hp⟩
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝕜 : Type) [RCLike 𝕜],
      (∃ T : HalfSobolev m 𝕜 p →L[𝕜] BoundaryLp m 𝕜 p, IsFlatTrace T) ∧
      ∀ T : HalfSobolev m 𝕜 p →L[𝕜] BoundaryLp m 𝕜 p, IsFlatTrace T →
        (∀ u, ∃ h : differenceEnergy (1 - 1 / p.toReal) p
            (boundaryPullback (Fin.last m) p (T u)) < ∞,
          fractionalNorm (1 - 1 / p.toReal) p
            ⟨boundaryPullback (Fin.last m) p (T u), h⟩ ≤ C * ‖u‖) ∧
        (∃ L : FractionalSpace 𝕜 m (1 - 1 / p.toReal) p →L[𝕜] HalfSobolev m 𝕜 p,
          (∀ g, ‖L g‖ ≤ C * fractionalNorm (1 - 1 / p.toReal) p g) ∧
          ∀ g, boundaryPullback (Fin.last m) p (T (L g)) = g.val)

end FlatExactTraceExpected
end P102.Trace
