import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ACL
import Mathlib.Analysis.Normed.Group.Pointwise

/-! The forward estimate in U4-05, paper.tex:1456–1460 and 1468.
The ball is a Euclidean open ball and integration uses the shared Euclidean
Lebesgue measure. Neighborhood inclusion expresses the interior margin without
assigning a finite distance to the complement of the whole space. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped Pointwise ENNReal
namespace P102.U4.DifferenceQuotient

/-- The source neighborhood V+B(0,|h|), in the Euclidean norm. -/
def neighborhood {d : ℕ} (V : Set (Space d)) (h : ℝ) : Set (Space d) :=
  V + Metric.ball 0 |h|

/-- Ambient representatives; all estimates are with restricted measures. -/
def quotient {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (u : Space d → 𝕜) (j : Fin d) (h : ℝ) (x : Space d) : 𝕜 :=
  h⁻¹ • (u (x + h • coordinateVector d j) - u x)

end DifferenceQuotient
namespace DifferenceQuotientExpected

/-- The functions u and v need only be locally integrable on Ω; only the
derivative v is assumed Lp on the neighborhood. No derivatives in directions
other than j are assumed. The constant-one estimate includes p=1 and real or
complex functions. -/
def Estimate : Prop :=
  ∀ (d : ℕ) (_hd : 0 < d) (𝕜 : Type) [RCLike 𝕜]
    (Ω V : Opens (Space d)) (j : Fin d) (h : ℝ)
    (p : ℝ≥0∞), 1 ≤ p → p ≠ ∞ → h ≠ 0 →
    IsCompact (closure (V : Set (Space d))) →
    closure (V : Set (Space d)) ⊆ (Ω : Set (Space d)) →
    DifferenceQuotient.neighborhood (V : Set (Space d)) h ⊆ (Ω : Set (Space d)) →
    ∀ (u v : Space d → 𝕜),
    LocallyIntegrableOn u Ω volume → LocallyIntegrableOn v Ω volume →
    MemLp v p (volume.restrict (DifferenceQuotient.neighborhood (V : Set (Space d)) h)) →
    distributionPartial {j} (regularDistribution Ω u) = regularDistribution Ω v →
    MemLp (DifferenceQuotient.quotient u j h) p (volume.restrict (V : Set (Space d))) ∧
      eLpNorm (DifferenceQuotient.quotient u j h) p (volume.restrict (V : Set (Space d))) ≤
        eLpNorm v p (volume.restrict
          (DifferenceQuotient.neighborhood (V : Set (Space d)) h))

end DifferenceQuotientExpected
end P102.U4
