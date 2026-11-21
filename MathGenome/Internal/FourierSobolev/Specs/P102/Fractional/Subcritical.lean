import MathGenome.Internal.FourierSobolev.Specs.P102.Fractional.Extension

/-!
Independent statements for the subcritical continuous embedding in
paper.tex, Theorem U5-05 (2322–2335), and its proof (2359–2399).
The scalar field may be real or complex. The dimension is positive, the source
exponent is finite and includes one, and no support condition is imposed.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal Topology

namespace P102.Fractional

/-- The critical fractional Sobolev exponent `d p / (d - s p)`.
It is used under `s * p.toReal < d`, so the denominator is strictly positive.
The total definition outside that range does not assert any embedding there. -/
def sobolevExponent (d : ℕ) (s : ℝ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal ((d : ℝ) * p.toReal / ((d : ℝ) - s * p.toReal))

end P102.Fractional

namespace Specs.P102.Fractional.Subcritical
open _root_.P102.Fractional
universe u

/-- The homogeneous whole-space estimate, with membership explicitly stated.
The right hand side contains only the Gagliardo seminorm, with no zero-order
term. There is no bounded-support or smoothness hypothesis on the input. -/
def wholeSpace : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → s * p.toReal < (d : ℝ) →
  ∀ (𝕜 : Type u) [RCLike 𝕜], ∃ C : ℝ≥0,
    ∀ u : Space 𝕜 (Set.univ : Set (Domain d)) s p,
      MemLp (firstProjection u) (sobolevExponent d s p) (domainMeasure Set.univ) ∧
      eLpNorm (firstProjection u) (sobolevExponent d s p) (domainMeasure Set.univ) ≤
        (C : ℝ≥0∞) * seminorm Set.univ s p (firstProjection u)

/-- The bounded Lipschitz open-set estimate by the full Gagliardo norm.
There is no connectedness or nonemptiness hypothesis; `n = 0` covers dimension
one. All objects and the geometric condition are the upstream canonical ones.
Extended norms avoid interpreting a divergent norm as zero via `toReal`. -/
def boundedDomain : Prop :=
  ∀ (n : ℕ) (G : Set (Domain (n + 1))), IsBoundedLipschitzOpen G →
  ∀ (s : ℝ), 0 < s → s < 1 →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ∞ → s * p.toReal < (n + 1 : ℕ) →
  ∀ (𝕜 : Type u) [RCLike 𝕜], ∃ C : ℝ≥0,
    ∀ u : Space 𝕜 G s p,
      MemLp (firstProjection u) (sobolevExponent (n + 1) s p) (domainMeasure G) ∧
      eLpNorm (firstProjection u) (sobolevExponent (n + 1) s p) (domainMeasure G) ≤
        (C : ℝ≥0∞) *
          (eLpNorm (firstProjection u) p (domainMeasure G) +
            seminorm G s p (firstProjection u))

end Specs.P102.Fractional.Subcritical
