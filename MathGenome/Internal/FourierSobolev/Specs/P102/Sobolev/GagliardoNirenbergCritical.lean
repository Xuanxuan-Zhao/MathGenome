import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SubcriticalWhole

/-! Critical whole-space clause of paper.tex, Theorem U5-02 (1962–1983,
2006–2022). Finite NNReal exponents range over all real 1 ≤ r ≤ q < ∞.
The functions are the existing distribution-defined Sobolev classes, with
the canonical Euclidean weak gradient. No support assumption is imposed.
ENNReal.rpow_zero = 1 omits the gradient factor at q = r, also for zero gradient. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace P102.Sobolev
namespace GagliardoNirenbergCriticalExpected

def Inequality : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (r q : ℝ≥0), 1 ≤ r → r ≤ q →
    ∃ C : ℝ≥0, ∀ (𝕜 : Type) [RCLike 𝕜] [Fact (1 ≤ (d : ℝ≥0∞))]
      (u : U4.Sobolev 𝕜 (⊤ : Opens (U4.Space d)) 1 (d : ℝ≥0∞)),
      MemLp (U4.sobolevUnderlying u) r volume →
      MemLp (U4.sobolevUnderlying u) q volume ∧
      eLpNorm (U4.sobolevUnderlying u) q volume ≤
        (C : ℝ≥0∞) * eLpNorm (weakGradient u) (d : ℝ≥0∞) volume ^
          (1 - (r : ℝ) / q) *
          eLpNorm (U4.sobolevUnderlying u) r volume ^ ((r : ℝ) / q)

end GagliardoNirenbergCriticalExpected
end P102.Sobolev
