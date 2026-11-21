import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SobolevSpace

/-! Whole-space clause of paper.tex, Theorem AN-11-C04-R02 (1782–1821).
The scalar field is real or complex. Exponents are nonnegative reals subject
only to 1 ≤ p < d; thus all real exponents in the source range are included.
The gradient uses the actual first derivative coordinates and the Euclidean
norm, while the Sobolev graph retains its existing sum norm. -/
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace P102.Sobolev
open P102.U4

def firstIndex {d : ℕ} (i : Fin d) : SobolevIndex d 1 := ⟨{i}, by simp⟩

def criticalExponent (d : ℕ) (p : ℝ≥0) : ℝ≥0 := d * p / (d - p)

/-- Euclidean weak gradient of the distribution-defined Sobolev class. -/
def weakGradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) :
    Space d → EuclideanSpace 𝕜 (Fin d) :=
  fun x => WithLp.toLp 2 (fun i => sobolevDerivative u (firstIndex i) x)

namespace SubcriticalWholeExpected
/-- Homogeneous estimate, including p=1, for all whole-space W¹ᵖ classes.
The constant depends only on d,p, with no support or zero-boundary assumption. -/
def Inequality : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (p : ℝ≥0), 1 ≤ p → p < d →
    ∃ C : ℝ≥0, ∀ (𝕜 : Type) [RCLike 𝕜] [Fact (1 ≤ (p : ℝ≥0∞))]
      (u : U4.Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p),
      MemLp (weakGradient u) p volume ∧
      MemLp (sobolevUnderlying u) (criticalExponent d p) volume ∧
      eLpNorm (sobolevUnderlying u) (criticalExponent d p) volume ≤
        (C : ℝ≥0∞) * eLpNorm (weakGradient u) p volume
end SubcriticalWholeExpected
end P102.Sobolev
