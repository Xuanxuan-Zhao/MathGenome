import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SobolevSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Whole-space first-order conclusions used in paper.tex:1848–1878.
The gradient is the actual vector of coordinate weak derivatives with its
Euclidean norm. The infinity endpoint has its own statement, so no convention
about `ENNReal.toReal ∞` or smooth norm density is needed there. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal
namespace P102.Sobolev.MorreyWhole
open P102.U4

def firstIndex {d : ℕ} (i : Fin d) : SobolevIndex d 1 := ⟨{i}, by simp⟩

def gradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) (x : Space d) :
    PiLp 2 (fun _ : Fin d => 𝕜) :=
  WithLp.toLp 2 (fun i => sobolevDerivative u (firstIndex i) x)

def gradientNorm {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) : ℝ :=
  (eLpNorm (gradient u) p volume).toReal

def Represents {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p) (f : Space d → 𝕜) : Prop :=
  (sobolevUnderlying u : Space d → 𝕜) =ᵐ[volume] f

namespace Expected

def Finite : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ), 1 ≤ d →
  ∀ (p : ℝ≥0∞) [Fact (1 ≤ p)], (d : ℝ≥0∞) < p → p ≠ ⊤ →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 p,
    ∃ f : Space d → 𝕜, Continuous f ∧ Represents u f ∧
      (∀ x y, ‖f x - f y‖ ≤ C * gradientNorm u * ‖x - y‖ ^ (1 - (d : ℝ) / p.toReal)) ∧
      (∀ x, ‖f x‖ ≤ C * (‖sobolevUnderlying u‖ + gradientNorm u)) ∧
      ∀ g : Space d → 𝕜, Continuous g → Represents u g → g = f

def Infinity : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (d : ℕ), 1 ≤ d →
  ∃ C : ℝ, 0 ≤ C ∧ ∀ u : Sobolev 𝕜 (⊤ : Opens (Space d)) 1 ⊤,
    ∃ f : Space d → 𝕜, Continuous f ∧ Represents u f ∧
      (∀ x y, ‖f x - f y‖ ≤ C * gradientNorm u * ‖x - y‖) ∧
      (∀ x, ‖f x‖ ≤ ‖sobolevUnderlying u‖) ∧
      ∀ g : Space d → 𝕜, Continuous g → Represents u g → g = f

end Expected
end P102.Sobolev.MorreyWhole
