import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SobolevSpace
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! Scalar chain and bounded product clauses of paper.tex:1675–1684.
The scalar differential is always over ℝ, including for complex scalars.
There are no restrictions on dimension, the open set, or the exponent beyond p ≥ 1. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal NNReal ContDiff
namespace P102.U4

/-- The coordinate multi-index of order one. -/
def firstSobolevIndex {d : ℕ} (j : Fin d) : SobolevIndex d 1 :=
  ⟨{j}, by simp⟩

/-- The canonical weak coordinate derivative in the distribution graph. -/
abbrev firstWeakDerivative {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω 1 p) (j : Fin d) : DomainLp 𝕜 Ω p :=
  sobolevDerivative u (firstSobolevIndex j)

namespace ChainProductExpected

/-- All three zero-order integrability cases, with the full real differential. -/
def ChainRule : Prop :=
  ∀ {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u : Sobolev 𝕜 Ω 1 p) (F : 𝕜 → 𝕜),
    ContDiff ℝ 1 F → (∃ C : ℝ≥0, ∀ t, ‖fderiv ℝ F t‖ ≤ C) →
    (F 0 = 0 ∨ volume (Ω : Set (Space d)) < ⊤ ∨ p = ⊤) →
    ∃ w : Sobolev 𝕜 Ω 1 p,
      sobolevUnderlying w =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => F (sobolevUnderlying u x)) ∧
      ∀ j : Fin d, firstWeakDerivative w j =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => fderiv ℝ F (sobolevUnderlying u x) (firstWeakDerivative u j x))

/-- Boundedness means essential boundedness on the actual domain. -/
def ProductRule : Prop :=
  ∀ {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (p : ℝ≥0∞) [Fact (1 ≤ p)] (u v : Sobolev 𝕜 Ω 1 p),
    MemLp (sobolevUnderlying u) ∞ (volume.restrict (Ω : Set (Space d))) →
    MemLp (sobolevUnderlying v) ∞ (volume.restrict (Ω : Set (Space d))) →
    ∃ w : Sobolev 𝕜 Ω 1 p,
      sobolevUnderlying w =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => sobolevUnderlying u x * sobolevUnderlying v x) ∧
      ∀ j : Fin d, firstWeakDerivative w j =ᵐ[volume.restrict (Ω : Set (Space d))]
        (fun x => sobolevUnderlying v x * firstWeakDerivative u j x +
          sobolevUnderlying u x * firstWeakDerivative v j x)

end ChainProductExpected
end P102.U4
