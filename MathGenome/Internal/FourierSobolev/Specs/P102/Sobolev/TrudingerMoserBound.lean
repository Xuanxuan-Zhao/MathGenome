import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ZeroExtension
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ChainProduct
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Independent scope of the upper-bound part of paper.tex:2180–2228.
The nonnegative extended integral asserts finiteness as well as the estimate.
The sphere measure is the Euclidean surface measure from polar coordinates.
No regularity of the boundary of the open set is assumed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal
namespace P102.Sobolev
open P102.U4
namespace TrudingerMoser

/-- Area of the Euclidean unit sphere, with its unnormalized surface measure. -/
def sphereArea (d : ℕ) : ℝ :=
  (volume : Measure (Space d)).toSphere.real Set.univ

/-- The sharp coefficient α_d = d σ_{d-1}^{1/(d-1)}. -/
def sharpCoefficient (d : ℕ) : ℝ :=
  (d : ℝ) * sphereArea d ^ (1 / ((d : ℝ) - 1))

/-- The critical power d/(d-1). -/
def criticalPower (d : ℕ) : ℝ := (d : ℝ) / ((d : ℝ) - 1)

/-- Euclidean weak gradient, also for complex-valued functions. -/
def weakGradient {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 Ω 1 p) (x : Space d) : EuclideanSpace 𝕜 (Fin d) :=
  WithLp.toLp 2 (fun j => firstWeakDerivative u j x)

end TrudingerMoser
namespace TrudingerMoserExpected
open TrudingerMoser

/-- The constant depends only on dimension, uniformly for real and complex
scalars and for every nonempty bounded open set. -/
def Bound : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d),
    letI : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)),
        (Ω : Set (Space d)).Nonempty → Bornology.IsBounded (Ω : Set (Space d)) →
        ∀ u : SobolevZero 𝕜 Ω 1 (d : ℝ≥0∞),
          eLpNorm (weakGradient u.val) (d : ℝ≥0∞)
            (volume.restrict (Ω : Set (Space d))) ≤ 1 →
          (∫⁻ x in (Ω : Set (Space d)),
            ENNReal.ofReal (Real.exp
              (sharpCoefficient d * ‖sobolevUnderlying u.val x‖ ^ criticalPower d))) ≤
            ENNReal.ofReal C * volume (Ω : Set (Space d))

end TrudingerMoserExpected
end P102.Sobolev
