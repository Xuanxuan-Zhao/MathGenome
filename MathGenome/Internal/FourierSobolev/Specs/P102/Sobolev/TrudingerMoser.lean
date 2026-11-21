import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.MoserMembership
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Complete scope of paper.tex:2180–2250 and the endpoint observation at
2030–2033. The upper bound uses the shared sphere measure and coefficient.
Sharpness is stated as an extended supremum, and concentration uses continuous
representatives of actual W₀ classes, with the exact gradient normalization.
No regularity of the boundary is imposed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace P102.Sobolev
namespace TrudingerMoserExpected
open P102.U4 TrudingerMoser

/-- This is exactly the already allocated endpoint upper bound. -/
def UpperBound : Prop := Bound

/-- Infinite supremum for every coefficient strictly above the sharp one.
Real witnesses suffice for failure of a scalar inequality. -/
def Sharpness : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d),
    letI : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
    ∀ (Ω : Opens (Space d)),
      (Ω : Set (Space d)).Nonempty → Bornology.IsBounded (Ω : Set (Space d)) →
      ∀ α : ℝ, sharpCoefficient d < α →
        (⨆ (u : SobolevZero ℝ Ω 1 (d : ℝ≥0∞))
          (_ : eLpNorm (weakGradient u.val) (d : ℝ≥0∞)
            (volume.restrict (Ω : Set (Space d))) ≤ 1),
          exponentialIntegral Ω α (sobolevUnderlying u.val)) = ⊤

/-- All finite positive exponents are included (hence all finite Lʳ norms).
The bound is uniform over the entire gradient unit ball. -/
def UniformFiniteNorms : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d),
    letI : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
    ∀ (Ω : Opens (Space d)),
      (Ω : Set (Space d)).Nonempty → Bornology.IsBounded (Ω : Set (Space d)) →
      ∀ r : ℝ≥0∞, 0 < r → r < ⊤ → ∃ B : ℝ≥0∞, B < ⊤ ∧
        ∀ u : SobolevZero ℝ Ω 1 (d : ℝ≥0∞),
          eLpNorm (weakGradient u.val) (d : ℝ≥0∞)
            (volume.restrict (Ω : Set (Space d))) ≤ 1 →
          MemLp (sobolevUnderlying u.val) r (volume.restrict (Ω : Set (Space d))) ∧
          eLpNorm (sobolevUnderlying u.val) r (volume.restrict (Ω : Set (Space d))) ≤ B

/-- Geometric construction interface. This is a Prop definition, not
an assumption or a certificate: the source profiles must be realized as actual
zero-boundary Sobolev classes with exact Euclidean gradient norm one. -/
def ProfileMembership : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d),
    letI : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
    ∀ (Ω : Opens (Space d)) (c : Space d) (R : ℝ),
      0 < R → Metric.closedBall c R ⊆ (Ω : Set (Space d)) →
      ∀ L : ℝ, 0 < L → ∃ u : SobolevZero ℝ Ω 1 (d : ℝ≥0∞),
        (sobolevUnderlying u.val : Space d → ℝ) =ᵐ[volume.restrict (Ω : Set (Space d))]
          moserFunction c R L ∧
        eLpNorm (weakGradient u.val) (d : ℝ≥0∞)
          (volume.restrict (Ω : Set (Space d))) = 1

/-- Elementary profile interface, independent of weak derivatives.
Continuity, the central plateau, and the shrinking ball give these two limits. -/
def ProfileDivergence : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Ω : Opens (Space d)) (c : Space d) (R : ℝ),
    0 < R → Metric.closedBall c R ⊆ (Ω : Set (Space d)) →
      (∀ L : ℝ, 0 < L → Continuous (moserFunction c R L)) ∧
      Tendsto (fun n : ℕ => eLpNorm (moserFunction c R ((n : ℝ) + 1)) ⊤
        (volume.restrict (Ω : Set (Space d)))) atTop (𝓝 ⊤) ∧
      (∀ α : ℝ, sharpCoefficient d < α →
        Tendsto (fun n : ℕ => exponentialIntegral Ω α (moserFunction c R ((n : ℝ) + 1)))
          atTop (𝓝 ⊤))

/-- The same concentrating family works simultaneously for every finite r and
all supercritical α. The continuous representatives are the source profiles. -/
def Concentration : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d),
    letI : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
    ∀ (Ω : Opens (Space d)),
      (Ω : Set (Space d)).Nonempty → Bornology.IsBounded (Ω : Set (Space d)) →
      ∃ (c : Space d) (R : ℝ) (u : ℕ → SobolevZero ℝ Ω 1 (d : ℝ≥0∞)),
        0 < R ∧ Metric.closedBall c R ⊆ (Ω : Set (Space d)) ∧
        (∀ n : ℕ, Continuous (moserFunction c R ((n : ℝ) + 1)) ∧
          (sobolevUnderlying (u n).val : Space d → ℝ) =ᵐ[volume.restrict (Ω : Set (Space d))]
            moserFunction c R ((n : ℝ) + 1) ∧
          eLpNorm (weakGradient (u n).val) (d : ℝ≥0∞)
            (volume.restrict (Ω : Set (Space d))) = 1) ∧
        (∀ r : ℝ≥0∞, 0 < r → r < ⊤ → ∃ B : ℝ≥0∞, B < ⊤ ∧
          ∀ n, MemLp (sobolevUnderlying (u n).val) r (volume.restrict (Ω : Set (Space d))) ∧
            eLpNorm (sobolevUnderlying (u n).val) r (volume.restrict (Ω : Set (Space d))) ≤ B) ∧
        Tendsto (fun n => eLpNorm (sobolevUnderlying (u n).val) ⊤
          (volume.restrict (Ω : Set (Space d)))) atTop (𝓝 ⊤) ∧
        (∀ α : ℝ, sharpCoefficient d < α →
          Tendsto (fun n => exponentialIntegral Ω α (sobolevUnderlying (u n).val))
            atTop (𝓝 ⊤))

/-- No whole-space critical endpoint estimate, even with the sum of the gradient
and a finite Lʳ norm on the right. This excludes the claimed critical GN endpoint. -/
def EndpointFailure : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d),
    letI : Fact (1 ≤ (d : ℝ≥0∞)) := ⟨by exact_mod_cast (by omega : 1 ≤ d)⟩
    ∀ r : ℝ≥0∞, 1 ≤ r → r < ⊤ →
      ¬ ∃ C : ℝ≥0, ∀ u : Sobolev (d := d) ℝ ⊤ 1 (d : ℝ≥0∞),
        MemLp (sobolevUnderlying u) r volume →
        eLpNorm (sobolevUnderlying u) ⊤ volume ≤
          C * (eLpNorm (weakGradient u) (d : ℝ≥0∞) volume +
            eLpNorm (sobolevUnderlying u) r volume)

end TrudingerMoserExpected
end P102.Sobolev
