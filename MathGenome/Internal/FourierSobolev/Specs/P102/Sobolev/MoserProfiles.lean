import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.TrudingerMoserBound
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Explicit profiles in paper.tex:2229–2250, with Lebesgue measure and arbitrary
interior centers. These definitions do not assert Sobolev membership. -/
universe u

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace P102.Sobolev
open P102.U4
namespace TrudingerMoser

/-- Extended exponential integral, so a supremum equal to infinity is literal. -/
def exponentialIntegral {d : ℕ} {𝕜 : Type u} [NormedAddCommGroup 𝕜]
    (Ω : Opens (Space d)) (α : ℝ) (f : Space d → 𝕜) : ℝ≥0∞ :=
  ∫⁻ x in (Ω : Set (Space d)),
    ENNReal.ofReal (Real.exp (α * ‖f x‖ ^ criticalPower d))

/-- Height of the plateau at logarithmic time L. -/
def moserHeight (d : ℕ) (L : ℝ) : ℝ :=
  (L / sharpCoefficient d) ^ (1 / criticalPower d)

/-- The source's truncated logarithmic profile, including its value at the
center. The parameters used in the theorem satisfy d ≥ 2, R > 0, L > 0. -/
def moserFunction {d : ℕ} (c : Space d) (R L : ℝ) (x : Space d) : ℝ :=
  moserHeight d L *
    (if x = c then 1 else
      min 1 (max 0 ((d : ℝ) * Real.log (R / ‖x - c‖) / L)))

end TrudingerMoser
namespace MoserProfilesExpected
open TrudingerMoser

def exponentialIntegral_type : Type (u + 1) :=
  {d : ℕ} → {𝕜 : Type u} → [NormedAddCommGroup 𝕜] →
    Opens (Space d) → ℝ → (Space d → 𝕜) → ℝ≥0∞
def exponentialIntegral_value : exponentialIntegral_type :=
  fun {d} {_} [_] Ω α f => ∫⁻ x in (Ω : Set (Space d)),
    ENNReal.ofReal (Real.exp (α * ‖f x‖ ^ criticalPower d))

def moserHeight_type : Type := ℕ → ℝ → ℝ
def moserHeight_value : moserHeight_type :=
  fun d L => (L / sharpCoefficient d) ^ (1 / criticalPower d)

def moserFunction_type : Type := {d : ℕ} → Space d → ℝ → ℝ → Space d → ℝ
def moserFunction_value : moserFunction_type :=
  fun {d} c R L x => moserHeight d L *
    (if x = c then 1 else min 1 (max 0 ((d : ℝ) * Real.log (R / ‖x - c‖) / L)))

def ProfileDivergence : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Ω : Opens (Space d)) (c : Space d) (R : ℝ),
    0 < R → Metric.closedBall c R ⊆ (Ω : Set (Space d)) →
      (∀ L : ℝ, 0 < L → Continuous (moserFunction c R L)) ∧
      Tendsto (fun n : ℕ => eLpNorm (moserFunction c R ((n : ℝ) + 1)) ⊤
        (volume.restrict (Ω : Set (Space d)))) atTop (𝓝 ⊤) ∧
      (∀ α : ℝ, sharpCoefficient d < α →
        Tendsto (fun n : ℕ => exponentialIntegral Ω α (moserFunction c R ((n : ℝ) + 1)))
          atTop (𝓝 ⊤))

end MoserProfilesExpected
end P102.Sobolev
