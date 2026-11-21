import MathGenome.Internal.FourierSobolev.Specs.P102.U4.SobolevSpace
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DistributionConvolution
import MathGenome.Internal.FourierSobolev.Specs.P102.U2.ApproximateIdentities

/-! Whole-space clause of paper.tex, AN-11-C04-R03 (1429–1434).
The Sobolev norm is the existing L¹ norm of the finite derivative tuple.
The dimension and derivative order may be zero; no claim at p = infinity.
The cutoff and mollification statements specify the analytic constructions,
independently of the final sequential density statement. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions ENNReal Topology
namespace P102.U4

/-- A smooth function represents the entire weak-derivative tuple, including zero. -/
def RepresentsSobolev {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (f : Space d → 𝕜) (u : Sobolev 𝕜 (⊤ : Opens (Space d)) m p) : Prop :=
  ∀ α : SobolevIndex d m,
    (sobolevDerivative u α : Space d → 𝕜) =ᵐ[volume] multiPartial f α.val

/-- The exact sum of the errors in all derivative coordinates. -/
def sobolevSumError {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (u v : Sobolev 𝕜 (⊤ : Opens (Space d)) m p) : ℝ :=
  ∑ α : SobolevIndex d m, ‖sobolevDerivative u α - sobolevDerivative v α‖

/-- Smooth compact kernels normalized as an approximate identity and supported
in the ball of radius ε. No existence certificate is assumed by the density target. -/
def IsSobolevMollifier {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : ℝ → WholeTests d 𝕜) : Prop :=
  P102.U2.ApproximateIdentitiesExpected.Conditions volume (fun ε => (ρ ε : Space d → 𝕜)) ∧
    ∀ ε > 0, tsupport (ρ ε) ⊆ Metric.closedBall 0 ε

namespace WholeSpaceDensityExpected

def SmoothTests : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (φ : WholeTests d 𝕜),
    ∃ u : Sobolev 𝕜 (⊤ : Opens (Space d)) m p, RepresentsSobolev φ u

/-- Commutation is pointwise for the smooth representatives; it requires no
compact support of u. It therefore includes every compactly supported u. -/
def WeakMollification : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)]
    (u : Sobolev 𝕜 (⊤ : Opens (Space d)) m p) (ρ : WholeTests d 𝕜)
    (α : SobolevIndex d m),
    multiPartial (localConvolution (regularDistribution ⊤ (sobolevUnderlying u)) ρ) α.val =
      localConvolution (regularDistribution ⊤ (sobolevDerivative u α)) ρ

def MollifierExistence : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜], ∃ ρ : ℝ → WholeTests d 𝕜, IsSobolevMollifier ρ

/-- The precise cutoff used in the source: dilation of a fixed smooth cutoff.
The conclusion asserts membership and convergence, rather than assuming either. -/
def Cutoff : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ⊤ → ∀ (χ : WholeTests d ℝ),
    (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
    (∀ x ∈ Metric.closedBall (0 : Space d) 1, χ x = 1) →
    ∀ u : Sobolev 𝕜 (⊤ : Opens (Space d)) m p,
    ∃ v : ℕ → Sobolev 𝕜 (⊤ : Opens (Space d)) m p,
      (∀ n, (sobolevUnderlying (v n) : Space d → 𝕜) =ᵐ[volume]
        fun x => (χ (((n + 1 : ℕ) : ℝ)⁻¹ • x) : 𝕜) * sobolevUnderlying u x) ∧
      (∀ n, HasCompactEssentialSupport (sobolevUnderlying (v n))) ∧
      Tendsto (fun n => sobolevSumError (v n) u) atTop (𝓝 0)

/-- Every weak derivative of the compactly supported input is approximated in
Lp; the output is genuinely smooth and compactly supported. -/
def Mollification : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ⊤ → ∀ (ρ : ℝ → WholeTests d 𝕜), IsSobolevMollifier ρ →
    ∀ u : Sobolev 𝕜 (⊤ : Opens (Space d)) m p,
    HasCompactEssentialSupport (sobolevUnderlying u) →
    ∃ v : ℝ → Sobolev 𝕜 (⊤ : Opens (Space d)) m p,
      (∀ ε > 0,
        ContDiff ℝ (⊤ : ℕ∞)
          (localConvolution (regularDistribution ⊤ (sobolevUnderlying u)) (ρ ε)) ∧
        HasCompactSupport
          (localConvolution (regularDistribution ⊤ (sobolevUnderlying u)) (ρ ε)) ∧
        RepresentsSobolev
          (localConvolution (regularDistribution ⊤ (sobolevUnderlying u)) (ρ ε)) (v ε) ∧
        ∀ α : SobolevIndex d m,
          (sobolevDerivative (v ε) α : Space d → 𝕜) =ᵐ[volume]
            localConvolution (regularDistribution ⊤ (sobolevDerivative u α)) (ρ ε)) ∧
      (∀ α : SobolevIndex d m,
        Tendsto (fun ε => ‖sobolevDerivative (v ε) α - sobolevDerivative u α‖)
          (𝓝[>] 0) (𝓝 0)) ∧
      Tendsto (fun ε => sobolevSumError (v ε) u) (𝓝[>] 0) (𝓝 0)

/-- Sequential density in the exact sum norm, with all derivative representatives
specified. There is no compact-support hypothesis on the input. -/
def Density : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (m : ℕ) (p : ℝ≥0∞) [Fact (1 ≤ p)],
    p ≠ ⊤ → ∀ u : Sobolev 𝕜 (⊤ : Opens (Space d)) m p,
    ∃ (φ : ℕ → WholeTests d 𝕜) (v : ℕ → Sobolev 𝕜 (⊤ : Opens (Space d)) m p),
      (∀ n, RepresentsSobolev (φ n) (v n)) ∧
      Tendsto v atTop (𝓝 u) ∧
      Tendsto (fun n => sobolevSumError (v n) u) atTop (𝓝 0)

end WholeSpaceDensityExpected
end P102.U4
