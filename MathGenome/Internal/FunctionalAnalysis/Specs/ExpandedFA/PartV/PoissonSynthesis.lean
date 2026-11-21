import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.PositiveHarmonic
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.AbsoluteSynthesis
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.ScalarLpDuality
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-! Independent statements for `fa2:p5:poisson-synthesis`, paper.tex:23535–23559.
The circle measure and real Poisson kernel are the accepted normalized objects.
Both real and complex scalar data are included. Boundary density explicitly
requires a subsequence in a fixed cone at almost every point. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal lp

namespace ExpandedFA.PartV.PoissonSynthesis
open PartIV.PositiveHarmonic

instance circleHaar_isFinite : IsFiniteMeasure circleHaar :=
  inferInstanceAs (IsFiniteMeasure (Measure.haarMeasure ⊤))

/-- A fixed aperture region with vertex on the unit circle. -/
def stolzRegion (ζ : Circle) (M : ℝ) : Set ℂ :=
  {z | z ∈ unitDisk ∧ ‖z - (ζ : ℂ)‖ ≤ M * (1 - ‖z‖)}

/-- The source's density hypothesis, with aperture allowed to depend on ζ. -/
def NontangentiallyDense (z : ℕ → ℂ) : Prop :=
  ∀ᵐ (ζ : Circle) ∂circleHaar, ∃ M : ℝ, 0 < M ∧ ∃ k : ℕ → ℕ,
    StrictMono k ∧ Tendsto (fun j => z (k j)) atTop (𝓝 (ζ : ℂ)) ∧
      ∀ j, z (k j) ∈ stolzRegion ζ M

/-- Mean oscillation on shrinking closed circle balls (chord distance). -/
def IsLebesguePoint {𝕜 : Type*} [RCLike 𝕜] (g : Circle → 𝕜) (ζ : Circle) : Prop :=
  Tendsto (fun r : ℝ =>
    (∫ η in Metric.closedBall ζ r, ‖g η - g ζ‖ ∂circleHaar) /
      circleHaar.real (Metric.closedBall ζ r)) (𝓝[>] 0) (𝓝 0)

/-- The scalar-linear Poisson test; no conjugation is inserted. -/
def poissonTest {𝕜 : Type*} [RCLike 𝕜] (g : Circle → 𝕜) (z : ℂ) : 𝕜 :=
  ∫ ζ, (circlePoissonKernel z ζ : 𝕜) * g ζ ∂circleHaar

/-- The same Poisson kernel as a scalar continuous function on the circle. -/
def kernelContinuous {𝕜 : Type*} [RCLike 𝕜] (z : ℂ) (hz : z ∈ unitDisk) :
    C(Circle, 𝕜) where
  toFun ζ := (circlePoissonKernel z ζ : 𝕜)
  continuous_toFun := by
    apply RCLike.continuous_ofReal.comp
    apply continuous_const.div (by fun_prop)
    intro ζ
    apply pow_ne_zero
    apply norm_ne_zero_iff.mpr
    intro h
    have heq : z = (ζ : ℂ) := (sub_eq_zero.mp h).symm
    have hlt : ‖z‖ < 1 := hz
    simp [heq] at hlt

/-- The native L¹ class of P_z. Its witness only requires z to lie in the disk. -/
def poissonAtom {𝕜 : Type*} [RCLike 𝕜] (z : ℂ) (hz : z ∈ unitDisk) :
    Lp 𝕜 1 circleHaar :=
  ContinuousMap.toLp (𝕜 := 𝕜) 1 circleHaar (kernelContinuous z hz)

namespace Spec

/-- Pointwise convergence along every fixed Stolz region at a Lebesgue point. -/
def BoundaryConvergence : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (g : Circle → 𝕜), MemLp g ∞ circleHaar →
    ∀ ζ : Circle, IsLebesguePoint g ζ → ∀ M : ℝ, 0 < M →
      Tendsto (poissonTest g) (𝓝[stolzRegion ζ M] (ζ : ℂ)) (𝓝 (g ζ))

/-- Scalar Lebesgue differentiation for the same circle balls and measure. -/
def AeLebesguePoints : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (g : Circle → 𝕜), MemLp g ∞ circleHaar →
    ∀ᵐ (ζ : Circle) ∂circleHaar, IsLebesguePoint g ζ

/-- The dyadic-annulus envelope in the source, in chord distance. -/
def StolzKernelBound : Prop :=
  ∀ {ζ : Circle} {M : ℝ}, 0 < M → ∀ {z : ℂ}, z ∈ stolzRegion ζ M →
    ∀ η : Circle, circlePoissonKernel z η ≤
      2 * (1 + (M + 1) ^ 2) * (1 - ‖z‖) /
        ((1 - ‖z‖) ^ 2 + ‖(η : ℂ) - (ζ : ℂ)‖ ^ 2)

/-- A useful cap estimate for the circle metric and this normalization. -/
def CapMassBound : Prop :=
  ∀ ζ : Circle, ∀ {r : ℝ}, 0 < r →
    circleHaar.real (Metric.closedBall ζ r) ≤ 4 * r

/-- The accepted normalization gives native scalar L¹ norm exactly one. -/
def KernelNorm : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (z : ℂ) (hz : z ∈ unitDisk),
    ‖poissonAtom (𝕜 := 𝕜) z hz‖ = 1

/-- Both directions of the exact L∞ norming equality. -/
def ExactNorming : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (z : ℕ → ℂ), (∀ n, z n ∈ unitDisk) →
    NontangentiallyDense z → ∀ g : Lp 𝕜 ∞ circleHaar,
      (⨆ n : ℕ, ‖poissonTest (g : Circle → 𝕜) (z n)‖) = ‖g‖

/-- The continuous scalar-linear dual is normed by the native Poisson atoms. -/
def DualNorming : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (z : ℕ → ℂ) (hz : ∀ n, z n ∈ unitDisk),
    NontangentiallyDense z → ∀ L : Lp 𝕜 1 circleHaar →L[𝕜] 𝕜,
      (⨆ n : ℕ, ‖L (poissonAtom (𝕜 := 𝕜) (z n) (hz n))‖) = ‖L‖

/-- Exact absolutely norm-convergent synthesis with the strict coefficient sum. -/
def AbsolutePoissonSynthesis : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (z : ℕ → ℂ) (hz : ∀ n, z n ∈ unitDisk),
    NontangentiallyDense z → ∀ (f : Lp 𝕜 1 circleHaar) (ε : ℝ), 0 < ε →
    ∃ a : ℓ¹(ℕ, 𝕜),
      HasSum (fun n => a n • poissonAtom (𝕜 := 𝕜) (z n) (hz n)) f ∧
      Summable (fun n => ‖a n • poissonAtom (𝕜 := 𝕜) (z n) (hz n)‖) ∧
      (∑' n, ‖a n‖) < ‖f‖ + ε

/-- The functional-analytic step isolated from the harmonic boundary theorem. -/
def ExactNormingOfBoundaryConvergence : Prop :=
  BoundaryConvergence → AeLebesguePoints → ExactNorming

def DualNormingOfExactNorming : Prop := ExactNorming → DualNorming

def SynthesisOfDualNorming : Prop := DualNorming → AbsolutePoissonSynthesis

/-- Assembly of the harmonic boundary theorem and quantitative synthesis. -/
def SynthesisOfBoundaryConvergence : Prop :=
  BoundaryConvergence → AbsolutePoissonSynthesis

end Spec
end ExpandedFA.PartV.PoissonSynthesis
