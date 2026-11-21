import MathGenome.Internal.FourierSobolev.Specs.P102.U4.LocalConvolution

/-! Independent statements for paper.tex:1339–1357. The kernel can be signed
or complex. The positive parameter tends to zero from the right. All tests
are the canonical ambient zero extensions; convergence takes place in one
fixed compact subset of the original open set, not merely pointwise.

The positive-dimensional assertions below are stated for every natural d;
this also allows their specialization to the singleton in u4_zero_dimension.
The arbitrary-kernel local-convolution statements are retained in full. -/

noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions Topology Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace P102.U4.Mollification

/-- The value at parameter zero is immaterial for the right-hand limit. -/
def scaledKernel {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (ε : ℝ) :
    TestSpace 𝕜 (⊤ : Opens (Space d)) := by
  classical
  exact if hε : ε = 0 then 0 else
    { toFun := fun x => (ε ^ d)⁻¹ • ρ (ε⁻¹ • x)
      contDiff' := by
        have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : Space d => ε⁻¹ • x) := by
          change ContDiff ℝ (⊤ : ℕ∞)
            ((ε⁻¹ • ContinuousLinearMap.id ℝ (Space d)) : Space d → Space d)
          exact (ε⁻¹ • ContinuousLinearMap.id ℝ (Space d)).contDiff
        simpa only [Function.comp_def, Pi.smul_apply] using
          (ContDiff.const_smul (ε ^ d)⁻¹ (ρ.contDiff.comp h))
      hasCompactSupport' := by
        let e : Space d ≃ₜ Space d := Homeomorph.smul (Units.mk0 ε⁻¹ (inv_ne_zero hε))
        have h : HasCompactSupport (fun x : Space d => ρ (ε⁻¹ • x)) :=
          ρ.hasCompactSupport.comp_homeomorph e
        exact h.smul_left (f := fun _ : Space d => (ε ^ d)⁻¹)
      tsupport_subset' := subset_univ _ }

/-- Reflection in the origin; no conjugation occurs. -/
def reflectedKernel {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) :
    TestSpace 𝕜 (⊤ : Opens (Space d)) where
  toFun x := ρ (-x)
  contDiff' := ρ.contDiff.comp contDiff_neg
  hasCompactSupport' := ρ.hasCompactSupport.comp_homeomorph (Homeomorph.neg (Space d))
  tsupport_subset' := subset_univ _

/-- This is (check ρ)*φ, in the source's convolution convention. -/
def reflectedSmoothing {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (φ : Space d → 𝕜) (y : Space d) : 𝕜 :=
  ∫ x, ρ (x - y) * φ x

namespace Expected

def ScaledKernelType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  TestSpace 𝕜 (⊤ : Opens (Space d)) → ℝ → TestSpace 𝕜 (⊤ : Opens (Space d))
def ScaledKernelValue : ScaledKernelType := @scaledKernel

def ReflectedKernelType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  TestSpace 𝕜 (⊤ : Opens (Space d)) → TestSpace 𝕜 (⊤ : Opens (Space d))
def ReflectedKernelValue : ReflectedKernelType := @reflectedKernel

def ReflectedSmoothingType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  TestSpace 𝕜 (⊤ : Opens (Space d)) → (Space d → 𝕜) → Space d → 𝕜
def ReflectedSmoothingValue : ReflectedSmoothingType := @reflectedSmoothing

def ScalingFormula : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (ε : ℝ), 0 < ε → ∀ x,
    scaledKernel ρ ε x = (ε ^ d)⁻¹ • ρ (ε⁻¹ • x)

def ScalingSupport : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (ε : ℝ), 0 < ε →
    tsupport (scaledKernel ρ ε) = ε • tsupport ρ

/-- Mass and absolute mass are both preserved. -/
def ScalingIntegrals : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (ε : ℝ), 0 < ε →
    (∫ x, scaledKernel ρ ε x) = (∫ x, ρ x) ∧
    (∫ x, ‖scaledKernel ρ ε x‖) = (∫ x, ‖ρ x‖)

def ShrinkingSupport : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))) (δ : ℝ), 0 < δ →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), tsupport (scaledKernel ρ ε) ⊆ Metric.ball 0 δ

/-- A neighborhood of every compact subset is admissible eventually. -/
def EventuallyAdmissible : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (K : Compacts (Space d)), (K : Set (Space d)) ⊆ Ω →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ V : Opens (Space d),
      (K : Set (Space d)) ⊆ V ∧ (V : Set (Space d)) ⊆ convolutionDomain Ω (scaledKernel ρ ε)

def RelativelyCompactDomain : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω V : Opens (Space d))
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))),
    IsCompact (closure (V : Set (Space d))) → closure (V : Set (Space d)) ⊆ Ω →
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), (V : Set (Space d)) ⊆ convolutionDomain Ω (scaledKernel ρ ε)

/-- The unscaled local transpose identity, including absolute existence of the
scalar integral and the actual test representing the inner integral. -/
def IntegralPairing : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (T : DistributionSpace 𝕜 Ω) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (φ : TestSpace 𝕜 Ω), tsupport φ ⊆ convolutionDomain Ω ρ →
    ∃ ψ : TestSpace 𝕜 Ω,
      (∀ y, ψ y = reflectedSmoothing ρ φ y) ∧
      Integrable (fun x => localConvolution T ρ x * φ x) ∧
      (∫ x, localConvolution T ρ x * φ x) = T ψ

/-- The common-support topology is the canonical fixed-support Fréchet topology.
The family may be set to zero away from a sufficiently small positive interval. -/
def FixedSupportApproximation : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))), (∫ x, ρ x) = 1 →
    ∀ φ : TestSpace 𝕜 Ω, ∃ (K : Compacts (Space d))
      (hK : (K : Set (Space d)) ⊆ Ω) (φK : FixedSupport d 𝕜 K)
      (ψ : ℝ → FixedSupport d 𝕜 K),
      stageInclusion 𝕜 hK φK = φ ∧
      Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 φK) ∧
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ y,
        ψ ε y = reflectedSmoothing (scaledKernel ρ ε) φ y

/-- The complete eventual identity, on a neighborhood of the test support. -/
def EventuallyPairing : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (T : DistributionSpace 𝕜 Ω) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d)))
    (φ : TestSpace 𝕜 Ω),
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ (V : Opens (Space d)) (ψ : TestSpace 𝕜 Ω),
      tsupport φ ⊆ V ∧ (V : Set (Space d)) ⊆ convolutionDomain Ω (scaledKernel ρ ε) ∧
      (∀ y, ψ y = reflectedSmoothing (scaledKernel ρ ε) φ y) ∧
      Integrable (fun x => localConvolution T (scaledKernel ρ ε) x * φ x) ∧
      (∫ x, localConvolution T (scaledKernel ρ ε) x * φ x) = T ψ

/-- Local distribution convergence on an arbitrary open set, including the empty
set and natural dimension zero. No positivity or whole-space premise is added. -/
def DistributionLimit : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (T : DistributionSpace 𝕜 Ω) (ρ : TestSpace 𝕜 (⊤ : Opens (Space d))),
    (∫ x, ρ x) = 1 → ∀ φ : TestSpace 𝕜 Ω,
    Tendsto (fun ε => ∫ x, localConvolution T (scaledKernel ρ ε) x * φ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (T φ))

def CompleteLocalConvolution : Prop :=
  LocalConvolutionExpected.OpenDomain ∧ LocalConvolutionExpected.AdmissibleTest ∧
  LocalConvolutionExpected.Pairing ∧ LocalConvolutionExpected.Smooth ∧
  LocalConvolutionExpected.KernelDerivative ∧ LocalConvolutionExpected.DerivativeDomain ∧
  LocalConvolutionExpected.Derivative ∧ LocalConvolutionExpected.RegularIntegral

end Expected
end P102.U4.Mollification
