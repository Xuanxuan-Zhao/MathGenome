import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.DistributionCalculus
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.SmoothApproximateIdentities

/-! Distribution convolution with a test, paper.tex:17326–17368.
The ambient open set is all of ℝ^d, the dual is scalar-linear, and all
natural dimensions and both manuscript scalar fields are retained. -/
set_option autoImplicit false
noncomputable section
open Set TopologicalSpace Filter MeasureTheory
open scoped Topology ContDiff Distributions

namespace ExpandedFA.Distributions

/-- The test y ↦ φ(x-y) on the whole Euclidean space. -/
def reflectedTranslate {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (x : Domain d) :
    Tests 𝕜 (⊤ : Opens (Domain d)) where
  toFun y := φ (x - y)
  contDiff' := φ.contDiff.comp (contDiff_const.sub contDiff_id)
  hasCompactSupport' := φ.hasCompactSupport.comp_isClosedEmbedding
    (Homeomorph.subLeft x).isClosedEmbedding
  tsupport_subset' := subset_univ _

/-- The scaled real mollifier regarded as a scalar-valued test. The value
at zero scale is irrelevant to the right-hand limit and is set to zero. -/
def scaledMollifierTest {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (ρ : Domain d → ℝ) (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    (ε : ℝ) : Tests 𝕜 (⊤ : Opens (Domain d)) :=
  if hε : ε = 0 then 0 else
  { toFun := fun x => (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε x : 𝕜)
    contDiff' := (RCLike.ofRealCLM : ℝ →L[ℝ] 𝕜).contDiff.comp
      (contDiff_const.mul (hρ.1.comp (contDiff_id.const_smul ε⁻¹)))
    hasCompactSupport' := by
      have hs : HasCompactSupport (SmoothApproximateIdentitiesSpec.ScaledKernelValue ρ ε) :=
        (hρ.2.1.comp_isClosedEmbedding
          (Homeomorph.smul (Units.mk0 ε⁻¹ (inv_ne_zero hε))).isClosedEmbedding).mul_left
      exact hs.comp_left (by simp)
    tsupport_subset' := subset_univ _ }

end ExpandedFA.Distributions

namespace Specs.ExpandedFA.Distributions.DistributionRegularization
open _root_.ExpandedFA.Distributions

def convolutionType := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ},
  ScalarDistribution 𝕜 (⊤ : Opens (Domain d)) →
  Tests 𝕜 (⊤ : Opens (Domain d)) → Domain d → 𝕜

def convolutionValue : convolutionType := fun u φ x => u (reflectedTranslate φ x)

def smoothType : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))),
  ContDiff ℝ ∞ (convolutionValue u φ)

/-- All finite coordinate words; in particular the canonical word for each
multi-index gives precisely the source's derivative identity. -/
def derivativesType : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (w : List (Fin d)),
  partialFunction w (convolutionValue u φ) =
    convolutionValue (DistributionCalculus.derivativeValue 𝕜 d ⊤ w u) φ ∧
  convolutionValue (DistributionCalculus.derivativeValue 𝕜 d ⊤ w u) φ =
    convolutionValue u (testPartialCLM w φ)

/-- Weak convergence is the ordinary scalar-linear test pairing of the actual
smooth function with Lebesgue measure. No weak convergence is assumed. -/
def approximationType : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (ρ : Domain d → ℝ) (hρ : SmoothApproximateIdentitiesSpec.IsMollifier ρ)
    (ψ : Tests 𝕜 (⊤ : Opens (Domain d))),
  Tendsto (fun ε => ∫ x, convolutionValue u (scaledMollifierTest ρ hρ ε) x * ψ x)
    (𝓝[>] (0 : ℝ)) (𝓝 (u ψ))

/-- The separately useful transfer identity, the second equality of derivativesType. -/
def derivativeTransferType : Prop := ∀ {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain d)))
    (φ : Tests 𝕜 (⊤ : Opens (Domain d))) (w : List (Fin d)),
  convolutionValue (DistributionCalculus.derivativeValue 𝕜 d ⊤ w u) φ =
    convolutionValue u (testPartialCLM w φ)

end Specs.ExpandedFA.Distributions.DistributionRegularization
