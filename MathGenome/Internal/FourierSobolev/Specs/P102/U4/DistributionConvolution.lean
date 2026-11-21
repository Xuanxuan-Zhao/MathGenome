import MathGenome.Internal.FourierSobolev.Specs.P102.U4.CompactSupportExtension
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.LocalConvolution
import Mathlib.Topology.Algebra.Group.Pointwise

/-! Independent scope of paper.tex:1392–1410 (U4-04), apart from the
separately allocated symmetry theorem. Pairings are bilinear over either scalar
field. Compact support is required of S only in the defining pairing.
The locally integrable compatibility assertion covers either compact factor. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff Distributions Pointwise
namespace P102.U4

/-- The actual whole-space test occurring in the inner pairing. -/
def additionTest {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (φ : WholeTests d 𝕜) (x : Space d) : WholeTests d 𝕜 where
  toFun y := φ (x + y)
  contDiff' := φ.contDiff.comp (contDiff_const.add contDiff_id)
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph (Homeomorph.addLeft x)
  tsupport_subset' := subset_univ _

/-- Before proving compact support in x, the inner pairing is a scalar function. -/
def convolutionInner {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (φ : WholeTests d 𝕜)
    (x : Space d) : 𝕜 := S (additionTest φ x)

/-- Compact essential support does not depend on pointwise values on null sets. -/
def HasCompactEssentialSupport {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f : Space d → 𝕜) : Prop :=
  ∃ K : Compacts (Space d), ∀ᵐ x ∂volume, x ∉ K → f x = 0

/-- The manuscript's ordinary integral convention, evaluated where integrable. -/
def functionConvolution {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (f g : Space d → 𝕜) (x : Space d) : 𝕜 := ∫ y, f (x - y) * g y

namespace DistributionConvolutionExpected

def AdditionTestType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  WholeTests d 𝕜 → Space d → WholeTests d 𝕜
def AdditionTestValue : AdditionTestType := @additionTest

def InnerType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] →
  DistributionSpace 𝕜 (⊤ : Opens (Space d)) → WholeTests d 𝕜 → Space d → 𝕜
def InnerValue : InnerType := @convolutionInner

def InnerTest : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))), IsCompact (relativeSupport S) →
    ∀ φ : WholeTests d 𝕜,
      ContDiff ℝ (⊤ : ℕ∞) (convolutionInner S φ) ∧
      tsupport (convolutionInner S φ) ⊆ tsupport φ - relativeSupport S ∧
      HasCompactSupport (convolutionInner S φ)

/-- Equality with the canonical smooth extension, independently of its cutoff. -/
def ExtensionPairing : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
    (E : SmoothFunctions 𝕜 (⊤ : Opens (Space d)) →L[𝕜] 𝕜),
    (∀ ψ : WholeTests d 𝕜, E (testToSmooth 𝕜 ψ) = S ψ) →
    ∀ (φ : WholeTests d 𝕜) (x : Space d),
      convolutionInner S φ x = E (testToSmooth 𝕜 (additionTest φ x))

/-- A canonical continuous map on tests, including the defining formula. -/
def InnerOperator : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜]
    (S : DistributionSpace 𝕜 (⊤ : Opens (Space d))), IsCompact (relativeSupport S) →
    ∃ H : WholeTests d 𝕜 →L[𝕜] WholeTests d 𝕜,
      ∀ φ x, H φ x = convolutionInner S φ x

/-- Construction, support and both derivative identities on the full class of
pairs with at least one compact support. No symmetry conclusion is assumed. -/
def Construction : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜],
    ∃ C : (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) →
        (IsCompact (relativeSupport T) ∨ IsCompact (relativeSupport S)) →
        DistributionSpace 𝕜 (⊤ : Opens (Space d)),
      (∀ T S hS φ,
        ∃ ψ : WholeTests d 𝕜, (∀ x, ψ x = convolutionInner S φ x) ∧
          C T S (Or.inr hS) φ = T ψ) ∧
      (∀ T S h, relativeSupport (C T S h) ⊆ relativeSupport T + relativeSupport S) ∧
      (∀ (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
          (hS : IsCompact (relativeSupport S)) (α : MultiIndex d),
        (∃ hα : IsCompact (relativeSupport (distributionPartial α S)),
          distributionPartial α (C T S (Or.inr hS)) =
            C T (distributionPartial α S) (Or.inr hα)) ∧
        distributionPartial α (C T S (Or.inr hS)) =
          C (distributionPartial α T) S (Or.inr hS))

/-- The ordinary integral formula for the inner pairing of any locally
integrable representative. -/
def RegularInner : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (g : Space d → 𝕜),
    LocallyIntegrable g volume → ∀ (φ : WholeTests d 𝕜) (x : Space d),
      convolutionInner (regularDistribution ⊤ g) φ x = ∫ y, g y * φ (x + y)

/-- Complete remaining conclusion, including the construction on either compact
factor. The right-compact pairing fixes the orientation. Symmetry is not assumed.
For the differentiated compact factor hα is supplied explicitly; its existence
is included, so no support/compactness hypothesis is strengthened. -/
def Convolution : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜],
    ∃ C : (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d))) →
        (IsCompact (relativeSupport T) ∨ IsCompact (relativeSupport S)) →
        DistributionSpace 𝕜 (⊤ : Opens (Space d)),
      (∀ T S hS φ,
        ∃ ψ : WholeTests d 𝕜, (∀ x, ψ x = convolutionInner S φ x) ∧
          C T S (Or.inr hS) φ = T ψ) ∧
      (∀ T S h, relativeSupport (C T S h) ⊆ relativeSupport T + relativeSupport S) ∧
      (∀ (T S : DistributionSpace 𝕜 (⊤ : Opens (Space d)))
          (hS : IsCompact (relativeSupport S)) (α : MultiIndex d),
        (∃ hα : IsCompact (relativeSupport (distributionPartial α S)),
          distributionPartial α (C T S (Or.inr hS)) =
            C T (distributionPartial α S) (Or.inr hα)) ∧
        distributionPartial α (C T S (Or.inr hS)) =
          C (distributionPartial α T) S (Or.inr hS)) ∧
      (∀ (T : DistributionSpace 𝕜 (⊤ : Opens (Space d))) (ρ : WholeTests d 𝕜),
        ∃ hρ : IsCompact (relativeSupport (regularDistribution ⊤ ρ)),
          C T (regularDistribution ⊤ ρ) (Or.inr hρ) =
            regularDistribution ⊤ (localConvolution T ρ)) ∧
      (∀ (f g : Space d → 𝕜),
        LocallyIntegrable f volume → LocallyIntegrable g volume →
        (HasCompactEssentialSupport f ∨ HasCompactEssentialSupport g) →
        (∀ᵐ x ∂volume, Integrable (fun y => f (x - y) * g y) volume) ∧
        LocallyIntegrable (functionConvolution f g) volume ∧
        ∃ h : IsCompact (relativeSupport (regularDistribution ⊤ f)) ∨
              IsCompact (relativeSupport (regularDistribution ⊤ g)),
          C (regularDistribution ⊤ f) (regularDistribution ⊤ g) h =
            regularDistribution ⊤ (functionConvolution f g))

end DistributionConvolutionExpected
end P102.U4
