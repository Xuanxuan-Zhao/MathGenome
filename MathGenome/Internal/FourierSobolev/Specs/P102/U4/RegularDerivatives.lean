import MathGenome.Internal.FourierSobolev.Specs.P102.U4.TestSpace

/-! Independent scope of paper.tex:1315–1326. Functions are ambient representatives;
all hypotheses and a.e. conclusions are restricted to the open set. Pairings are
scalar-bilinear, including for complex scalars. No positive-dimension or nonempty
open-set hypothesis is imposed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ContDiff Distributions
namespace P102.U4

/-- The canonical regular distribution, using multiplication without conjugation. -/
def regularDistribution {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d))
    (f : Space d → 𝕜) : DistributionSpace 𝕜 Ω :=
  TestFunction.integralAgainstBilinCLM (ContinuousLinearMap.mul 𝕜 𝕜) volume f

/-- Continuous map on tests realizing successive coordinate derivatives. -/
def testPartialWord {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) :
    List (Fin d) → TestSpace 𝕜 Ω →L[𝕜] TestSpace 𝕜 Ω
  | [] => ContinuousLinearMap.id 𝕜 _
  | i :: l => (TestFunction.lineDerivCLM 𝕜 (coordinateVector d i)).comp (testPartialWord Ω l)

/-- The coordinate multi-index derivative of a distribution, by transposition. -/
def distributionPartial {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (α : MultiIndex d) (T : DistributionSpace 𝕜 Ω) : DistributionSpace 𝕜 Ω :=
  ((-1 : 𝕜) ^ α.card) • T.comp (testPartialWord Ω (α.sort (· ≤ ·)))

namespace RegularDerivativesExpected

def RegularType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → (Ω : Opens (Space d)) →
  (Space d → 𝕜) → DistributionSpace 𝕜 Ω
def RegularValue : RegularType := @regularDistribution

def DerivativeType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {Ω : Opens (Space d)} →
  MultiIndex d → DistributionSpace 𝕜 Ω → DistributionSpace 𝕜 Ω
def DerivativeValue : DerivativeType := @distributionPartial

def Pairing : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (f : Space d → 𝕜),
    LocallyIntegrableOn f Ω volume → ∀ φ : TestSpace 𝕜 Ω,
      regularDistribution Ω f φ = ∫ x in Ω, f x * φ x

def SupportBound : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (f : Space d → 𝕜),
    LocallyIntegrableOn f Ω volume → ∀ (K : Compacts (Space d))
      (hK : (K : Set (Space d)) ⊆ Ω) (φ : FixedSupport d 𝕜 K),
      ‖regularDistribution Ω f (stageInclusion 𝕜 hK φ)‖ ≤
        coordinateSupSeminorm 𝕜 K 0 φ * ∫ x in K, ‖f x‖

def Injectivity : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (f g : Space d → 𝕜),
    LocallyIntegrableOn f Ω volume → LocallyIntegrableOn g Ω volume →
      (regularDistribution Ω f = regularDistribution Ω g ↔ f =ᵐ[volume.restrict Ω] g)

def DerivativeFormula : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (α : MultiIndex d)
    (T : DistributionSpace 𝕜 Ω) (φ : TestSpace 𝕜 Ω),
    ∃ ψ : TestSpace 𝕜 Ω, (∀ x, ψ x = multiPartial φ α x) ∧
      distributionPartial α T φ = (-1 : 𝕜) ^ α.card * T ψ

def DerivativeZero : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (T : DistributionSpace 𝕜 Ω),
    distributionPartial (0 : MultiIndex d) T = T

def DerivativeAdd : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (α β : MultiIndex d)
    (T : DistributionSpace 𝕜 Ω),
    distributionPartial (α + β) T = distributionPartial α (distributionPartial β T)

def CoordinateCommutation : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (i j : Fin d)
    (T : DistributionSpace 𝕜 Ω),
    distributionPartial {i} (distributionPartial {j} T) =
      distributionPartial {j} (distributionPartial {i} T)

/-- Exactly finite C^{|α|} regularity on Ω, with no regularity required outside Ω. -/
def ClassicalCompatibility : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (α : MultiIndex d)
    (f : Space d → 𝕜), ContDiffOn ℝ (α.card : ℕ) f Ω →
      distributionPartial α (regularDistribution Ω f) = regularDistribution Ω (multiPartial f α)

end RegularDerivativesExpected
end P102.U4
