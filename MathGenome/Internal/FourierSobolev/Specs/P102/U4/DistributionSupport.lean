import MathGenome.Internal.FourierSobolev.Specs.P102.U4.DistributionOperations

/-! Relative distribution support, paper.tex:1329–1336.
All tests are ambient zero extensions; all support conclusions are relative to Ω.
The statements also cover empty open sets and dimension zero. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff Distributions Topology
namespace P102.U4

/-- Annihilation of every test whose closed support lies in the given set. -/
def VanishesOn {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (T : DistributionSpace 𝕜 Ω) (U : Set (Space d)) : Prop :=
  ∀ φ : TestSpace 𝕜 Ω, tsupport φ ⊆ U → T φ = 0

/-- Union of the relatively open regions of vanishing, as an ambient open set. -/
def vanishingRegion {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (T : DistributionSpace 𝕜 Ω) : Set (Space d) :=
  ⋃₀ {U : Set (Space d) | IsOpen U ∧ U ⊆ Ω ∧ VanishesOn T U}

/-- Support within the open domain, excluding ambient boundary points. -/
def relativeSupport {d : ℕ} {𝕜 : Type} [RCLike 𝕜] {Ω : Opens (Space d)}
    (T : DistributionSpace 𝕜 Ω) : Set (Space d) :=
  (Ω : Set (Space d)) \ vanishingRegion T

namespace SupportExpected

def SupportType := {d : ℕ} → {𝕜 : Type} → [RCLike 𝕜] → {Ω : Opens (Space d)} →
  DistributionSpace 𝕜 Ω → Set (Space d)
def SupportValue : SupportType := @relativeSupport

def LargestVanishing : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (T : DistributionSpace 𝕜 Ω),
    IsOpen (vanishingRegion T) ∧ vanishingRegion T ⊆ Ω ∧
    VanishesOn T (vanishingRegion T) ∧
    ∀ U : Set (Space d), IsOpen U → U ⊆ Ω → VanishesOn T U → U ⊆ vanishingRegion T

def RelativelyClosed : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (T : DistributionSpace 𝕜 Ω),
    IsClosed ((Subtype.val : Ω → Space d) ⁻¹' relativeSupport T)

def Locality : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (T : DistributionSpace 𝕜 Ω)
    (φ ψ : TestSpace 𝕜 Ω) (U : Set (Space d)), IsOpen U →
      relativeSupport T ⊆ U → EqOn φ ψ U → T φ = T ψ

def CutoffPairing : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)) (T : DistributionSpace 𝕜 Ω)
    (a : SmoothCoefficient 𝕜 Ω) (φ : TestSpace 𝕜 Ω) (U : Set (Space d)),
    IsOpen U → relativeSupport T ⊆ U → (∀ x ∈ U, a.val x = 1) →
      T (coefficientTestProduct a φ) = T φ

def MultiplierSupport : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (M : TestMultiplierFamily 𝕜 Ω), HasMultiplierGraph M →
    ∀ (a : SmoothCoefficient 𝕜 Ω) (T : DistributionSpace 𝕜 Ω),
      relativeSupport (transposeMultiplier M a T) ⊆
        ((Ω : Set (Space d)) ∩ tsupport a.val) ∩ relativeSupport T

def DerivativeSupport : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (α : MultiIndex d) (T : DistributionSpace 𝕜 Ω),
    relativeSupport (distributionPartial α T) ⊆ relativeSupport T

def RestrictionSupport : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (V Ω : Opens (Space d)) (h : V ≤ Ω)
    (T : DistributionSpace 𝕜 Ω),
    relativeSupport (restrictDistribution h T) = (V : Set (Space d)) ∩ relativeSupport T

/-- The complete operations part of Proposition AN-11-C02-R03 is retained. -/
def Operations : Prop :=
  OperationsExpected.MultiplicationOperations ∧ OperationsExpected.RestrictionOperations ∧
    OperationsExpected.RestrictionTransitive

end SupportExpected
end P102.U4
