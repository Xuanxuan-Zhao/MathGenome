import MathGenome.Internal.FourierSobolev.Specs.P102.U4.RegularDerivatives
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! Zero weak gradient on an arbitrary connected open set. Ambient representatives
are used, with all integrability and a.e. conclusions restricted to the open set.
`IsPreconnected` permits the empty open set. -/
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal
namespace P102.Sobolev.ZeroGradientExpected
open P102.U4

def Constant : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (u : Space d → 𝕜), IsPreconnected (Ω : Set (Space d)) →
    LocallyIntegrableOn u Ω volume →
    (∀ i : Fin d, distributionPartial {i} (regularDistribution Ω u) = 0) →
    ∃ c : 𝕜, u =ᵐ[volume.restrict Ω] fun _ => c

def UniqueConstant : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (u : Space d → 𝕜), IsConnected (Ω : Set (Space d)) →
    LocallyIntegrableOn u Ω volume →
    (∀ i : Fin d, distributionPartial {i} (regularDistribution Ω u) = 0) →
    ∃! c : 𝕜, u =ᵐ[volume.restrict Ω] fun _ => c

/-- The general locally integrable formulation also covers exponents below one. -/
def WholeSpaceZeroOfLocallyIntegrable : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜], 0 < d →
    ∀ (p : ℝ≥0∞) (u : Space d → 𝕜), p ≠ 0 → p ≠ ∞ →
    LocallyIntegrable u volume → MemLp u p volume →
    (∀ i : Fin d, distributionPartial {i}
      (regularDistribution (⊤ : Opens (Space d)) u) = 0) →
    u =ᵐ[volume] 0

def WholeSpaceZero : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜], 0 < d →
    ∀ (p : ℝ≥0∞) (u : Space d → 𝕜), 1 ≤ p → p ≠ ∞ → MemLp u p volume →
    (∀ i : Fin d, distributionPartial {i}
      (regularDistribution (⊤ : Opens (Space d)) u) = 0) →
    u =ᵐ[volume] 0

end P102.Sobolev.ZeroGradientExpected
