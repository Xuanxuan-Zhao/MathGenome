import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SubcriticalConcentration
import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.HolderConcentration

/-! The concentration examples following Rellich in paper.tex:1929–1937.
The imported independent Specs supply the canonical smooth representatives,
full Sobolev norm bounds, fixed positive Euclidean gradient norms, and target
convergence notions. These statements assemble all three endpoint failures
on arbitrary nonempty open sets and specialize them to bounded Lipschitz sets.
No connectedness hypothesis is imposed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff ENNReal NNReal Topology
namespace P102.Sobolev.EndpointNoncompactness
open P102.U4

namespace Expected

def Subcritical : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)),
    (Ω : Set (Space d)).Nonempty → ∀ (p : ℝ≥0), 1 ≤ p → p < d →
    ∀ [Fact (1 ≤ (p : ℝ≥0∞))], SubcriticalResult 𝕜 Ω p

def Supercritical : Prop :=
  ∀ (d : ℕ), 0 < d → ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)),
    (Ω : Set (Space d)).Nonempty → ∀ (p : ℝ≥0), 1 ≤ p → (d : ℝ≥0) < p →
    ∀ [Fact (1 ≤ (p : ℝ≥0∞))], SupercriticalResult 𝕜 Ω p

def DimensionOne : Prop :=
  ∀ (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space 1)),
    (Ω : Set (Space 1)).Nonempty → DimensionOneResult 𝕜 Ω

def Lipschitz : Prop :=
  (∀ (m : ℕ) (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
      (Ω : Opens (Space (m + 1))),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) →
    (Ω : Set (Space (m + 1))).Nonempty →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0), 1 ≤ p →
    ∀ [Fact (1 ≤ (p : ℝ≥0∞))],
      (p < (m + 1 : ℕ) → SubcriticalResult 𝕜 Ω p) ∧
      ((m + 1 : ℕ) < p → SupercriticalResult 𝕜 Ω p)) ∧
  (∀ (e : GraphPieces.Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1)),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient 0)) →
    (Ω : Set (Space 1)).Nonempty → ∀ (𝕜 : Type) [RCLike 𝕜], DimensionOneResult 𝕜 Ω)

end Expected
end P102.Sobolev.EndpointNoncompactness
