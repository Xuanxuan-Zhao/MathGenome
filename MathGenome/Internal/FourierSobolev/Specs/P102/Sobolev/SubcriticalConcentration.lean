import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.ConcentrationScaling
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! The subcritical concentration example of paper.tex:1929–1937, with the
Lebesgue, representative, and Euclidean-gradient conventions of 47–61 and
1708–1712. No boundedness or boundary regularity is imposed on the local
example. The existential common family includes the full Sobolev norm bound,
actual smooth representatives, canonical Sobolev classes, and a fixed positive
Euclidean weak-gradient norm. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff ENNReal NNReal Topology
namespace P102.Sobolev.EndpointNoncompactness
open P102.U4

/-- Failure of convergence measured directly on representatives. -/
def NoLpSubsequence {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (F : ℕ → Space d → 𝕜) (Ω : Opens (Space d)) (q : ℝ≥0∞) : Prop :=
  ∀ σ : ℕ → ℕ, StrictMono σ →
    ¬ ∃ g : Space d → 𝕜, MemLp g q (volume.restrict (Ω : Set (Space d))) ∧
      Tendsto (fun n => eLpNorm (F (σ n) - g) q
        (volume.restrict (Ω : Set (Space d)))) atTop (𝓝 0)

/-- The target sequence consists of actual Lq classes of the displayed smooth
representatives, has the asserted norm, and has no norm-convergent subsequence. -/
def LpSequenceNoncompact {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (F : ℕ → Space d → 𝕜) (Ω : Opens (Space d)) (q : ℝ≥0∞) (c : ℝ) : Prop :=
  ∃ hq : 1 ≤ q, letI : Fact (1 ≤ q) := ⟨hq⟩
    ∃ V : ℕ → Lp 𝕜 q (volume.restrict (Ω : Set (Space d))),
      (∀ n, (V n : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))] F n) ∧
      (∀ n, ‖V n‖ = c) ∧
      ∀ σ : ℕ → ℕ, StrictMono σ →
        ∀ g : Lp 𝕜 q (volume.restrict (Ω : Set (Space d))),
          ¬ Tendsto (fun n => V (σ n)) atTop (𝓝 g)

/-- Exact critical norm, a.e. limit for all positive scales, and an explicit
bounded Sobolev sequence whose Lp* classes have no convergent subsequence. -/
def SubcriticalResult {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] : Prop :=
  ∃ D : ConcentrationFamily 𝕜 Ω p,
    let f := rescale D.bump D.center (1 - (d : ℝ) / p)
    ∃ c : ℝ, 0 < c ∧
      (∀ r, 0 < r → r < D.radius →
        MemLp (f r) (criticalExponent d p) (volume.restrict (Ω : Set (Space d))) ∧
        eLpNorm (f r) (criticalExponent d p) (volume.restrict (Ω : Set (Space d))) =
          ENNReal.ofReal c) ∧
      (∀ᵐ x ∂volume.restrict (Ω : Set (Space d)),
        Tendsto (fun r => f r x) (𝓝[>] 0) (𝓝 0)) ∧
      NoLpSubsequence (fun n => f (scales D.radius n)) Ω (criticalExponent d p) ∧
      LpSequenceNoncompact (fun n => f (scales D.radius n)) Ω (criticalExponent d p) c

namespace SubcriticalExpected

def OpenSet : Prop :=
  ∀ (d : ℕ) (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d)),
    (Ω : Set (Space d)).Nonempty → ∀ (p : ℝ≥0), 1 ≤ p → p < d →
    ∀ [Fact (1 ≤ (p : ℝ≥0∞))], SubcriticalResult 𝕜 Ω p

def Lipschitz : Prop :=
  ∀ (m : ℕ) (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
      (Ω : Opens (Space (m + 1))),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) →
    (Ω : Set (Space (m + 1))).Nonempty →
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0), 1 ≤ p → p < (m + 1 : ℕ) →
    ∀ [Fact (1 ≤ (p : ℝ≥0∞))], SubcriticalResult 𝕜 Ω p

/-- The bridge uses the norm topology of the actual quotient Lq space.
No finite-measure hypothesis is needed. -/
def LpBridge : Prop :=
  ∀ {α E : Type} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (F : ℕ → α → E) (V : ℕ → Lp E q μ),
    (∀ n, (V n : α → E) =ᵐ[μ] F n) →
    ∀ g : Lp E q μ,
      Tendsto V atTop (𝓝 g) ↔
        Tendsto (fun n => eLpNorm (F n - (g : α → E)) q μ) atTop (𝓝 0)

end SubcriticalExpected
end P102.Sobolev.EndpointNoncompactness
