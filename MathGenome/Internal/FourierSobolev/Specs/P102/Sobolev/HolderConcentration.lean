import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.ConcentrationScaling
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The two endpoint concentration examples in paper.tex:1929–1937.
Canonical spaces, scalar conventions and Sobolev classes are imported from
ConcentrationScaling. Domains are arbitrary nonempty open sets, with no
connectedness, boundedness or boundary assumptions. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff ENNReal NNReal Topology
namespace P102.Sobolev.EndpointNoncompactness
open P102.U4

/-- Convergence in the full Hölder norm, expressed on the actual representatives.
The first clause is convergence in supremum norm; the second is convergence
of the Hölder seminorm of the difference. -/
def HolderTendsto {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (F : ℕ → Space d → 𝕜) (g : Space d → 𝕜) (S : Set (Space d)) (a : ℝ) : Prop :=
  TendstoUniformlyOn F g atTop S ∧
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    ∀ x ∈ S, ∀ y ∈ S,
      ‖(F n x - g x) - (F n y - g y)‖ ≤ ε * ‖x - y‖ ^ a

/-- Full supercritical example. A scaled pair of distinct interior points
bounds the endpoint Hölder seminorm from below at every small scale.
The no-subsequence clause uses the full Hölder norm on the closure. -/
def SupercriticalResult {d : ℕ} (𝕜 : Type) [RCLike 𝕜]
    (Ω : Opens (Space d)) (p : ℝ≥0) [Fact (1 ≤ (p : ℝ≥0∞))] : Prop :=
  ∃ D : ConcentrationFamily 𝕜 Ω p,
    let a := 1 - (d : ℝ) / p
    let f := rescale D.bump D.center a
    (∀ r, 0 < r → r < D.radius →
      ∃ M : ℝ, IntegerEmbeddings.HolderNormBound (f r)
        (closure (Ω : Set (Space d))) a M) ∧
    TendstoUniformlyOn f 0 (𝓝[>] 0) (closure (Ω : Set (Space d))) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ r, 0 < r → r < D.radius →
      ∃ x ∈ (Ω : Set (Space d)), ∃ y ∈ (Ω : Set (Space d)),
        x ≠ y ∧ c * ‖x - y‖ ^ a ≤ ‖f r x - f r y‖) ∧
    (∀ σ : ℕ → ℕ, StrictMono σ → ¬ ∃ g : Space d → 𝕜,
      HolderTendsto (fun n => f (scales D.radius (σ n))) g
        (closure (Ω : Set (Space d))) a)

/-- The separate d=p=1 endpoint uses fixed-height shrinking bumps. -/
def DimensionOneResult (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space 1)) : Prop :=
  letI : Fact (1 ≤ ((1 : ℝ≥0) : ℝ≥0∞)) := ⟨by norm_num⟩
  ∃ D : ConcentrationFamily 𝕜 Ω 1,
    let f := rescale D.bump D.center 0
    (∀ r, 0 < r → r < D.radius → IntegerEmbeddings.RepresentsOn (D.U r) (f r)) ∧
    (∀ r, 0 < r → f r D.center = 1) ∧
    (∀ x, x ≠ D.center → Tendsto (fun r => f r x) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ σ : ℕ → ℕ, StrictMono σ → ¬ ∃ g : Space 1 → 𝕜,
      TendstoUniformlyOn (fun n => f (scales D.radius (σ n))) g atTop
        (closure (Ω : Set (Space 1))))

namespace HolderExpected

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
    ∀ (𝕜 : Type) [RCLike 𝕜] (p : ℝ≥0), 1 ≤ p → (m + 1 : ℕ) < p →
    ∀ [Fact (1 ≤ (p : ℝ≥0∞))], SupercriticalResult 𝕜 Ω p) ∧
  (∀ (e : GraphPieces.Ambient 0 ≃ₗᵢ[ℝ] Space 1) (Ω : Opens (Space 1)),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient 0)) →
    (Ω : Set (Space 1)).Nonempty → ∀ (𝕜 : Type) [RCLike 𝕜], DimensionOneResult 𝕜 Ω)

end HolderExpected
end P102.Sobolev.EndpointNoncompactness
