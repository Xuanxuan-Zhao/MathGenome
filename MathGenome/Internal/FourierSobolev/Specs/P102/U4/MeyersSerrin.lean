import MathGenome.Internal.FourierSobolev.Specs.P102.U4.WholeSpaceDensity
import MathGenome.Internal.FourierSobolev.Specs.P102.U4.ZeroExtension

/-! Independent statements for paper.tex:1427–1438, AN-11-C04-R03.
The functions below are represented on the ambient Euclidean space, but their
smoothness and their derivative equalities are required only on the given open
set. No extension across its boundary is imposed. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ContDiff Distributions ENNReal Topology
namespace P102.U4

/-- All weak derivatives, including order zero, are represented by the ordinary
derivatives of the same function on Ω. Values outside Ω have no significance. -/
def RepresentsSobolevOn {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Space d → 𝕜) (u : Sobolev 𝕜 Ω m p) : Prop :=
  ∀ α : SobolevIndex d m,
    (sobolevDerivative u α : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))]
      multiPartial f α.val

/-- The full derivative sum error on an arbitrary open set. -/
def domainSobolevSumError {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    {Ω : Opens (Space d)} {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (u v : Sobolev 𝕜 Ω m p) : ℝ :=
  ∑ α : SobolevIndex d m, ‖sobolevDerivative u α - sobolevDerivative v α‖

namespace MeyersSerrinExpected

/-- Sequential smooth density on every open set, in precisely the source norm.
Includes empty opens, dimension zero, and order zero; excludes p = ∞. -/
def SmoothDensity : Prop :=
  ∀ {d : ℕ} {𝕜 : Type} [RCLike 𝕜] (Ω : Opens (Space d)) (m : ℕ)
    (p : ℝ≥0∞) [Fact (1 ≤ p)], p ≠ ⊤ →
    ∀ u : Sobolev 𝕜 Ω m p,
    ∃ (f : ℕ → Space d → 𝕜) (v : ℕ → Sobolev 𝕜 Ω m p),
      (∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (f n) Ω ∧ RepresentsSobolevOn (f n) (v n)) ∧
      Tendsto v atTop (𝓝 u) ∧
      Tendsto (fun n => domainSobolevSumError (v n) u) atTop (𝓝 0)

/-- The compactly supported whole-space clause, with its existing canonical
objects and the entire derivative sum convergence. -/
def WholeSpaceDensity : Prop := WholeSpaceDensityExpected.Density

/-- W₀ is the norm closure of tests. Its zero-extension operator is a linear
isometry into the whole-space Sobolev space, commuting with every derivative. -/
def ZeroExtension : Prop :=
  ZeroExtensionExpected.Closure ∧ ZeroExtensionExpected.Extension

end MeyersSerrinExpected
end P102.U4
