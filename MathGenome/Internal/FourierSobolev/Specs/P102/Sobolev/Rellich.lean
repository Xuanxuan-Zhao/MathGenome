import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.CriticalMorreyEmbeddings
import MathGenome.Internal.FourierSobolev.Specs.P102.Sobolev.SupportedCompactness

/-! Rellich compactness, paper.tex:1883–1928. All finite exponents at least
one are included, including p=d=1. The shared geometric condition includes
boundedness and allows empty and disconnected open sets. -/
noncomputable section
open Set TopologicalSpace MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace P102.Sobolev.Rellich
open P102.U4

/-- Compactness of the actual inclusion on almost-everywhere classes. -/
def CompactLpInclusion {d : ℕ} (𝕜 : Type) [RCLike 𝕜] (Ω : Opens (Space d))
    (p q : ℝ≥0∞) [Fact (1 ≤ p)] [Fact (1 ≤ q)] : Prop :=
  ∃ I : Sobolev 𝕜 Ω 1 p →L[𝕜] DomainLp 𝕜 Ω q,
    Function.Injective I ∧
    (∀ u, (I u : Space d → 𝕜) =ᵐ[volume.restrict (Ω : Set (Space d))]
      sobolevUnderlying u) ∧
    ∀ A : Set (Sobolev 𝕜 Ω 1 p), Bornology.IsBounded A →
      IsCompact (closure (I '' A))

/-- Uniform convergence plus convergence of the Hölder seminorm of the
error. At beta=0 only uniform convergence is required, exactly the supremum
norm convention. For beta>0 this is convergence in the full C^(0,beta) norm. -/
def HolderConvergesOn {d : ℕ} {𝕜 : Type} [RCLike 𝕜]
    (v : ℕ → Space d → 𝕜) (f : Space d → 𝕜) (S : Set (Space d)) (β : ℝ) : Prop :=
  TendstoUniformlyOn v f atTop S ∧
    (β = 0 ∨ ∀ ε > 0, ∀ᶠ n in atTop,
      ∀ x ∈ S, ∀ y ∈ S,
        ‖(v n x - f x) - (v n y - f y)‖ ≤ ε * ‖x - y‖ ^ β)

namespace Expected

def Lebesgue : Prop :=
  ∀ (m : ℕ) (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) →
    ∀ (p q : ℝ≥0) (hp : 1 ≤ p) (hq : 1 ≤ q),
    (p < (m + 1 : ℕ) → q < criticalExponent (m + 1) p) →
    letI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
    letI : Fact (1 ≤ (q : ℝ≥0∞)) := ⟨by exact_mod_cast hq⟩
    ∀ (𝕜 : Type) [RCLike 𝕜], CompactLpInclusion 𝕜 Ω p q

/-- The functions v_n are the unique continuous representatives on the closure
constructed upstream. Quantifying over every such choice makes independence
of arbitrary values outside the closure explicit. The limit belongs to the
same Hölder target, with convergence of the full norm as defined above. -/
def Holder : Prop :=
  ∀ (m : ℕ) (e : GraphPieces.Ambient m ≃ₗᵢ[ℝ] Space (m + 1))
    (Ω : Opens (Space (m + 1))),
    Geometry.IsLipschitzOpen (Extension.geometricOpen e Ω : Set (GraphPieces.Ambient m)) →
    ∀ (p : ℝ≥0) (hp : 1 ≤ p), (m + 1 : ℕ) < p →
    ∀ β : ℝ, 0 ≤ β → β < 1 - ((m + 1 : ℕ) : ℝ) / p →
    letI : Fact (1 ≤ (p : ℝ≥0∞)) := ⟨by exact_mod_cast hp⟩
    ∀ (𝕜 : Type) [RCLike 𝕜] (u : ℕ → Sobolev 𝕜 Ω 1 p),
    Bornology.IsBounded (range u) →
    ∀ v : ℕ → Space (m + 1) → 𝕜,
    (∀ n, ContinuousOn (v n) (closure (Ω : Set (Space (m + 1)))) ∧
      IntegerEmbeddings.RepresentsOn (u n) (v n)) →
    ∃ (σ : ℕ → ℕ) (f : Space (m + 1) → 𝕜), StrictMono σ ∧
      ContinuousOn f (closure (Ω : Set (Space (m + 1)))) ∧
      (∃ M : ℝ, IntegerEmbeddings.HolderNormBound f
        (closure (Ω : Set (Space (m + 1)))) β M) ∧
      HolderConvergesOn (v ∘ σ) f (closure (Ω : Set (Space (m + 1)))) β

end Expected
end P102.Sobolev.Rellich
