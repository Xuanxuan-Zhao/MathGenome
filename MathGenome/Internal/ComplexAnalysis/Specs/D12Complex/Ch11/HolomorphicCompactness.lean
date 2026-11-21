import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-! The holomorphic part of paper.tex, d12:11-04. Functions are total complex
functions restricted to Ω. Local boundedness is quantified over every compact
subset, and the subsequence has one index map for all compact subsets. -/
noncomputable section
open Set Filter

namespace Specs.D12Complex.Ch11.HolomorphicCompactness
open _root_.D12Complex

def LocallyBounded_type := Set ℂ → Set (ℂ → ℂ) → Prop

def LocallyBounded_value : LocallyBounded_type :=
  fun Ω 𝓕 => ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ f ∈ 𝓕, ∀ z ∈ K, ‖f z‖ ≤ M

def equicontinuousOn_compact_type : Prop :=
  ∀ (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ)), IsOpen Ω →
    (∀ f ∈ 𝓕, HolomorphicOn Ω f) → LocallyBounded_value Ω 𝓕 →
    ∀ K : Set ℂ, IsCompact K → K ⊆ Ω →
      UniformEquicontinuousOn (fun f : 𝓕 => (f : ℂ → ℂ)) K

def subsequence_holomorphic_limit_type : Prop :=
  ∀ (Ω : Set ℂ) (𝓕 : Set (ℂ → ℂ)), IsOpen Ω →
    (∀ f ∈ 𝓕, HolomorphicOn Ω f) → LocallyBounded_value Ω 𝓕 →
    ∀ F : ℕ → ℂ → ℂ, (∀ n, F n ∈ 𝓕) →
      ∃ (φ : ℕ → ℕ) (f : ℂ → ℂ), StrictMono φ ∧ HolomorphicOn Ω f ∧
        TendstoLocallyUniformlyOn (fun n => F (φ n)) f atTop Ω

end Specs.D12Complex.Ch11.HolomorphicCompactness
