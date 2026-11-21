import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch13.HarmonicFoundation
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The monotone dichotomy in paper.tex:2584–2594. Functions are total
representatives, with hypotheses and conclusions restricted to the domain.
There is no sign assumption on the original sequence. -/
noncomputable section
open Filter Set
open scoped Topology

namespace D12Complex.HarnackConvergence

/-- Ordinary real uniform convergence on every compact subset, including the
empty compact set. -/
def ConvergesOnCompacts (Ω : Set ℂ) (u : ℕ → ℂ → ℝ) (v : ℂ → ℝ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → TendstoUniformlyOn u v atTop K

/-- The threshold and compact set are fixed before the eventual index. -/
def DivergesOnCompacts (Ω : Set ℂ) (u : ℕ → ℂ → ℝ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ Ω → ∀ T : ℝ,
    ∀ᶠ n in atTop, ∀ z ∈ K, T < u n z

end D12Complex.HarnackConvergence

namespace Specs.D12Complex.Ch13.HarnackConvergence
open _root_.D12Complex _root_.D12Complex.HarnackConvergence

def harnack_convergence_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℕ → ℂ → ℝ), IsDomain Ω →
    (∀ n, HarmonicOn Ω (u n)) → (∀ z ∈ Ω, Monotone (fun n => u n z)) →
    (∃ v : ℂ → ℝ, HarmonicOn Ω v ∧ ConvergesOnCompacts Ω u v) ∨
      DivergesOnCompacts Ω u

/-- The same criterion works at every chosen basepoint. -/
def bounded_iff_finite_limit_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℕ → ℂ → ℝ), IsDomain Ω →
    (∀ n, HarmonicOn Ω (u n)) → (∀ z ∈ Ω, Monotone (fun n => u n z)) →
    ∀ a ∈ Ω, BddAbove (range (fun n => u n a)) ↔
      ∃ v : ℂ → ℝ, HarmonicOn Ω v ∧ ConvergesOnCompacts Ω u v

def unbounded_iff_compact_divergence_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℕ → ℂ → ℝ), IsDomain Ω →
    (∀ n, HarmonicOn Ω (u n)) → (∀ z ∈ Ω, Monotone (fun n => u n z)) →
    ∀ a ∈ Ω, (¬ BddAbove (range (fun n => u n a))) ↔ DivergesOnCompacts Ω u

/-- Finite convergence at any point rules out divergence at any other point. -/
def no_mixed_limits_type : Prop :=
  ∀ (Ω : Set ℂ) (u : ℕ → ℂ → ℝ), IsDomain Ω →
    (∀ n, HarmonicOn Ω (u n)) → (∀ z ∈ Ω, Monotone (fun n => u n z)) →
    ∀ a ∈ Ω, ∀ b ∈ Ω, ∀ L : ℝ,
      Tendsto (fun n => u n a) atTop (𝓝 L) →
      ¬ Tendsto (fun n => u n b) atTop atTop

end Specs.D12Complex.Ch13.HarnackConvergence
