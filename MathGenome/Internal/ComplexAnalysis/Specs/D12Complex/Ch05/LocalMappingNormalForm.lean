import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.LocalZeroFactorization
import Mathlib.Data.Set.Card

/-! Independent statements for paper.tex:1355–1380, D12.05.05.
The nonconstancy premise concerns the germ, not values on remote components.
The inverse maps and the exact fibre sets all use the same source U.
The center's local multiplicity is the analytic order of f - f(a).
-/
noncomputable section
open Filter Set
open scoped Topology

namespace Specs.D12Complex.Ch05.LocalMappingNormalForm
open _root_.D12Complex

/-- Positive powers are surjective, including the zero target. -/
def complex_power_surjective_type : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ w : ℂ, ∃ z : ℂ, z ^ m = w

/-- Exactly m distinct roots, with no algebraic-closure hypothesis. -/
def complex_power_roots_type : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ w : ℂ, w ≠ 0 →
    Set.Finite {z : ℂ | z ^ m = w} ∧ Set.ncard {z : ℂ | z ^ m = w} = m

/-- Local power coordinate, image, all noncentral fibre counts, and the
central fibre with its exact local multiplicity. -/
def local_mapping_normal_form_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ) (a : ℂ),
    HolomorphicOn Ω f → a ∈ Ω → ¬ (∀ᶠ z in 𝓝 a, f z = f a) →
    ∃ (m : ℕ), 0 < m ∧ ∃ (r : ℝ), 0 < r ∧
    ∃ (U : Set ℂ) (φ ψ : ℂ → ℂ),
      a ∈ U ∧ U ⊆ Ω ∧ BiholomorphicPair U (Metric.ball 0 r) φ ψ ∧
      φ a = 0 ∧ (∀ z ∈ U, f z - f a = (φ z) ^ m) ∧
      f '' U = Metric.ball (f a) (r ^ m) ∧
      (∀ w ∈ Metric.ball (f a) (r ^ m), w ≠ f a →
        Set.Finite {z : ℂ | z ∈ U ∧ f z = w} ∧
          Set.ncard {z : ℂ | z ∈ U ∧ f z = w} = m) ∧
      (∀ z ∈ U, f z = f a ↔ z = a) ∧
      analyticOrderAt (fun z => f z - f a) a = (m : ℕ∞)

end Specs.D12Complex.Ch05.LocalMappingNormalForm
