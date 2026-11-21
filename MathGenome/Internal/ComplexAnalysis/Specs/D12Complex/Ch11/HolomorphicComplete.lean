import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.CompactOpenMetric
import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch01.Basic
import Mathlib.Topology.MetricSpace.Cauchy

/-! Completeness in the exact metric of paper.tex:2390–2400.
Functions are maps on Ω itself, so values outside Ω are not part of the
metric space. The zero extension is used only to express the canonical
pointwise complex differentiability predicate on the open set Ω. -/
noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.Ch11

/-- A representative on the plane; its values off Ω have no significance. -/
def extendFromOpen (Ω : Set ℂ) (f : Ω → ℂ) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ Ω then f ⟨z, hz⟩ else 0

/-- Actual complex-differentiable functions on Ω, with their continuous maps. -/
def HolomorphicSpace (Ω : Set ℂ) :=
  {f : C(Ω, ℂ) // HolomorphicOn Ω (extendFromOpen Ω f)}

end D12Complex.Ch11

namespace Specs.D12Complex.Ch11.HolomorphicComplete
open _root_.D12Complex.Ch11

/-- Restriction of any function satisfying the original weak holomorphy
predicate belongs to this space; continuity imposes no extra hypothesis. -/
def restriction_type : Prop :=
  ∀ (Ω : Set ℂ) (f : ℂ → ℂ), _root_.D12Complex.HolomorphicOn Ω f →
    ∃ g : HolomorphicSpace Ω, ∀ z : Ω, g.val z = f z

/-- Every Cauchy sequence for the specified series distance has a finite
holomorphic limit, converges in that distance, and converges on each compact. -/
def cauchy_limit_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → ∀ F : ℕ → HolomorphicSpace Ω,
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      compactOpenDistance Ω (F m).val (F n).val < ε) →
    ∃ f : HolomorphicSpace Ω,
      Tendsto (fun n => compactOpenDistance Ω (F n).val f.val) atTop (𝓝 0) ∧
      ∀ K : Set Ω, IsCompact K →
        TendstoUniformlyOn (fun n z => (F n).val z) f.val atTop K

/-- Completeness as a metric-space statement, with the precise distance,
for all open sets, without connectedness or nonemptiness assumptions. -/
def complete_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω →
    ∃ m : MetricSpace (HolomorphicSpace Ω),
      (∀ f g : HolomorphicSpace Ω,
        @dist _ m.toDist f g = compactOpenDistance Ω f.val g.val) ∧
      @CompleteSpace (HolomorphicSpace Ω) m.toUniformSpace

end Specs.D12Complex.Ch11.HolomorphicComplete
