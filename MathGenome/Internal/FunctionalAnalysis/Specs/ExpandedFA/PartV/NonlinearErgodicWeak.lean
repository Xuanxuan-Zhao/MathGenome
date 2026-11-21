import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonexpansiveDemiclosure
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-! Independent statements for the weak part of paper.tex,
`fa2:p5:nonlinear-ergodic`, 22474–22514. All dual tests are scalar-linear.
The value of the Cesàro average at zero is harmless and does not restrict
its stated positive-index definition or its limit. -/
noncomputable section
open Filter
open scoped Topology
namespace ExpandedFA.PartV.NonlinearErgodicWeak.Spec
universe u v

abbrev Nonexpansive := @NonexpansiveDemiclosure.Spec.Nonexpansive
abbrev WeaklyConverges := @NonexpansiveDemiclosure.Spec.WeaklyConverges
abbrev averaged := @NonexpansiveDemiclosure.Spec.averaged

/-- The ordinary arithmetic averages of a sequence. -/
def cesaro (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] (z : ℕ → H) (n : ℕ) : H :=
  letI := ExpandedFA.Hilbert.Conventions.Spec.RealificationValue 𝕜 H
  (n : ℝ)⁻¹ • ∑ j ∈ Finset.range n, z j

/-- Asymptotic regularity of the averaged iterates, for the original T. -/
def AveragedRegularity : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), Nonexpansive T → (∃ p, T p = p) → ∀ f : H,
    Tendsto (fun n => (averaged 𝕜 T)^[n] f - T ((averaged 𝕜 T)^[n] f)) atTop (𝓝 0)

/-- Asymptotic regularity of the Cesàro averages of the original orbit. -/
def CesaroRegularity : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), Nonexpansive T → (∃ p, T p = p) → ∀ f : H,
    Tendsto (fun n => cesaro 𝕜 (fun j => T^[j] f) n -
      T (cesaro 𝕜 (fun j => T^[j] f) n)) atTop (𝓝 0)

/-- Uniqueness of arbitrary topological weak cluster points, without a
countable neighborhood basis or a subsequence assumption. -/
def UniqueWeakCluster (𝕜 : Type u) {H : Type v} [RCLike 𝕜]
    [NormedAddCommGroup H] [NormedSpace 𝕜 H] (z : ℕ → H) : Prop :=
  ∀ p q : H,
    MapClusterPt (toWeakSpace 𝕜 H p) atTop (fun n => toWeakSpace 𝕜 H (z n)) →
    MapClusterPt (toWeakSpace 𝕜 H q) atTop (fun n => toWeakSpace 𝕜 H (z n)) → p = q

def WeakClusterUniqueness : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), Nonexpansive T → (∃ p, T p = p) → ∀ f : H,
    UniqueWeakCluster 𝕜 (fun n => (averaged 𝕜 T)^[n] f) ∧
    UniqueWeakCluster 𝕜 (cesaro 𝕜 (fun j => T^[j] f))

/-- The two weak limits are independently quantified fixed points. -/
def NonlinearErgodicWeak : Prop :=
  ∀ (𝕜 : Type u) (H : Type v) [RCLike 𝕜]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    (T : H → H), Nonexpansive T → (∃ p, T p = p) → ∀ f : H,
    (∃ p, T p = p ∧ WeaklyConverges 𝕜 (fun n => (averaged 𝕜 T)^[n] f) p) ∧
    (∃ q, T q = q ∧ WeaklyConverges 𝕜 (cesaro 𝕜 (fun j => T^[j] f)) q)

end ExpandedFA.PartV.NonlinearErgodicWeak.Spec
