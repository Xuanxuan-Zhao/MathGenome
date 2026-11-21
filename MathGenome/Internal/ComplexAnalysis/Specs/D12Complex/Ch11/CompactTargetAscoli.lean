import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-! The compact metric target assertion of paper.tex, d12:11-04.
The domain is the subtype Ω, so continuity and compact subsets are relative
to Ω. The epsilon-delta hypothesis is pointwise local equicontinuity; δ may
vary with z and ε but is common to every member of the family. The strictly
increasing subsequence is chosen before the universal quantifier over compact
sets. Bundling the limit as a continuous map includes its continuity.
No nonemptiness, connectedness, or properness of Ω is imposed. -/

open Set Filter
open scoped Topology

universe u v

namespace Specs.D12Complex.Ch11.CompactTargetAscoli

/-- Every sequence from a locally equicontinuous family with compact metric
range has one subsequence converging uniformly on every compact subset. -/
def subsequence_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω →
  ∀ (Y : Type u) [MetricSpace Y] [CompactSpace Y]
    (ι : Type v) (F : ι → C(Ω, Y)),
    (∀ z : Ω, ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ w : Ω, dist w z < δ →
        ∀ i : ι, dist (F i z) (F i w) < ε) →
    ∀ a : ℕ → ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : C(Ω, Y), ∀ K : Set Ω, IsCompact K →
        TendstoUniformlyOn (fun n z => F (a (φ n)) z) g atTop K

end Specs.D12Complex.Ch11.CompactTargetAscoli
