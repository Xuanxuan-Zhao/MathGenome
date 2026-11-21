import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.CompactExhaustion
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.UniformSpace.UniformConvergence

open Set Filter
open scoped Topology NNReal

namespace D12Complex.Ch11

/-- Restrict a continuous map on Ω to the positive exhaustion stage K_(n+1).
Indexing by n : ℕ includes precisely the indices j ≥ 1 in the manuscript. -/
noncomputable def restrictToStage (Ω : Set ℂ) (n : ℕ) (f : C(Ω, ℂ)) :
    C(compactExhaustionStage Ω (n + 1), ℂ) :=
  f.comp ⟨fun z => ⟨z.val, z.property.1⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- Supremum of the nonnegative pointwise distances. The supremum in ℝ≥0
of the empty family is zero. Openness guarantees boundedness of this family. -/
noncomputable def compactStageSup (Ω : Set ℂ) (n : ℕ) (f g : C(Ω, ℂ)) : ℝ≥0 :=
  ⨆ z : compactExhaustionStage Ω (n + 1),
    nndist (restrictToStage Ω n f z) (restrictToStage Ω n g z)

/-- The precise geometric series metric of d12:11-01. -/
noncomputable def compactOpenDistance (Ω : Set ℂ) (f g : C(Ω, ℂ)) : ℝ :=
  ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) * min 1 (compactStageSup Ω n f g : ℝ)

end D12Complex.Ch11

namespace Specs.D12Complex.Ch11.CompactOpenMetric

open _root_.D12Complex.Ch11

def stageSup_type := (Ω : Set ℂ) → ℕ → C(Ω, ℂ) → C(Ω, ℂ) → ℝ≥0
noncomputable def stageSup_value : stageSup_type := compactStageSup
def distance_type := (Ω : Set ℂ) → C(Ω, ℂ) → C(Ω, ℂ) → ℝ
noncomputable def distance_value : distance_type := compactOpenDistance

def supremum_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → ∀ (n : ℕ) (f g : C(Ω, ℂ)) (r : ℝ), 0 ≤ r →
    ((compactStageSup Ω n f g : ℝ) ≤ r ↔
      ∀ z : compactExhaustionStage Ω (n + 1),
        ‖f ⟨z.val, z.property.1⟩ - g ⟨z.val, z.property.1⟩‖ ≤ r)

def emptySupremum_type : Prop :=
  ∀ (Ω : Set ℂ) (n : ℕ) (f g : C(Ω, ℂ)),
    compactExhaustionStage Ω (n + 1) = ∅ → compactStageSup Ω n f g = 0

def summable_type : Prop :=
  ∀ (Ω : Set ℂ) (f g : C(Ω, ℂ)),
    Summable (fun n : ℕ =>
      (1 / 2 : ℝ) ^ (n + 1) * min 1 (compactStageSup Ω n f g : ℝ))

def metric_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω →
    ∃ m : MetricSpace C(Ω, ℂ),
      ∀ f g : C(Ω, ℂ), @dist _ m.toDist f g = compactOpenDistance Ω f g

/-- Convergence is stated for arbitrary filters, hence includes sequences.
Compact sets are subsets of the subtype Ω, with its usual subspace topology. -/
def convergence_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → ∀ (ι : Type) (l : Filter ι)
    (F : ι → C(Ω, ℂ)) (f : C(Ω, ℂ)),
    Tendsto (fun i => compactOpenDistance Ω (F i) f) l (𝓝 0) ↔
      ∀ K : Set Ω, IsCompact K →
        TendstoUniformlyOn (fun i z => F i z) f l K

def topology_type : Prop :=
  ∀ (Ω : Set ℂ), IsOpen Ω → ∀ (ι : Type) (l : Filter ι)
    (F : ι → C(Ω, ℂ)) (f : C(Ω, ℂ)),
    Tendsto F l (𝓝 f) ↔ Tendsto (fun i => compactOpenDistance Ω (F i) f) l (𝓝 0)

def empty_type : Prop := ∃! _f : C((∅ : Set ℂ), ℂ), True

end Specs.D12Complex.Ch11.CompactOpenMetric
