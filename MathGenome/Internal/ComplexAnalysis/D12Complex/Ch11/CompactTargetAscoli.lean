import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch11.CompactTargetAscoli
import Mathlib.Topology.UniformSpace.Ascoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Sequences

open Set Filter
open scoped Topology

namespace D12Complex.Ch11.CompactTargetAscoli

/-- A compact envelope for an equicontinuous family with compact target.
Take the closure in the product topology, whose members remain equicontinuous
and hence continuous. Arzelà–Ascoli upgrades its pointwise compactness to
compactness in the compact-open topology. -/
lemma exists_compact_superset {X Y ι : Type*} [TopologicalSpace X]
    [UniformSpace Y] [CompactSpace Y]
    (F : ι → C(X, Y)) (hF : Equicontinuous (fun i x => F i x)) :
    ∃ S : Set C(X, Y), IsCompact S ∧ ∀ i, F i ∈ S := by
  classical
  let A : Set (X → Y) := closure (range (fun i x => F i x))
  have hA : A.Equicontinuous := (equicontinuous_iff_range.mp hF).closure
  let S : Set C(X, Y) := {f | (f : X → Y) ∈ A}
  have himage : ContinuousMap.toFun '' S = A := by
    ext f
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact hg
    · intro hf
      exact ⟨⟨f, hA.continuous_of_mem hf⟩, hf, rfl⟩
  have hS : Equicontinuous (fun (f : S) (x : X) => f.val x) :=
    hA.comp (fun (f : S) => ⟨(f.val : X → Y), f.property⟩)
  refine ⟨S, ArzelaAscoli.isCompact_of_equicontinuous S ?_ hS, ?_⟩
  · rw [himage]
    exact isClosed_closure.isCompact
  · intro i
    exact subset_closure (mem_range_self i)

/-- The compact metric target Arzelà–Ascoli subsequence theorem, with local
pointwise equicontinuity and a single subsequence for every compact set. -/
theorem subsequence : Specs.D12Complex.Ch11.CompactTargetAscoli.subsequence_type := by
  intro Ω hΩ Y _ _ ι F hF a
  let : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  have heq : Equicontinuous (fun i z => F i z) :=
    fun z => Metric.equicontinuousAt_iff.mpr (hF z)
  obtain ⟨S, hS, hFS⟩ := exists_compact_superset F heq
  obtain ⟨g, _, φ, hφ, hlim⟩ := hS.tendsto_subseq (fun n => hFS (a n))
  refine ⟨φ, hφ, g, ?_⟩
  exact ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.mp hlim

end D12Complex.Ch11.CompactTargetAscoli
