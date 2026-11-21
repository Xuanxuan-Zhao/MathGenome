import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.CompactMaximum
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch06.StrongModulus
import Mathlib.Topology.Order.Compact

/-! The modulus attains a global maximum by compactness. At every point
with the same value as a maximizer, the planar strong maximum principle
in a source chart makes the function constant throughout that chart.
Consequently the maximizer's fibre is nonempty, closed, and open, hence
is the whole connected surface. -/

open Set Filter
open scoped Topology

namespace D12Complex.Surfaces

theorem scalarHolomorphic_constant_of_compact :
    Specs.D12Complex.Ch20.CompactMaximum.scalarHolomorphic_constant_of_compact_type := by
  intro X _ _ S f hf
  let := S.connected
  obtain ⟨a, _, hmax⟩ := isCompact_univ.exists_isMaxOn
    (Set.univ_nonempty : (Set.univ : Set X).Nonempty) hf.1.norm.continuousOn
  let E : Set X := {x | f x = f a}
  have hclosed : IsClosed E := isClosed_eq hf.1 continuous_const
  have hopen : IsOpen E := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change f x = f a at hx
    obtain ⟨e, he, hxe⟩ := S.isAtlas.1 x
    have hxcoord := e.val.map_source hxe
    have hlocal : IsLocalMaxOn (fun z => ‖(f ∘ e.val.symm) z‖)
        e.val.target (e.val x) := by
      apply Filter.Eventually.of_forall
      intro z
      simpa only [Function.comp_apply, e.val.left_inv hxe, hx, Set.mem_ofPred_eq] using
        hmax (Set.mem_univ (e.val.symm z))
    have hconst := StrongModulus.constant_of_local_maximum_modulus
      e.val.target (f ∘ e.val.symm) (e.val x) e.property
      (hf.2 e he) hxcoord hlocal
    apply mem_of_superset (e.val.open_source.mem_nhds hxe)
    intro y hy
    change f y = f a
    calc
      f y = f x := by
        simpa only [Function.comp_apply, e.val.left_inv hy, e.val.left_inv hxe]
          using hconst (e.val y) (e.val.map_source hy)
      _ = f a := hx
  have hall : E = univ := (show IsClopen E from ⟨hclosed, hopen⟩).eq_univ ⟨a, rfl⟩
  exact ⟨f a, fun x => show x ∈ E from hall.symm ▸ Set.mem_univ x⟩

end D12Complex.Surfaces
