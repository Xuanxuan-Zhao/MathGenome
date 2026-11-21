import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch05.Ultranets
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Ultrafilters
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.FinerFilterSubnet

/-! Ultranets, paper.tex d10:05:ultrafilter and d10:05:ultranet.
The existence proof uses ultrafilter extension (and hence choice) followed
by the proved monotone-cofinal finer-filter subnet construction. -/

open Set Filter
universe u v
namespace D10Topology.Ch05
open D10Topology.Ch04

/-- A net is eventually in each subset or eventually in its complement. -/
def IsUltranet {D : Type v} {X : Type u} [Preorder D] (a : D → X) : Prop :=
  ∀ A : Set X, EventuallyIn a A ∨ EventuallyIn a Aᶜ

theorem ultranet_iff_tailFilter_ultrafilter {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] (a : D → X) :
    IsUltranet a ↔ IsUltrafilter (TailFilter a) := by
  letI := tailFilter_proper a
  constructor
  · intro ha
    apply (ultrafilter_alternative _ (tailFilter_proper a)).mpr
    intro A
    refine ⟨?_, ?_⟩
    · exact (ha A).imp (tailFilter_mem a A).mpr (tailFilter_mem a Aᶜ).mpr
    · rintro ⟨hA, hc⟩
      exact Filter.compl_notMem hA hc
  · intro h A
    exact ((ultrafilter_alternative _ (tailFilter_proper a)).mp h A).1.imp
      (tailFilter_mem a A).mp (tailFilter_mem a Aᶜ).mp

/-- Extend the original proper tail filter to an ultrafilter. The subnet
bridge supplies a proper tail filter containing that ultrafilter, so
maximality forces equality and hence the ultranet alternative. -/
theorem exists_ultranet_subnet {D : Type v} {X : Type u}
    [Preorder D] [Nonempty D] [IsDirectedOrder D] (a : D → X) :
    ∃ (E : Type (max u v)) (p : Preorder E),
      Nonempty E ∧ @IsDirectedOrder E p.toLE ∧
      ∃ φ : E → D, @SubnetMap E D p _ φ ∧ @IsUltranet E X p (subnet a φ) := by
  obtain ⟨U, hU, hUT⟩ := proper_filter_extension (TailFilter a) (tailFilter_proper a)
  letI := hU.1
  obtain ⟨E, p, hn, hd, φ, hφ, hproper, hfiner, _⟩ := finer_filter_subnet a U hUT
  letI := p
  letI := hn
  letI := hd
  refine ⟨E, p, hn, hd, φ, hφ, ?_⟩
  apply (ultranet_iff_tailFilter_ultrafilter (subnet a φ)).mpr
  have heq : TailFilter (subnet a φ) = U := hU.2 _ hproper hfiner
  rw [heq]
  exact hU

end D10Topology.Ch05
