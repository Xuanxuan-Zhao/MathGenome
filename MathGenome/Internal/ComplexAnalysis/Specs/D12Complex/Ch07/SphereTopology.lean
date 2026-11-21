import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.Sphere
import Mathlib.Topology.PartialHomeomorph.Defs

/-!
The topology part of paper.tex, d12:07-05-classification (1782–1801).
These statements refer to the canonical one-point topology and to the exact
partial equivalences fixed in the upstream sphere Spec. The chart assertions
include openness and a partial homeomorphism with the same maps, domains and
images. The transition assertion uses weak complex holomorphy, in both directions,
on the full overlap ℂ \ {0}.
-/

namespace Specs.D12Complex.Ch07.SphereTopology
open _root_.D12Complex

def sphere_compact_type : Prop := CompactSpace RiemannSphere

def sphere_hausdorff_type : Prop := T2Space RiemannSphere

def sphere_connected_type : Prop := ConnectedSpace RiemannSphere

def sphereFinite_denseRange_type : Prop := DenseRange sphereFinite

def finiteChart_homeomorph_type : Prop :=
  IsOpen finiteChart.source ∧ IsOpen finiteChart.target ∧
    ∃ e : PartialHomeomorph RiemannSphere ℂ, e.toPartialEquiv = finiteChart

def infinityChart_homeomorph_type : Prop :=
  IsOpen infinityChart.source ∧ IsOpen infinityChart.target ∧
    ∃ e : PartialHomeomorph RiemannSphere ℂ, e.toPartialEquiv = infinityChart

def sphere_chart_overlap_type : Prop :=
  finiteChart.target ∩ finiteChart.symm ⁻¹' infinityChart.source = ({0}ᶜ : Set ℂ) ∧
  infinityChart.target ∩ infinityChart.symm ⁻¹' finiteChart.source = ({0}ᶜ : Set ℂ)

def sphere_chart_transition_formulas_type : Prop :=
  ∀ z : ℂ, z ≠ 0 →
    infinityChart (finiteChart.symm z) = z⁻¹ ∧
    finiteChart (infinityChart.symm z) = z⁻¹

def sphere_chart_transition_biholomorphic_type : Prop :=
  BiholomorphicPair ({0}ᶜ : Set ℂ) ({0}ᶜ : Set ℂ)
    (fun z => infinityChart (finiteChart.symm z))
    (fun w => finiteChart (infinityChart.symm w))

end Specs.D12Complex.Ch07.SphereTopology
