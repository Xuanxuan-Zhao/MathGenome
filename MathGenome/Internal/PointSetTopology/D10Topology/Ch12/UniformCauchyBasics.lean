import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.UniformCauchyBasics
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformConventions

/-! The three implications in paper.tex, Lemma `d10:12:cauchy-cluster`.
The Chapter 4 bridges identify the manuscript's neighborhood formulations of
convergence and clustering. The Chapter 12 bridge identifies its small-square
Cauchy condition, including properness, with Mathlib's `Cauchy`.
The canonical uniform-space topology is the induced topology, as established
in `D10Topology.Ch12.UniformTopology.uniformTopology_eq_canonical`.
-/

open Filter
universe u v

namespace D10Topology.Ch12

/-- Convergence of a proper filter implies the Cauchy condition. -/
theorem convergent_cauchy {X : Type u} [UniformSpace X] (F : Filter X) (x : X)
    (hF : F.NeBot) (hx : Ch04.FilterConverges F x) : CauchyFilter F := by
  letI : F.NeBot := hF
  exact (cauchyFilter_iff_mathlib F).mpr
    (cauchy_nhds.mono ((Ch04.converges_iff_le_nhds F x).mp hx))

/-- A Cauchy filter converges to every one of its cluster points. -/
theorem cauchy_cluster_converges {X : Type u} [UniformSpace X]
    (F : Filter X) (x : X) (hF : CauchyFilter F)
    (hx : Ch04.FilterClusters F x) : Ch04.FilterConverges F x := by
  exact (Ch04.converges_iff_le_nhds F x).mpr
    (le_nhds_of_cauchy_adhp ((cauchyFilter_iff_mathlib F).mp hF)
      ((Ch04.clusters_iff_clusterPt F x).mp hx))

/-- Uniformly continuous maps send Cauchy filters to Cauchy image filters. -/
theorem uniformContinuous_image_cauchy {X : Type u} {Y : Type v}
    [UniformSpace X] [UniformSpace Y] (f : X → Y) (F : Filter X)
    (hf : EntourageContinuous f) (hF : CauchyFilter F) :
    CauchyFilter (Ch04.ImageFilter f F) := by
  exact (cauchyFilter_iff_mathlib (Ch04.ImageFilter f F)).mpr
    (((cauchyFilter_iff_mathlib F).mp hF).map
      ((entourageContinuous_iff_mathlib f).mp hf))

end D10Topology.Ch12
