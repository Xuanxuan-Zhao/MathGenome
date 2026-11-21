import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.CountableUniformMetrization
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.UniformConventions
import Mathlib.Topology.Metrizable.Uniformity

open Set Filter
open scoped Uniformity
universe u

namespace D10Topology.Ch12

abbrev HasCountableEntourageBase :=
  Specs.D10Topology.Ch12.CountableUniformMetrization.HasCountableEntourageBase

/-- The explicit entourage-base formulation agrees with the library's filter
interface, even for a finite base or a bottom filter on the empty type. -/
theorem countable_entourage_base_iff_mathlib :
    Specs.D10Topology.Ch12.CountableUniformMetrization.countable_entourage_base_iff_mathlib := by
  intro X uX
  constructor
  · rintro ⟨B, hcount, hmem, hrefine⟩
    have hb : (𝓤 X).HasBasis (fun V => V ∈ B) id := by
      constructor
      intro U
      exact ⟨hrefine U, fun ⟨V, hV, hVU⟩ => mem_of_superset (hmem V hV) hVU⟩
    exact (show (𝓤 X).HasCountableBasis (fun V => V ∈ B) id from ⟨hb, hcount⟩).isCountablyGenerated
  · intro h
    letI := h
    obtain ⟨V, hV⟩ := (𝓤 X).exists_antitone_basis
    refine ⟨range V, countable_range V, ?_, ?_⟩
    · rintro _ ⟨n, rfl⟩
      exact hV.mem n
    · intro U hU
      obtain ⟨n, hn⟩ := hV.mem_iff.mp hU
      exact ⟨V n, mem_range_self n, hn⟩

/-- The library chain construction yields a finite real-valued pseudometric
with exactly the original uniformity. The converse uses its 1/(n+1) base. -/
theorem countable_uniform_pseudometrization :
    Specs.D10Topology.Ch12.CountableUniformMetrization.countable_uniform_pseudometrization := by
  intro X uX
  rw [countable_entourage_base_iff_mathlib]
  constructor
  · intro h
    letI := h
    exact UniformSpace.metrizable_uniformity X
  · rintro ⟨d, hd⟩
    have h : (@uniformity X d.toUniformSpace).IsCountablyGenerated :=
      (@Metric.uniformity_basis_dist_inv_nat_succ X d).isCountablyGenerated
    rwa [hd] at h

/-- Separation is precisely the additional hypothesis for a metric that
generates this uniformity, rather than only its topology. -/
theorem countable_uniform_metrization :
    Specs.D10Topology.Ch12.CountableUniformMetrization.countable_uniform_metrization := by
  intro X uX hbase
  constructor
  · rintro ⟨d, hd⟩
    have h : @T0Space X d.toUniformSpace.toTopologicalSpace := by
      letI := d
      infer_instance
    have ht : @T0Space X uX.toTopologicalSpace := by
      rwa [hd] at h
    exact separated_iff_mathlib.mpr ht
  · intro hsep
    letI : (𝓤 X).IsCountablyGenerated := countable_entourage_base_iff_mathlib.mp hbase
    letI : T0Space X := separated_iff_mathlib.mp hsep
    exact ⟨UniformSpace.metricSpace X, rfl⟩

theorem empty_uniform_pseudometrization :
    Specs.D10Topology.Ch12.CountableUniformMetrization.empty_uniform_pseudometrization := by
  intro X uX hX
  have hz : (Specs.D10Topology.Ch12.PseudometricFamilies.zeroPseudometric X).toUniformSpace = uX :=
    uniformity_empty_unique _ _
  refine ⟨countable_uniform_pseudometrization.mpr ⟨_, hz⟩, ?_, uniformity_empty, hz, ?_⟩
  · apply separated_iff_mathlib.mpr
    infer_instance
  · intro x
    exact isEmptyElim x

end D10Topology.Ch12
