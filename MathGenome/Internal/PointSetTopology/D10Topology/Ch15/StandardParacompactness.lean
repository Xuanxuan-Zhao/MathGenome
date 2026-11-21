import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch15.StandardParacompactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.MetricSigmaRefinement
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.RefinementUpgrade
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.Compactness

/-!
The three assertions of paper.tex, Theorem d10:15:metric-paracompact.
Metric and regular Lindelöf spaces use the accepted refinement upgrade.
For the latter, a countable subcover is split into singleton indexed layers.
A compact space uses a finite subcover directly. No proof assumes T₁ for
the Lindelöf case or any separation property for the compact case.
-/

open Set
universe u v

namespace D10Topology.Ch15

/-- Every countably indexed family is sigma locally finite: inject its indices
into ℕ, so that each layer has at most one index. This also covers empty and
finite index types, without repeating a nonempty member infinitely often. -/
lemma sigmaLocallyFinite_of_countable {X : Type u} {J : Type v}
    [TopologicalSpace X] [Countable J] (V : J → Set X) : SigmaLocallyFinite V := by
  obtain ⟨c, hc⟩ := Countable.exists_injective_nat J
  apply (sigmaLocallyFinite_iff_layers V).mpr
  refine ⟨c, fun n => ?_⟩
  let : Subsingleton {j : J // c j = n} :=
    ⟨fun a b => Subtype.ext (hc (a.property.trans b.property.symm))⟩
  exact locallyFinite_of_finite _

/-- Every metric space is paracompact for its specified metric topology. -/
theorem metric_paracompact {X : Type u} (d : MetricSpace X) :
    @Paracompact X (Specs.D10Topology.Ch09.MetricConventions.metricTopology
      d.toPseudoMetricSpace) := by
  let := d
  change Paracompact X
  apply refinement_upgrade X inferInstance
  intro I U ho hU
  obtain ⟨V, hVo, hVr, hVd, _⟩ := metric_sigma_refinement U ho hU
  exact ⟨ℕ × I, V, hVo, sigmaLocallyDiscrete_sigmaLocallyFinite V hVd, hVr⟩

/-- Regular Lindelöf spaces are paracompact; regularity has no T₁ assumption. -/
theorem regular_lindelof_paracompact (X : Type u) [TopologicalSpace X]
    (hR : RegularSpace X) (hL : LindelofSpace X) : Paracompact X := by
  apply refinement_upgrade X hR
  intro I U ho hU
  obtain ⟨S, hSc, hScov⟩ := Ch08.lindelof_indexed_countable_subcover hL U ho hU
  let : Countable S := hSc
  refine ⟨S, fun i => U i.val, fun i => ho i.val,
    sigmaLocallyFinite_of_countable _, ?_, fun i => ⟨i.val, Subset.rfl⟩⟩
  simpa only [iUnion_subtype] using hScov

/-- Compact spaces are paracompact, with no separation hypothesis. -/
theorem compact_paracompact (X : Type u) [TopologicalSpace X]
    (hC : Ch05.CoverCompact X) : Paracompact X := by
  constructor
  intro I U ho hU
  have hcompact := (Ch05.coverCompact_iff_isCompact_univ X).mp hC
  obtain ⟨S, hScov⟩ := hcompact.elim_finite_subcover U ho hU.ge
  refine ⟨(S : Set I), fun i => U i.val, fun i => ho i.val, ?_,
    locallyFinite_of_finite _, fun i => ⟨i.val, Subset.rfl⟩⟩
  apply iUnion_eq_univ_iff.mpr
  intro x
  obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hScov (mem_univ x))
  exact ⟨⟨i, hi⟩, hxi⟩

end D10Topology.Ch15
