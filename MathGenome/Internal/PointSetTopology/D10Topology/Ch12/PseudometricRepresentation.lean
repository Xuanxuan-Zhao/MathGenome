import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch12.PseudometricRepresentation
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.DyadicChains
import MathGenome.Internal.PointSetTopology.D10Topology.Ch12.EntourageCalculus

open Set Filter
open scoped Uniformity
universe u

namespace D10Topology.Ch12

/-- Repeated symmetric cube roots, followed by the dyadic chain lemma, provide
a bounded uniformly continuous pseudometric for a prescribed entourage. -/
theorem entourage_pseudometric :
    Specs.D10Topology.Ch12.PseudometricRepresentation.entourage_pseudometric := by
  intro X uX U hU
  classical
  let E := {W : Set (X × X) // W ∈ 𝓤 X}
  have hroot (W : E) : ∃ Z : E,
      relationInverse Z.val = Z.val ∧ Z.val ⊆ W.val ∧ relationPower Z.val 3 ⊆ W.val := by
    obtain ⟨Z, hZ, hs, hsub, hcube⟩ := symmetric_power_refinement 3 W.val W.property
    exact ⟨⟨Z, hZ⟩, hs, hsub, hcube⟩
  choose root hsym hsub hcube using hroot
  let W : ℕ → E := Nat.rec ⟨univ, univ_mem⟩
    (fun _ W => root ⟨W.val ∩ U, inter_mem W.property hU⟩)
  let V : ℕ → Set (X × X) := fun n => (W n).val
  have hsymV (n : ℕ) : relationInverse (V (n + 1)) = V (n + 1) :=
    hsym ⟨(W n).val ∩ U, inter_mem (W n).property hU⟩
  have hcubeV (n : ℕ) : relationPower (V (n + 1)) 3 ⊆ V n :=
    (hcube ⟨(W n).val ∩ U, inter_mem (W n).property hU⟩).trans inter_subset_left
  have hVU : V 1 ⊆ U :=
    (hsub ⟨(W 0).val ∩ U, inter_mem (W 0).property hU⟩).trans inter_subset_right
  obtain ⟨p, hp, hb, hi, hu⟩ := dyadic_chains V rfl
    (fun n => (W (n + 1)).property) hsymV hcubeV
  let d : PseudoMetricSpace X :=
    { dist := p
      dist_self := hp.2.1
      dist_comm := hp.2.2.1
      dist_triangle := hp.2.2.2 }
  refine ⟨d, hb, hu, hu.continuous, ?_, ?_⟩
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (show (1 / 2 : ℝ) < 1 by norm_num)
    exact mem_of_superset (W n).property (fun q hq => ((hi n).1 hq).trans_lt hn)
  · have hquarter : (1 / 2 : ℝ) ^ (1 + 1) = 1 / 4 := by norm_num
    intro q hq
    apply hVU
    apply (hi 1).2
    change p q.1 q.2 < (1 / 4 : ℝ) at hq
    change p q.1 q.2 < (1 / 2 : ℝ) ^ (1 + 1)
    rw [hquarter]
    exact hq

/-- The family indexed by the original entourages generates precisely the
original uniformity. Each member is bounded and continuous for the original
product structures, even if the uniformity is not separated or countably based. -/
theorem pseudometric_representation :
    Specs.D10Topology.Ch12.PseudometricRepresentation.pseudometric_representation := by
  intro X uX
  classical
  choose p hp using (fun U : {U : Set (X × X) // U ∈ 𝓤 X} =>
    entourage_pseudometric U.val U.property)
  refine ⟨p, hp, ?_⟩
  apply UniformSpace.ext
  change @uniformity X (⨅ U, (p U).toUniformSpace) = 𝓤 X
  rw [iInf_uniformity]
  apply le_antisymm
  · intro U hU
    let i : {U : Set (X × X) // U ∈ 𝓤 X} := ⟨U, hU⟩
    have hball : {q | @dist X (p i).toDist q.1 q.2 < (1 / 4 : ℝ)} ∈
        @uniformity X (p i).toUniformSpace :=
      @Metric.dist_mem_uniformity X (p i) (1 / 4) (by norm_num)
    exact mem_of_superset ((iInf_le (fun i => @uniformity X (p i).toUniformSpace) i) hball)
      (hp i).2.2.2.2
  · refine le_iInf fun i => (@Metric.uniformity_basis_dist X (p i)).ge_iff.mpr ?_
    intro ε hε
    exact (hp i).2.2.2.1 ε hε

theorem empty_pseudometric_representation :
    Specs.D10Topology.Ch12.PseudometricRepresentation.empty_pseudometric_representation := by
  intro X hX uX
  exact ⟨Subsingleton.elim _ _, uniformContinuous_const, continuous_const⟩

end D10Topology.Ch12
