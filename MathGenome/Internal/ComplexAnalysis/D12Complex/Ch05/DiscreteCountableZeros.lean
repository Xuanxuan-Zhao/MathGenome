import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch05.DiscreteCountableZeros
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.IdentityTheorem
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Connected.LocallyConnected

/-!
Discrete and countable zero sets (paper.tex:1323–1338).
The identity theorem rules out accumulation anywhere inside the domain,
including at points not initially assumed to be zeros. Compactness then
gives finiteness, and second countability gives countability of the
discrete subspace. Components of a plane open set are themselves open
domains, so the final theorem applies without excluding zero functions
on unrelated components.
-/

open Filter Set
open scoped Topology

namespace D12Complex.DiscreteCountableZeros

private lemma no_accPt_zeros {Ω : Set ℂ} {f : ℂ → ℂ}
    (hΩ : IsDomain Ω) (hf : HolomorphicOn Ω f)
    (hnonzero : ¬ EqOn f (fun _ => 0) Ω) {a : ℂ} (ha : a ∈ Ω) :
    ¬ AccPt a (𝓟 {z | z ∈ Ω ∧ f z = 0}) := by
  intro hacc
  exact hnonzero (IdentityTheorem.identity_zero_of_accPt Ω f a hΩ hf ha hacc)

theorem zeroSet_isDiscrete :
    Specs.D12Complex.Ch05.DiscreteCountableZeros.zeroSet_isDiscrete_type := by
  intro Ω f hΩ hf hnonzero
  exact isDiscrete_iff_discreteTopology.mpr
    (discreteTopology_of_noAccPts fun _ hz => no_accPt_zeros hΩ hf hnonzero hz.1)

theorem zeros_isolated :
    Specs.D12Complex.Ch05.DiscreteCountableZeros.zeros_isolated_type := by
  intro Ω f hΩ hf hnonzero a ha hfa
  obtain ⟨U, hU, heq⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp
    (zeroSet_isDiscrete Ω f hΩ hf hnonzero) a ⟨ha, hfa⟩
  have haU : a ∈ U := by
    have : a ∈ U ∩ {z | z ∈ Ω ∧ f z = 0} := heq.symm ▸ mem_singleton a
    exact this.1
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hΩ.2.1.inter hU) a ⟨ha, haU⟩
  refine ⟨r, hr, fun z hz => (hball hz).1, ?_⟩
  intro z hz hfz
  have : z ∈ U ∩ {z | z ∈ Ω ∧ f z = 0} :=
    ⟨(hball hz).2, (hball hz).1, hfz⟩
  exact mem_singleton_iff.mp (heq ▸ this)

theorem zeros_finite_on_compact :
    Specs.D12Complex.Ch05.DiscreteCountableZeros.zeros_finite_on_compact_type := by
  intro Ω f hΩ hf hnonzero K hK hKΩ
  by_contra hinfinite
  obtain ⟨a, ha, hacc⟩ := (Set.not_finite.mp hinfinite).exists_accPt_of_subset_isCompact
    hK (fun _ hz => hz.1)
  apply no_accPt_zeros hΩ hf hnonzero (hKΩ ha)
  exact hacc.mono (principal_mono.mpr fun z hz => ⟨hKΩ hz.1, hz.2⟩)

theorem zeros_countable :
    Specs.D12Complex.Ch05.DiscreteCountableZeros.zeros_countable_type := by
  intro Ω f hΩ hf hnonzero
  exact (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    (zeroSet_isDiscrete Ω f hΩ hf hnonzero)

theorem zeros_componentwise :
    Specs.D12Complex.Ch05.DiscreteCountableZeros.zeros_componentwise_type := by
  intro Ω f hf a ha hnonzero
  have hC : IsDomain (connectedComponentIn Ω a) :=
    ⟨⟨a, mem_connectedComponentIn ha⟩, hf.1.connectedComponentIn,
      isPreconnected_connectedComponentIn⟩
  have hfC : HolomorphicOn (connectedComponentIn Ω a) f :=
    ⟨hf.1.connectedComponentIn, fun z hz => hf.2 z (connectedComponentIn_subset Ω a hz)⟩
  exact ⟨zeros_isolated _ f hC hfC hnonzero,
    zeroSet_isDiscrete _ f hC hfC hnonzero,
    zeros_finite_on_compact _ f hC hfC hnonzero,
    zeros_countable _ f hC hfC hnonzero⟩

end D12Complex.DiscreteCountableZeros
