import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.OmegaOneOpen
import MathGenome.Internal.PointSetTopology.D10Topology.Ch18.OrdinalCompact
import MathGenome.Internal.PointSetTopology.D10Topology.Ch05.CountableCompactness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch08.CountabilityConventions
import MathGenome.Internal.PointSetTopology.D10Topology.Ch11.LocalCompactConventions
import Mathlib.Topology.Order.Compact

open Set Filter Topology
open scoped Ordinal

namespace D10Topology.Ch18

abbrev OmegaOneOpen := Specs.D10Topology.Ch18.OmegaOneOpen.Y

theorem omegaOneOpen_orderTopology_eq_subspace :
    Ch01.orderTopology OmegaOneOpen = (inferInstance : TopologicalSpace OmegaOneOpen) := by
  exact (OrderTopology.topology_eq_generate_intervals (α := OmegaOneOpen)).symm

local instance : Nonempty OmegaOneOpen := ⟨⟨0, Ordinal.omega_pos 1⟩⟩

theorem omegaOneOpen_succ_lt (x : OmegaOneOpen) : x.val + 1 < (ω₁ : Ordinal.{0}) :=
  (Cardinal.isSuccLimit_omega 1).add_one_lt x.prop

theorem omegaOneOpen_isCompact_Iic (x : OmegaOneOpen) : IsCompact (Iic x) := by
  apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
  have he : Subtype.val '' (Iic x : Set OmegaOneOpen) = Icc (0 : Ordinal.{0}) x.val := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨zero_le, hb⟩
    · intro ha
      exact ⟨⟨a, ha.2.trans_lt x.prop⟩, ha.2, rfl⟩
  rw [he]
  exact isCompact_Icc

/-- Every countable set of countable ordinals has a countable upper bound (F4). -/
theorem omegaOneOpen_countable_bounded (S : Set OmegaOneOpen) (hS : S.Countable) :
    ∃ b : OmegaOneOpen, ∀ x ∈ S, x ≤ b := by
  let := hS.to_subtype
  let f : S → Ordinal.{0} := fun x => x.val.val
  refine ⟨⟨⨆ i, f i, Ordinal.iSup_lt_omega_one (fun i => i.val.prop)⟩, ?_⟩
  intro x hx
  exact Ordinal.le_iSup f ⟨x, hx⟩

/-- A closed initial interval is also open: it ends immediately before a successor. -/
theorem omegaOneOpen_isOpen_Iic (x : OmegaOneOpen) : IsOpen (Iic x) := by
  have he : (Iic x : Set OmegaOneOpen) =
      Subtype.val ⁻¹' Iio (x.val + 1) := by
    ext y
    change y.val ≤ x.val ↔ y.val < x.val + 1
    exact Order.lt_add_one_iff.symm
  rw [he]
  exact isOpen_Iio.preimage continuous_subtype_val

/-- Initial intervals below any fixed countable ordinal are countable. -/
theorem omegaOneOpen_countable_Iic (x : OmegaOneOpen) : (Iic x).Countable := by
  have h := (Cardinal.countable_Iio_of_lt_omega_one (omegaOneOpen_succ_lt x)).preimage
    (f := (Subtype.val : OmegaOneOpen → Ordinal.{0})) Subtype.val_injective
  apply h.mono
  intro y hy
  change y.val < x.val + 1
  exact Order.lt_add_one_iff.mpr (show y.val ≤ x.val from hy)

/-- Each point has a countable open ordered neighborhood, hence a countable local base. -/
theorem omegaOneOpen_firstCountable_mathlib : FirstCountableTopology OmegaOneOpen := by
  constructor
  intro x
  let := (omegaOneOpen_countable_Iic x).to_subtype
  let : OrderTopology (Iic x) := inferInstance
  let : FirstCountableTopology (Iic x) := inferInstance
  have he := (omegaOneOpen_isOpen_Iic x).isOpenEmbedding_subtypeVal
  rw [← he.map_nhds_eq ⟨x, mem_Iic.mpr le_rfl⟩]
  infer_instance

theorem omegaOneOpen_firstCountable :
    Ch04.FirstCountable (inferInstance : TopologicalSpace OmegaOneOpen) :=
  Ch08.firstCountable_iff_mathlib.mpr omegaOneOpen_firstCountable_mathlib

theorem omegaOneOpen_locallyCompact : Ch11.LocallyCompact OmegaOneOpen := by
  intro x
  exact ⟨Iic x, omegaOneOpen_isCompact_Iic x, Iic x,
    omegaOneOpen_isOpen_Iic x, mem_Iic.mpr le_rfl, Subset.rfl⟩

/-- A sequence lies in a compact initial interval, where it has a cluster point. -/
theorem omegaOneOpen_isCountablyCompact : IsCountablyCompact (univ : Set OmegaOneOpen) := by
  apply IsCountablyCompact.of_seq_clusterPt
  intro a _
  obtain ⟨b, hb⟩ := omegaOneOpen_countable_bounded (range a) (countable_range a)
  obtain ⟨x, _, hx⟩ := (omegaOneOpen_isCompact_Iic b).exists_mapClusterPt
    (f := atTop) (u := a) (tendsto_principal.mpr (Eventually.of_forall
      (fun n => hb (a n) (mem_range_self n))))
  exact ⟨x, mem_univ x, hx⟩

theorem omegaOneOpen_countablyCompact : Ch05.CountableCoverCompact OmegaOneOpen :=
  (Ch05.countableCoverCompact_iff_isCountablyCompact_univ OmegaOneOpen).mpr
    omegaOneOpen_isCountablyCompact

theorem omegaOneOpen_sequentiallyCompact : Ch05.SequentiallyCompact OmegaOneOpen :=
  (Ch05.firstCountable_countableCoverCompact_iff_sequentiallyCompact
    OmegaOneOpen omegaOneOpen_firstCountable).mp omegaOneOpen_countablyCompact

/-- Compactness bounds the set inside Y itself, so the bound is countable. -/
theorem omegaOneOpen_compact_subset_bounded (K : Set OmegaOneOpen) (hK : IsCompact K) :
    ∃ β : Ordinal.{0}, β < ω₁ ∧ ∀ x ∈ K, (x : Ordinal.{0}) ≤ β := by
  obtain ⟨b, hb⟩ := hK.bddAbove
  exact ⟨b.val, b.prop, hb⟩

theorem omegaOneOpen_not_compact : ¬ Ch05.CoverCompact OmegaOneOpen := by
  intro h
  have hK : IsCompact (univ : Set OmegaOneOpen) :=
    (Ch05.coverCompact_iff_isCompact_univ OmegaOneOpen).mp h
  obtain ⟨β, hβ, hb⟩ := omegaOneOpen_compact_subset_bounded univ hK
  let b : OmegaOneOpen := ⟨β, hβ⟩
  have hc := hb ⟨β + 1, omegaOneOpen_succ_lt b⟩ (mem_univ _)
  exact (lt_add_one β).not_ge hc

theorem omegaOneOpen_not_lindelof : ¬ LindelofSpace OmegaOneOpen := by
  intro h
  apply omegaOneOpen_not_compact
  apply (Ch05.coverCompact_iff_isCompact_univ OmegaOneOpen).mpr
  exact IsLindelof.isCompact omegaOneOpen_isCountablyCompact h.isLindelof_univ

theorem omegaOneOpen_not_sigmaCompact : ¬ Ch11.SigmaCompact OmegaOneOpen := by
  intro h
  let : SigmaCompactSpace OmegaOneOpen :=
    (Ch11.sigmaCompact_iff_sigmaCompactSpace OmegaOneOpen).mp h
  exact omegaOneOpen_not_lindelof inferInstance

end D10Topology.Ch18
