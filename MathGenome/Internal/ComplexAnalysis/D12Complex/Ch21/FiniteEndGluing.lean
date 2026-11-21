import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.FiniteEndGluing
import Mathlib.Topology.Algebra.Module.PerfectSpace
import Mathlib.Topology.Separation.Hausdorff

noncomputable section
open Set Topology

namespace D12Complex.FiniteEndGluing
universe u v w
namespace Data
variable {E : Type u} {J : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace B] (d : Data E J B)

@[simp] theorem psi_center (j : J) : d.psi j (d.center j) = Sum.inr j := by
  simp [psi, center]

@[simp] theorem psi_puncture (j : J) (t : Parameter (d.radius j)) :
    d.psi j (punctureInclusion t) = Sum.inl (d.theta j t) := by
  have ht : (t : ℂ) ≠ 0 := norm_pos_iff.mp t.property.1
  simp [psi, punctureInclusion, ht]

theorem psi_of_ne_zero (j : J) (t : FullDisk (d.radius j)) (ht : (t : ℂ) ≠ 0) :
    d.psi j t = Sum.inl (d.theta j ⟨t, norm_pos_iff.mpr ht,
      by simpa only [Metric.mem_ball, dist_zero_right] using t.property⟩) := by
  simp [psi, ht]

theorem psi_injective (j : J) : Function.Injective (d.psi j) := by
  intro s t h
  by_cases hs : (s : ℂ) = 0
  · have hs' : s = d.center j := Subtype.ext hs
    subst s
    rw [psi_center] at h
    by_cases ht : (t : ℂ) = 0
    · exact (Subtype.ext ht).symm
    · rw [psi_of_ne_zero d j t ht] at h
      cases h
  · by_cases ht : (t : ℂ) = 0
    · have ht' : t = d.center j := Subtype.ext ht
      subst t
      rw [psi_center, psi_of_ne_zero d j s hs] at h
      cases h
    · rw [psi_of_ne_zero d j s hs, psi_of_ne_zero d j t ht] at h
      exact Subtype.ext (congrArg (fun z : Parameter (d.radius j) => (z : ℂ)) ((d.theta_openEmbedding j).injective
        (Sum.inl.inj h)))

theorem range_psi (j : J) :
    range (d.psi j) = Sum.inl '' range (d.theta j) ∪ {Sum.inr j} := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    by_cases ht : (t : ℂ) = 0
    · have h : t = d.center j := Subtype.ext ht
      simp [h]
    · rw [psi_of_ne_zero d j t ht]
      exact Or.inl ⟨_, ⟨_, rfl⟩, rfl⟩
  · rintro (⟨_, ⟨t, rfl⟩, rfl⟩ | h)
    · exact ⟨punctureInclusion t, psi_puncture d j t⟩
    · rw [mem_singleton_iff] at h
      subst x
      exact ⟨d.center j, psi_center d j⟩

@[simp] theorem extendedProjection_inl (x : E) :
    d.extendedProjection (Sum.inl x) = d.projection x := rfl

@[simp] theorem extendedProjection_inr (j : J) :
    d.extendedProjection (Sum.inr j) = d.diskProjection j (d.center j) := rfl

theorem extendedProjection_psi (j : J) :
    d.extendedProjection ∘ d.psi j = d.diskProjection j := by
  funext t
  by_cases ht : (t : ℂ) = 0
  · have h : t = d.center j := Subtype.ext ht
    simp [h]
  · rw [Function.comp_apply, psi_of_ne_zero d j t ht, extendedProjection_inl]
    exact (d.agrees j _).symm

theorem isOpen_iff (U : Set (E ⊕ J)) :
    IsOpen[d.topology] U ↔
      IsOpen ((Sum.inl : E → E ⊕ J) ⁻¹' U) ∧
        ∀ j, IsOpen (d.psi j ⁻¹' U) := by
  exact isOpen_sup.trans (and_congr Iff.rfl
    (isOpen_iSup_iff.trans (forall_congr' fun _ => isOpen_coinduced)))

theorem continuous_extendedProjection :
    @Continuous (E ⊕ J) B d.topology _ d.extendedProjection := by
  let := d.topology
  rw [continuous_def]
  intro U hU
  rw [isOpen_iff]
  refine ⟨d.projection_continuous.isOpen_preimage U hU, fun j => ?_⟩
  have h := (d.diskProjection_continuous j).isOpen_preimage U hU
  simpa only [← preimage_comp, extendedProjection_psi] using h

lemma continuous_iff {Y : Type*} [TopologicalSpace Y] (f : E ⊕ J → Y) :
    Continuous[d.topology, inferInstance] f ↔
      Continuous (f ∘ Sum.inl) ∧ ∀ j, Continuous (f ∘ d.psi j) := by
  exact continuous_sup_dom.trans (and_congr continuous_coinduced_dom
    (continuous_iSup_dom.trans (forall_congr' fun _ => continuous_coinduced_dom)))

lemma punctureInclusion_openEmbedding (r : ℝ) :
    IsOpenEmbedding (@punctureInclusion r) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_subtype_val.subtype_mk _
  · intro x y h; exact Subtype.ext (congrArg (fun z : FullDisk r => (z : ℂ)) h)
  · apply IsOpenMap.subtype_mk
    exact ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const)).isOpenMap_subtype_val

lemma old_preimage_psi_image (j : J) (s : Set (FullDisk (d.radius j))) :
    Sum.inl ⁻¹' (d.psi j '' s) = d.theta j '' (punctureInclusion ⁻¹' s) := by
  ext x
  constructor
  · rintro ⟨t, ht, he⟩
    by_cases h : (t : ℂ) = 0
    · simp [psi, h] at he
    · let t' : Parameter (d.radius j) := ⟨t, norm_pos_iff.mpr h,
        by simpa only [Metric.mem_ball, dist_zero_right] using t.property⟩
      exact ⟨t', ht, by simpa only [psi, dite_eq_right h, Sum.inl.injEq] using he⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨punctureInclusion t, ht, d.psi_puncture j t⟩

lemma psi_preimage_old_image (j : J) (s : Set E) :
    d.psi j ⁻¹' (Sum.inl '' s) = punctureInclusion '' (d.theta j ⁻¹' s) := by
  ext t
  constructor
  · rintro ⟨x, hx, he⟩
    by_cases h : (t : ℂ) = 0
    · simp [psi, h] at he
    · let t' : Parameter (d.radius j) := ⟨t, norm_pos_iff.mpr h,
        by simpa only [Metric.mem_ball, dist_zero_right] using t.property⟩
      refine ⟨t', ?_, rfl⟩
      have he' : x = d.theta j t' := Sum.inl.inj (by simpa only [psi, dite_eq_right h] using he)
      simpa only [mem_preimage, he'] using hx
  · rintro ⟨x, hx, rfl⟩
    exact ⟨d.theta j x, hx, (d.psi_puncture j x).symm⟩

lemma old_openEmbedding : @IsOpenEmbedding E (E ⊕ J) inferInstance d.topology Sum.inl := by
  let := d.topology
  change IsOpenEmbedding Sum.inl
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_le_rng le_sup_left continuous_coinduced_rng
  · exact Sum.inl_injective
  · intro s hs
    apply (d.isOpen_iff _).mpr
    constructor
    · simpa only [Sum.inl_injective.preimage_image] using hs
    · intro j
      rw [d.psi_preimage_old_image]
      exact (punctureInclusion_openEmbedding (d.radius j)).isOpenMap _
        (hs.preimage (d.theta_openEmbedding j).continuous)

lemma psi_preimage_psi_image_of_ne (j k : J) (hjk : j ≠ k)
    (s : Set (FullDisk (d.radius j))) :
    d.psi k ⁻¹' (d.psi j '' s) =
      punctureInclusion '' (d.theta k ⁻¹' (d.theta j '' (punctureInclusion ⁻¹' s))) := by
  rw [← d.psi_preimage_old_image, ← d.old_preimage_psi_image]
  ext t
  constructor
  · rintro ⟨u, hu, he⟩
    by_cases ht : (t : ℂ) = 0
    · by_cases hu0 : (u : ℂ) = 0
      · have : j = k := by simpa only [psi, dite_eq_left ht, dite_eq_left hu0, Sum.inr.injEq] using he
        exact (hjk this).elim
      · simp [psi, ht, hu0] at he
    · refine ⟨d.theta k ⟨t, norm_pos_iff.mpr ht, by simpa only [Metric.mem_ball, dist_zero_right] using t.property⟩, ?_, ?_⟩
      · exact ⟨u, hu, by simpa only [psi, dite_eq_right ht] using he⟩
      · simp only [psi, dite_eq_right ht]
  · rintro ⟨x, ⟨u, hu, he⟩, hx⟩
    exact ⟨u, hu, he.trans hx⟩

lemma psi_openEmbedding (j : J) :
    @IsOpenEmbedding (FullDisk (d.radius j)) (E ⊕ J) inferInstance d.topology (d.psi j) := by
  let := d.topology
  change IsOpenEmbedding (d.psi j)
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_le_rng (le_sup_of_le_right (le_iSup _ j)) continuous_coinduced_rng
  · exact d.psi_injective j
  · intro s hs
    apply (d.isOpen_iff _).mpr
    constructor
    · rw [d.old_preimage_psi_image]
      exact (d.theta_openEmbedding j).isOpenMap _
        (hs.preimage (punctureInclusion_openEmbedding (d.radius j)).continuous)
    · intro k
      by_cases h : j = k
      · subst k
        simpa only [(d.psi_injective j).preimage_image] using hs
      · rw [d.psi_preimage_psi_image_of_ne j k h]
        exact (punctureInclusion_openEmbedding (d.radius k)).isOpenMap _
          (((d.theta_openEmbedding j).isOpenMap _
            (hs.preimage (punctureInclusion_openEmbedding (d.radius j)).continuous)).preimage
            (d.theta_openEmbedding k).continuous)

section ArbitraryTopology
variable [TopologicalSpace (E ⊕ J)]

theorem planeCharts_of_openEmbedding
    (hψ : ∀ j, IsOpenEmbedding (d.psi j)) (j : J) :
    ∃ e : OpenPartialHomeomorph (E ⊕ J) ℂ,
      e.source = range (d.psi j) ∧
      e.target = Metric.ball (0 : ℂ) (d.radius j) ∧
      (∀ t, e (d.psi j t) = (t : ℂ)) ∧
      (∀ t : FullDisk (d.radius j), e.symm (t : ℂ) = d.psi j t) := by
  letI : Nonempty (FullDisk (d.radius j)) := ⟨d.center j⟩
  let a := (hψ j).toOpenPartialHomeomorph (d.psi j)
  let b := (Metric.isOpen_ball : IsOpen (FullDisk (d.radius j))).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph
    (Subtype.val : FullDisk (d.radius j) → ℂ)
  refine ⟨a.symm.trans b, ?_, ?_, ?_, ?_⟩
  · simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      a, b, IsOpenEmbedding.toOpenPartialHomeomorph_target,
      IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  · simp only [OpenPartialHomeomorph.trans_target, OpenPartialHomeomorph.symm_target,
      a, b, IsOpenEmbedding.toOpenPartialHomeomorph_source, preimage_univ, inter_univ,
      IsOpenEmbedding.toOpenPartialHomeomorph_target, Subtype.range_coe]
  · intro t
    simp only [OpenPartialHomeomorph.trans_apply, a, b,
      IsOpenEmbedding.toOpenPartialHomeomorph_left_inv,
      IsOpenEmbedding.toOpenPartialHomeomorph_apply]
  · intro t
    change a (b.symm (t : ℂ)) = d.psi j t
    have hb : b.symm (t : ℂ) = t :=
      (Metric.isOpen_ball : IsOpen (FullDisk (d.radius j))).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv
    rw [hb]
    rfl

theorem isCompact_closedDiskImage_of_continuous
    (hψ : ∀ j, Continuous (d.psi j)) (j : J) {s : ℝ}
    (hs : s < d.radius j) :
    IsCompact (d.psi j '' ((Subtype.val : FullDisk (d.radius j) → ℂ) ⁻¹'
      Metric.closedBall (0 : ℂ) s)) := by
  have hk : IsCompact ((Subtype.val : FullDisk (d.radius j) → ℂ) ⁻¹'
      Metric.closedBall (0 : ℂ) s) := by
    apply IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (isCompact_closedBall (0 : ℂ) s)
    intro t ht
    refine ⟨⟨t, ?_⟩, rfl⟩
    exact lt_of_le_of_lt ht hs
  exact hk.image (hψ j)

end ArbitraryTopology


/-- Inverse parameter charts on the final topology, with the literal disk target. -/
theorem parameter_chart (j : J) :
    let := d.topology
    ∃ e : OpenPartialHomeomorph (E ⊕ J) ℂ,
      e.source = range (d.psi j) ∧
      e.target = Metric.ball (0 : ℂ) (d.radius j) ∧
      (∀ t, e (d.psi j t) = (t : ℂ)) ∧
      (∀ t : FullDisk (d.radius j), e.symm (t : ℂ) = d.psi j t) := by
  let := d.topology
  exact d.planeCharts_of_openEmbedding d.psi_openEmbedding j

theorem compact_parameter_disk (j : J) {s : ℝ} (hs : s < d.radius j) :
    @IsCompact (E ⊕ J) d.topology
      (d.psi j '' ((Subtype.val : FullDisk (d.radius j) → ℂ) ⁻¹'
        Metric.closedBall (0 : ℂ) s)) := by
  let := d.topology
  exact d.isCompact_closedDiskImage_of_continuous
    (fun j => (d.psi_openEmbedding j).continuous) j hs

theorem continuous_closedDiskMap (j : J) (s : ℝ) (hs : s < d.radius j) :
    @Continuous _ _ inferInstance d.topology (d.closedDiskMap j s hs) := by
  let := d.topology
  exact (d.psi_openEmbedding j).continuous.comp
    (continuous_subtype_val.subtype_mk _)

theorem range_closedDiskMap (j : J) (s : ℝ) (hs : s < d.radius j) :
    range (d.closedDiskMap j s hs) =
      d.psi j '' ((Subtype.val : FullDisk (d.radius j) → ℂ) ⁻¹'
        Metric.closedBall (0 : ℂ) s) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨t, lt_of_le_of_lt t.property hs⟩, t.property, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩


theorem dense_old :
    @DenseRange (E ⊕ J) d.topology E Sum.inl := by
  let := d.topology
  intro x
  cases x with
  | inl x => exact subset_closure ⟨x, rfl⟩
  | inr j =>
    rw [mem_closure_iff]
    intro U hU hj
    let V : Set (FullDisk (d.radius j)) := d.psi j ⁻¹' U
    have hV : IsOpen V := hU.preimage (d.psi_openEmbedding j).continuous
    have hW : IsOpen ((Subtype.val : FullDisk (d.radius j) → ℂ) '' V) :=
      Metric.isOpen_ball.isOpenMap_subtype_val V hV
    have h0 : (0 : ℂ) ∈ (Subtype.val : FullDisk (d.radius j) → ℂ) '' V := by
      exact ⟨d.center j, by simpa [V] using hj, rfl⟩
    obtain ⟨z, hz0, hz⟩ := (dense_compl_singleton (0 : ℂ)).exists_mem_open hW ⟨0, h0⟩
    obtain ⟨t, ht, rfl⟩ := hz
    have ht0 : (t : ℂ) ≠ 0 := hz0
    refine ⟨d.psi j t, ht, ?_⟩
    rw [d.psi_of_ne_zero j t ht0]
    exact ⟨_, rfl⟩

theorem connected [ConnectedSpace E]
 :
    @ConnectedSpace (E ⊕ J) d.topology := by
  let := d.topology
  have : PreconnectedSpace (E ⊕ J) := d.dense_old.preconnectedSpace d.old_openEmbedding.continuous
  exact ⟨⟨Sum.inl (Classical.choice inferInstance)⟩⟩

theorem secondCountable [SecondCountableTopology E] [Countable J]
 :
    @SecondCountableTopology (E ⊕ J) d.topology := by
  let := d.topology
  let f : E ⊕ (Σ j, FullDisk (d.radius j)) → E ⊕ J :=
    Sum.elim Sum.inl (fun t => d.psi t.1 t.2)
  have hc : Continuous f := continuous_sum_dom.mpr
    ⟨d.old_openEmbedding.continuous, continuous_sigma fun j => (d.psi_openEmbedding j).continuous⟩
  have ho : IsOpenMap f := d.old_openEmbedding.isOpenMap.sumElim
    (isOpenMap_sigma.mpr fun j => (d.psi_openEmbedding j).isOpenMap)
  have hs : Function.Surjective f := by
    rintro (x | j)
    · exact ⟨Sum.inl x, rfl⟩
    · exact ⟨Sum.inr ⟨j, d.center j⟩, d.psi_center j⟩
  exact (show IsOpenQuotientMap f from ⟨hs, hc, ho⟩).secondCountableTopology


theorem disjoint_range_psi (j k : J) (hjk : j ≠ k)
    (hc : d.diskProjection j (d.center j) = d.diskProjection k (d.center k)) :
    Disjoint (range (d.psi j)) (range (d.psi k)) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rw [d.range_psi j] at hx
  rw [d.range_psi k] at hy
  rcases hx with (⟨y, hyj, rfl⟩ | hx)
  · rcases hy with (⟨z, hzk, he⟩ | hy)
    · have he' : z = y := Sum.inl.inj he
      subst z
      exact Set.disjoint_left.mp (d.disjoint j k hjk hc) hyj hzk
    · cases (show Sum.inl y = Sum.inr k from hy)
  · have hx' : x = Sum.inr j := hx
    subst x
    rcases hy with (⟨z, _, he⟩ | hy)
    · cases he
    · exact hjk (Sum.inr.inj hy)

theorem disjoint_new_nhds (j k : J) (hjk : j ≠ k)
    (hc : d.diskProjection j (d.center j) = d.diskProjection k (d.center k)) :
    Disjoint
      (@nhds (E ⊕ J) d.topology (Sum.inr j))
      (@nhds (E ⊕ J) d.topology (Sum.inr k)) := by
  let := d.topology
  apply Filter.disjoint_of_disjoint_of_mem (d.disjoint_range_psi j k hjk hc)
  · exact (d.psi_openEmbedding j).isOpen_range.mem_nhds ⟨d.center j, d.psi_center j⟩
  · exact (d.psi_openEmbedding k).isOpen_range.mem_nhds ⟨d.center k, d.psi_center k⟩

theorem hausdorff [T2Space E] [T2Space B] :
    @T2Space (E ⊕ J) d.topology := by
  let := d.topology
  apply t2Space_iff_disjoint_nhds.mpr
  rintro (x | j) (y | k) hne
  · rw [← d.old_openEmbedding.map_nhds_eq x, ← d.old_openEmbedding.map_nhds_eq y]
    exact (Filter.disjoint_map Sum.inl_injective).mpr
      (disjoint_nhds_nhds.mpr (fun h => hne (congrArg Sum.inl h)))
  · exact (d.continuous_extendedProjection.tendsto (Sum.inl x)).disjoint
      (disjoint_nhds_nhds.mpr (d.avoids x k))
      (d.continuous_extendedProjection.tendsto (Sum.inr k))
  · exact (d.continuous_extendedProjection.tendsto (Sum.inr j)).disjoint
      (disjoint_nhds_nhds.mpr (Ne.symm (d.avoids y j)))
      (d.continuous_extendedProjection.tendsto (Sum.inl y))
  · by_cases hc : d.diskProjection j (d.center j) = d.diskProjection k (d.center k)
    · exact d.disjoint_new_nhds j k (fun h => hne (congrArg Sum.inr h)) hc
    · exact (d.continuous_extendedProjection.tendsto (Sum.inr j)).disjoint
        (disjoint_nhds_nhds.mpr hc)
        (d.continuous_extendedProjection.tendsto (Sum.inr k))


end Data
/-- Finite-end attachment with all topology, separation, chart and compact-disk
properties required by the algebraic compact-completion construction. -/
theorem finite_end_gluing :
    Specs.D12Complex.Ch21.FiniteEndGluing.finite_end_gluing_type := by
  intro E J B _ _ _ _ _ _ _ d
  let := d.topology
  refine ⟨d.isOpen_iff, d.old_openEmbedding, d.psi_openEmbedding, d.range_psi,
    d.dense_old, d.connected, d.hausdorff, d.secondCountable,
    d.continuous_extendedProjection, d.extendedProjection_inl,
    d.extendedProjection_inr, d.extendedProjection_psi, d.disjoint_range_psi, ?_, ?_⟩
  · intro j
    obtain ⟨e, hsource, htarget, he, heinv⟩ := d.parameter_chart j
    refine ⟨e, hsource, htarget, ?_, he, heinv⟩
    have h0 := he (d.center j)
    rw [d.psi_center j] at h0
    exact h0
  · intro j s _ hs
    refine ⟨d.continuous_closedDiskMap j s hs, d.range_closedDiskMap j s hs,
      d.compact_parameter_disk j hs, ?_⟩
    rw [d.range_closedDiskMap j s hs]
    exact d.compact_parameter_disk j hs

end D12Complex.FiniteEndGluing
