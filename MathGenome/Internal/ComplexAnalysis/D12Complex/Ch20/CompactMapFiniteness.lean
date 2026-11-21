import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.CompactMapFiniteness
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.MapsMultiplicity

noncomputable section
open Set Filter
open scoped Topology

namespace D12Complex.Surfaces
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- No constant germ can occur in a nonconstant holomorphic surface map. -/
lemma holomorphicMap_not_eventually_constant {S : RiemannSurface X}
    {T : RiemannSurface Y} {f : X → Y} (hf : HolomorphicMap S T f)
    (hnc : ¬ ∃ c, ∀ x, f x = c) (a : X) :
    ¬ ∀ᶠ x in 𝓝 a, f x = f a := by
  intro h
  obtain ⟨U, hU, hoU, haU⟩ := eventually_nhds_iff.mp h
  exact hnc ⟨f a, holomorphicMap_constant_of_open S T f hf U hoU ⟨a, haU⟩ (f a) hU⟩

theorem holomorphicMap_isOpenMap :
    Specs.D12Complex.Ch20.CompactMapFiniteness.holomorphicMap_isOpenMap_type := by
  intro X Y _ _ S T f hf hnc U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨a, haU, rfl⟩
  obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
  obtain ⟨d, hd, hfa⟩ := T.isAtlas.1 (f a)
  have hF := coordinate_holomorphicOn hf (subset_maximalAtlas S.isAtlas he)
    (subset_maximalAtlas T.isAtlas hd)
  let W := coordinateDomain e d f ∩ (e.val.target ∩ e.val.symm ⁻¹' U)
  have hW : IsOpen W := hF.1.inter (e.val.isOpen_inter_preimage_symm hU)
  have haW : e.val a ∈ W :=
    ⟨mem_coordinateDomain ha hfa, e.val.map_source ha, by rwa [mem_preimage, e.val.left_inv ha]⟩
  obtain ⟨m, hm, r, hr, V, φ, ψ, haV, hVW, hpair, hφ, hform, himage, hrest⟩ :=
    LocalMappingNormalForm.local_mapping_normal_form W (coordinateMap e d f) (e.val a)
      ⟨hW, fun z hz => hF.2 z hz.1⟩ haW
      (coordinate_not_eventually_constant hf hnc ha hfa)
  have htarget : coordinateMap e d f '' V ⊆ d.val.target := by
    rintro _ ⟨z, hz, rfl⟩
    exact d.val.map_source (hVW hz).1.2
  have hN := d.val.isOpen_image_symm_of_subset_target
    (show IsOpen (coordinateMap e d f '' V) by rw [himage]; exact Metric.isOpen_ball) htarget
  have haN : f a ∈ d.val.symm '' (coordinateMap e d f '' V) := by
    refine ⟨coordinateMap e d f (e.val a), ⟨e.val a, haV, rfl⟩, ?_⟩
    simp only [coordinateMap, e.val.left_inv ha, d.val.left_inv hfa]
  apply Filter.mem_of_superset (hN.mem_nhds haN)
  rintro _ ⟨w, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨e.val.symm z, (hVW hz).2.2, ?_⟩
  exact (d.val.left_inv (hVW hz).1.2).symm

theorem compact_holomorphicMap_surjective :
    Specs.D12Complex.Ch20.CompactMapFiniteness.compact_holomorphicMap_surjective_type := by
  intro X Y _ _ _ S T f hf hnc
  let := S.connected
  let := T.connected
  let := T.hausdorff
  have hc : IsClosed (range f) := isCompact_range (holomorphicMap_continuous S T f hf) |>.isClosed
  have ho : IsOpen (range f) := (holomorphicMap_isOpenMap S T f hf hnc).isOpen_range
  exact range_eq_univ.mp ((show IsClopen (range f) from ⟨hc, ho⟩).eq_univ (range_nonempty f))

theorem compact_holomorphicMap_finite_fibers :
    Specs.D12Complex.Ch20.CompactMapFiniteness.compact_holomorphicMap_finite_fibers_type := by
  intro X Y _ _ _ S T f hf hnc b
  let := T.hausdorff
  by_contra hfin
  obtain ⟨a, hacc⟩ := (Set.not_finite.mp hfin).exists_accPt_principal
  have hclosed : IsClosed {x | f x = b} :=
    isClosed_singleton.preimage (holomorphicMap_continuous S T f hf)
  have hab : f a = b := by
    have hh := hacc.clusterPt.mem_closure
    rw [hclosed.closure_eq] at hh
    exact hh
  rcases (hf a).constant_or_isolated with hconst | hiso
  · exact holomorphicMap_not_eventually_constant hf hnc a hconst
  · obtain ⟨x, ⟨hx, hxb⟩, hxa⟩ := accPt_iff_nhds.mp hacc _ hiso
    exact hx hxa (hxb.trans hab.symm)

/-- In valid coordinates a nonzero derivative forces multiplicity one. -/
lemma multiplicity_one_of_coordinate_deriv_ne_zero {S : RiemannSurface X}
    {T : RiemannSurface Y} {f : X → Y} (hf : HolomorphicMap S T f)
    {e : ComplexChart X} {d : ComplexChart Y}
    (he : e ∈ maximalAtlas S.atlas) (hd : d ∈ maximalAtlas T.atlas)
    {a : X} (ha : a ∈ e.val.source) (hfa : f a ∈ d.val.source)
    (hder : deriv (coordinateMap e d f) (e.val a) ≠ 0)
    {m : ℕ} (hm : HasMultiplicity S T f a m) : m = 1 := by
  have hg := holomorphicMapAt_chart_independent S T f a (hf a) e he d hd ha hfa
  have hc : coordinateMap e d f (e.val a) = d.val (f a) := by
    simp only [coordinateMap, e.val.left_inv ha]
  have ho : coordinateOrder e d f a = 1 := by
    simpa only [coordinateOrder, hc] using
      hg.analyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hder
  exact ENat.natCast_inj.mp ((hm.2 e he d hd ha hfa).symm.trans ho)

/-- A power-coordinate neighborhood contains no other ramification point.
This rules out accumulation even at points outside the ramification locus. -/
lemma ramification_eventually_absent {S : RiemannSurface X}
    {T : RiemannSurface Y} {f : X → Y} (hf : HolomorphicMap S T f)
    (hnc : ¬ ∃ c, ∀ x, f x = c) (a : X) :
    ∀ᶠ x in 𝓝 a, x ≠ a → x ∉ ramificationLocus S T f := by
  obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
  obtain ⟨d, hd, hfa⟩ := T.isAtlas.1 (f a)
  have heM := subset_maximalAtlas S.isAtlas he
  have hdM := subset_maximalAtlas T.isAtlas hd
  obtain ⟨m, hm, _⟩ := exists_unique_multiplicity S T f hf hnc a
  obtain ⟨r, hr, U, φ, ψ, haU, hU, hpair, hφa, hform⟩ :=
    local_power_form S T f hf hnc a m hm e heM d hdM ha hfa
  have hF := coordinate_holomorphicOn hf heM hdM
  have hnear : ∀ᶠ x in 𝓝 a, x ∈ e.val.source ∧ e.val x ∈ U :=
    Filter.Eventually.and (e.val.open_source.mem_nhds ha)
      ((e.val.continuousAt ha) (hpair.1.1.mem_nhds haU))
  filter_upwards [hnear] with x hx hxa
  have hxD := hU hx.2
  have hxinv : e.val.symm (e.val x) = x := e.val.left_inv hx.1
  have hfx : f x ∈ d.val.source := by
    have hh := hxD.2
    change f (e.val.symm (e.val x)) ∈ d.val.source at hh
    rwa [hxinv] at hh
  have hφx : φ (e.val x) ≠ 0 := by
    intro hzero
    have heq : e.val x = e.val a :=
      (biholomorphicPair_bijOn _ _ _ _ hpair).1.2.1 hx.2 haU (hzero.trans hφa.symm)
    exact hxa (e.val.injOn hx.1 ha heq)
  have hφder := biholomorphicPair_deriv_ne_zero hpair hx.2
  have hdiffF := hF.2 (e.val x) hxD
  have hdiffφ := hpair.1.2 (e.val x) hx.2
  have hevent : (fun z => coordinateMap e d f z - d.val (f a)) =ᶠ[𝓝 (e.val x)]
      (fun z => (φ z)^m) := Filter.Eventually.mono (hpair.1.1.mem_nhds hx.2) hform
  have hderEq : deriv (coordinateMap e d f) (e.val x) =
      (m : ℂ) * φ (e.val x)^(m-1) * deriv φ (e.val x) := by
    have hh := hevent.deriv_eq
    rw [(hdiffF.hasDerivAt.sub_const (d.val (f a))).deriv, (hdiffφ.hasDerivAt.fun_pow m).deriv] at hh
    exact hh
  have hder : deriv (coordinateMap e d f) (e.val x) ≠ 0 := by
    rw [hderEq]
    exact mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm.1))
      (pow_ne_zero _ hφx)) hφder
  rintro ⟨n, hn, hn1⟩
  have hnEq := multiplicity_one_of_coordinate_deriv_ne_zero hf heM hdM hx.1 hfx hder hn
  exact (Nat.ne_of_gt hn1) hnEq

theorem compact_holomorphicMap_finite_ramification :
    Specs.D12Complex.Ch20.CompactMapFiniteness.compact_holomorphicMap_finite_ramification_type := by
  intro X Y _ _ _ S T f hf hnc
  by_contra hfin
  obtain ⟨a, hacc⟩ := (Set.not_finite.mp hfin).exists_accPt_principal
  obtain ⟨x, ⟨hx, hxr⟩, hxa⟩ := accPt_iff_nhds.mp hacc _
    (ramification_eventually_absent hf hnc a)
  exact hx hxa hxr

theorem compact_holomorphicMap_finite_branchValues :
    Specs.D12Complex.Ch20.CompactMapFiniteness.compact_holomorphicMap_finite_branchValues_type := by
  intro X Y _ _ _ S T f hf hnc
  exact (compact_holomorphicMap_finite_ramification S T f hf hnc).image f

end D12Complex.Surfaces

namespace D12Complex.Surfaces.Definitions
abbrev ramificationLocus : Specs.D12Complex.Ch20.CompactMapFiniteness.ramificationLocus_type :=
  @D12Complex.Surfaces.ramificationLocus
abbrev branchValueSet : Specs.D12Complex.Ch20.CompactMapFiniteness.branchValueSet_type :=
  @D12Complex.Surfaces.branchValueSet
end D12Complex.Surfaces.Definitions
