import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch20.MapsMultiplicity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.Surfaces
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalMappingNormalForm
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.ScalarSphereBridge
import Mathlib.Topology.OpenPartialHomeomorph.Continuity

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.Surfaces
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- A transition map is holomorphic on a genuine neighborhood of each overlap point. -/
lemma compatibleCharts_germ {e e' : ComplexChart X} (h : CompatibleCharts e e')
    {a : X} (ha : a ∈ e.val.source) (ha' : a ∈ e'.val.source) :
    HolomorphicGermAt (fun z => e'.val (e.val.symm z)) (e.val a) := by
  let t := e.val.symm.trans e'.val
  have ht : e.val a ∈ t.source := by
    refine ⟨e.val.map_source ha, ?_⟩
    change e.val.symm (e.val a) ∈ e'.val.source
    rwa [e.val.left_inv ha]
  exact ⟨t.source, ht, h.1⟩

/-- Coordinate change is composition with the two biholomorphic transitions;
all inverse cancellations are restricted to actual chart neighborhoods. -/
lemma coordinate_germ_change {e e' : ComplexChart X} {d d' : ComplexChart Y}
    {f : X → Y} {a : X} (hf : ContinuousAt f a)
    (he : CompatibleCharts e' e) (hd : CompatibleCharts d d')
    (ha : a ∈ e.val.source) (ha' : a ∈ e'.val.source)
    (hfa : f a ∈ d.val.source) (hfa' : f a ∈ d'.val.source)
    (h : HolomorphicGermAt (coordinateMap e d f) (e.val a)) :
    HolomorphicGermAt (coordinateMap e' d' f) (e'.val a) := by
  have hs := compatibleCharts_germ he ha' ha
  have ht := compatibleCharts_germ hd hfa hfa'
  have hmid : HolomorphicGermAt (coordinateMap e d f)
      (e.val (e'.val.symm (e'.val a))) := by rwa [e'.val.left_inv ha']
  have hcomp := hmid.comp hs
  have hend : HolomorphicGermAt (fun z => d'.val (d.val.symm z))
      (coordinateMap e d f (e.val (e'.val.symm (e'.val a)))) := by
    simpa only [coordinateMap, e'.val.left_inv ha', e.val.left_inv ha] using ht
  apply (hend.comp (f := fun z => coordinateMap e d f (e.val (e'.val.symm z))) hcomp).congr
  have hsource : ∀ᶠ z in 𝓝 (e'.val a), e'.val.symm z ∈ e.val.source :=
    (e'.val.tendsto_symm ha') (e.val.open_source.mem_nhds ha)
  have htarget : ∀ᶠ z in 𝓝 (e'.val a), f (e'.val.symm z) ∈ d.val.source :=
    (hf.tendsto.comp (e'.val.tendsto_symm ha')) (d.val.open_source.mem_nhds hfa)
  filter_upwards [hsource, htarget] with z hz htz
  simp only [coordinateMap, e.val.left_inv hz, d.val.left_inv htz]

theorem holomorphicMapAt_chart_independent :
    Specs.D12Complex.Ch20.MapsMultiplicity.holomorphicMapAt_chart_independent_type := by
  intro X Y _ _
  rintro S T f a ⟨hc, e, he, d, hd, ha, hfa, hh⟩ e' he' d' hd' ha' hfa'
  exact coordinate_germ_change hc (he' e he)
    (compatibleCharts_symm (hd' d hd)) ha ha' hfa hfa' hh

theorem holomorphicMap_continuous :
    Specs.D12Complex.Ch20.MapsMultiplicity.holomorphicMap_continuous_type := by
  intro X Y _ _ S T f h
  exact continuous_iff_continuousAt.mpr fun a => (h a).1

/-- In coordinate germs a value is either locally constant or isolated.
This is a consequence of weak holomorphy and the proved Taylor bridge. -/
lemma HolomorphicMapAt.constant_or_isolated {S : RiemannSurface X}
    {T : RiemannSurface Y} {f : X → Y} {a : X} (hf : HolomorphicMapAt S T f a) :
    (∀ᶠ x in 𝓝 a, f x = f a) ∨
      ∀ᶠ x in 𝓝 a, x ≠ a → f x ≠ f a := by
  obtain ⟨hc, e, he, d, hd, ha, hfa, hg⟩ := hf
  have hcoord : coordinateMap e d f (e.val a) = d.val (f a) := by
    simp only [coordinateMap, e.val.left_inv ha]
  have hdomain : ∀ᶠ x in 𝓝 a, x ∈ e.val.source ∧ f x ∈ d.val.source :=
    Filter.Eventually.and (e.val.open_source.mem_nhds ha)
      (hc (d.val.open_source.mem_nhds hfa))
  rcases hg.analyticAt.eventually_eq_or_eventually_ne
      (analyticAt_const (v := d.val (f a))) with h | h
  · left
    have hp := (e.val.continuousAt ha) h
    filter_upwards [hdomain, hp] with x hx hxcoord
    have heq : d.val (f x) = d.val (f a) := by
      change coordinateMap e d f (e.val x) = d.val (f a) at hxcoord
      simpa only [coordinateMap, e.val.left_inv hx.1] using hxcoord
    exact d.val.injOn hx.2 hfa heq
  · right
    have hp : ∀ᶠ z in 𝓝 (e.val a), z ≠ e.val a →
        coordinateMap e d f z ≠ d.val (f a) := by
      simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using h
    have hp' := (e.val.continuousAt ha) hp
    filter_upwards [hdomain, hp'] with x hx hxcoord hxa hfx
    apply hxcoord (fun heq => hxa (e.val.injOn hx.1 ha heq))
    simp only [coordinateMap, e.val.left_inv hx.1, hfx]

theorem holomorphicMap_constant_of_open :
    Specs.D12Complex.Ch20.MapsMultiplicity.holomorphicMap_constant_of_open_type := by
  intro X Y _ _ S T f hf U hU hUn c heq
  let := S.connected
  let := T.hausdorff
  let E : Set X := {a | ∀ᶠ x in 𝓝 a, f x = c}
  have ho : IsOpen E := isOpen_iff_eventually.mpr fun a ha =>
    eventually_eventually_nhds.mpr ha
  have hcont := holomorphicMap_continuous S T f hf
  have hc : IsClosed E := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_eventually.mpr
    intro a ha
    change ¬ (∀ᶠ x in 𝓝 a, f x = c) at ha
    by_cases hac : f a = c
    · rcases (hf a).constant_or_isolated with h | h
      · exact (ha (by simpa only [hac] using h)).elim
      · filter_upwards [h] with b hb
        change ¬ (∀ᶠ x in 𝓝 b, f x = c)
        by_cases hba : b = a
        · simpa only [hba] using ha
        · intro hbc
          exact hb hba (hbc.self_of_nhds.trans hac.symm)
    · filter_upwards [(hcont.continuousAt (x := a)).eventually_ne hac] with b hb
      exact fun hbc => hb hbc.self_of_nhds
  obtain ⟨a, haU⟩ := hUn
  have haE : a ∈ E := Filter.Eventually.mono (hU.mem_nhds haU) fun x hx => heq hx
  have hall : E = univ := (show IsClopen E from ⟨hc, ho⟩).eq_univ ⟨a, haE⟩
  intro x
  have hx : x ∈ E := hall ▸ mem_univ x
  exact hx.self_of_nhds

/-- The derivative of a biholomorphic coordinate is nonzero, by the chain rule
applied to its inverse identity. -/
lemma biholomorphicPair_deriv_ne_zero {U V : Set ℂ} {f g : ℂ → ℂ}
    (h : BiholomorphicPair U V f g) {a : ℂ} (ha : a ∈ U) : deriv f a ≠ 0 := by
  have hdf := h.1.2 a ha
  have hdg := h.2.1.2 (f a) (h.2.2.1 ha)
  have heq : (fun z => g (f z)) =ᶠ[𝓝 a] (fun z => z) :=
    Filter.Eventually.mono (h.1.1.mem_nhds ha) fun z hz => h.2.2.2.2.1 hz
  have hd : deriv g (f a) * deriv f a = 1 := by
    have hh := (hdg.hasDerivAt.comp a hdf.hasDerivAt).deriv
    change deriv (fun z => g (f z)) a = _ at hh
    rw [heq.deriv_eq, deriv_id''] at hh
    exact hh.symm
  intro hz
  exact zero_ne_one (by simpa only [hz, mul_zero] using hd)

lemma compatibleCharts_deriv_ne_zero {e e' : ComplexChart X}
    (h : CompatibleCharts e e') {a : X}
    (ha : a ∈ e.val.source) (ha' : a ∈ e'.val.source) :
    deriv (fun z => e'.val (e.val.symm z)) (e.val a) ≠ 0 := by
  apply biholomorphicPair_deriv_ne_zero h
  refine ⟨e.val.map_source ha, ?_⟩
  change e.val.symm (e.val a) ∈ e'.val.source
  rwa [e.val.left_inv ha]

/-- An outer biholomorphic germ does not change the vanishing order. -/
lemma centered_order_comp {F G : ℂ → ℂ} {a : ℂ}
    (hF : HolomorphicGermAt F a) (hG : HolomorphicGermAt G (F a))
    (hG' : deriv G (F a) ≠ 0) :
    analyticOrderAt (fun z => G (F z) - G (F a)) a =
      analyticOrderAt (fun z => F z - F a) a := by
  have ho := hG.analyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hG'
  have hc := (hG.analyticAt.sub (analyticAt_const (v := G (F a)))).analyticOrderAt_comp hF.analyticAt
  change analyticOrderAt (fun z => G (F z) - G (F a)) a =
    analyticOrderAt (fun z => G z - G (F a)) (F a) *
      analyticOrderAt (fun z => F z - F a) a at hc
  simpa only [ho, one_mul] using hc

lemma coordinate_order_change {e e' : ComplexChart X} {d d' : ComplexChart Y}
    {f : X → Y} {a : X} (hf : ContinuousAt f a)
    (he : CompatibleCharts e' e) (hd : CompatibleCharts d d')
    (ha : a ∈ e.val.source) (ha' : a ∈ e'.val.source)
    (hfa : f a ∈ d.val.source) (hfa' : f a ∈ d'.val.source)
    (h : HolomorphicGermAt (coordinateMap e d f) (e.val a)) :
    coordinateOrder e' d' f a = coordinateOrder e d f a := by
  let F := coordinateMap e d f
  let G := fun z => e.val (e'.val.symm z)
  let H := fun z => d'.val (d.val.symm z)
  have hG := compatibleCharts_germ he ha' ha
  have hG' := compatibleCharts_deriv_ne_zero he ha' ha
  have hH := compatibleCharts_germ hd hfa hfa'
  have hH' := compatibleCharts_deriv_ne_zero hd hfa hfa'
  have hGa : G (e'.val a) = e.val a := by simp only [G, e'.val.left_inv ha']
  have hFa : F (e.val a) = d.val (f a) := by simp only [F, coordinateMap, e.val.left_inv ha]
  have hJ : HolomorphicGermAt (fun z => F (G z)) (e'.val a) :=
    (show HolomorphicGermAt F (G (e'.val a)) by rwa [hGa]).comp hG
  have hHa : H (d.val (f a)) = d'.val (f a) := by simp only [H, d.val.left_inv hfa]
  have ho := centered_order_comp hJ
    (show HolomorphicGermAt H (F (G (e'.val a))) by rwa [hGa, hFa])
    (show deriv H (F (G (e'.val a))) ≠ 0 by rwa [hGa, hFa])
  have heq : (fun z => H (F (G z)) - H (F (G (e'.val a)))) =ᶠ[𝓝 (e'.val a)]
      (fun z => coordinateMap e' d' f z - d'.val (f a)) := by
    have hsource : ∀ᶠ z in 𝓝 (e'.val a), e'.val.symm z ∈ e.val.source :=
      (e'.val.tendsto_symm ha') (e.val.open_source.mem_nhds ha)
    have htarget : ∀ᶠ z in 𝓝 (e'.val a), f (e'.val.symm z) ∈ d.val.source :=
      (hf.tendsto.comp (e'.val.tendsto_symm ha')) (d.val.open_source.mem_nhds hfa)
    filter_upwards [hsource, htarget] with z hz htz
    simp only [hGa, hFa, hHa, F, G, H, coordinateMap,
      e.val.left_inv hz, d.val.left_inv htz]
  rw [analyticOrderAt_congr heq] at ho
  rw [hGa, hFa] at ho
  change coordinateOrder e' d' f a = _ at ho
  rw [ho]
  have hs := analyticOrderAt_comp_of_deriv_ne_zero (f := fun z => F z - d.val (f a))
    hG.analyticAt hG'
  change analyticOrderAt (fun z => F (G z) - d.val (f a)) (e'.val a) =
    analyticOrderAt (fun z => F z - d.val (f a)) (G (e'.val a)) at hs
  simpa only [hGa, coordinateOrder, F] using hs

theorem coordinate_order_chart_independent :
    Specs.D12Complex.Ch20.MapsMultiplicity.coordinate_order_chart_independent_type := by
  intro X Y _ _ S T f a hf e he d hd e' he' d' hd' ha hfa ha' hfa'
  have hee := (maximalAtlas_isAtlas S.isAtlas).2 e' he' e he
  have hdd := (maximalAtlas_isAtlas T.isAtlas).2 d hd d' hd'
  exact (coordinate_order_change hf.1 hee hdd ha ha' hfa hfa'
    (holomorphicMapAt_chart_independent S T f a hf e he d hd ha hfa)).symm

lemma coordinateDomain_open {f : X → Y} (hf : Continuous f)
    (e : ComplexChart X) (d : ComplexChart Y) : IsOpen (coordinateDomain e d f) := by
  exact (hf.comp_continuousOn e.val.symm.continuousOn).isOpen_inter_preimage
    e.val.open_target d.val.open_source

lemma mem_coordinateDomain {e : ComplexChart X} {d : ComplexChart Y} {f : X → Y}
    {a : X} (ha : a ∈ e.val.source) (hfa : f a ∈ d.val.source) :
    e.val a ∈ coordinateDomain e d f :=
  ⟨e.val.map_source ha, by
    change f (e.val.symm (e.val a)) ∈ d.val.source
    rwa [e.val.left_inv ha]⟩

/-- On the full overlap of chart domains the representative is plane-holomorphic. -/
lemma coordinate_holomorphicOn {S : RiemannSurface X} {T : RiemannSurface Y}
    {f : X → Y} (hf : HolomorphicMap S T f)
    {e : ComplexChart X} (he : e ∈ maximalAtlas S.atlas)
    {d : ComplexChart Y} (hd : d ∈ maximalAtlas T.atlas) :
    HolomorphicOn (coordinateDomain e d f) (coordinateMap e d f) := by
  refine ⟨coordinateDomain_open (holomorphicMap_continuous S T f hf) e d, ?_⟩
  intro z hz
  have hh := holomorphicMapAt_chart_independent S T f (e.val.symm z)
    (hf _) e he d hd (e.val.map_target hz.1) hz.2
  rw [e.val.right_inv hz.1] at hh
  exact hh.differentiableAt

lemma coordinate_eventually_constant_iff {e : ComplexChart X} {d : ComplexChart Y}
    {f : X → Y} {a : X} (hf : ContinuousAt f a)
    (ha : a ∈ e.val.source) (hfa : f a ∈ d.val.source) :
    (∀ᶠ z in 𝓝 (e.val a), coordinateMap e d f z = d.val (f a)) ↔
      ∀ᶠ x in 𝓝 a, f x = f a := by
  constructor
  · intro h
    have hh : ∀ᶠ x in 𝓝 a, coordinateMap e d f (e.val x) = d.val (f a) :=
      (e.val.continuousAt ha) h
    filter_upwards [hh, e.val.open_source.mem_nhds ha,
      hf (d.val.open_source.mem_nhds hfa)] with x hx hxe hxd
    exact d.val.injOn hxd hfa (by simpa only [coordinateMap, e.val.left_inv hxe] using hx)
  · intro h
    filter_upwards [(e.val.tendsto_symm ha) h] with z hz
    change f (e.val.symm z) = f a at hz
    simp only [coordinateMap, hz]

lemma coordinate_not_eventually_constant {S : RiemannSurface X} {T : RiemannSurface Y}
    {f : X → Y} (hf : HolomorphicMap S T f) (hnc : ¬ ∃ c, ∀ x, f x = c)
    {a : X} {e : ComplexChart X} {d : ComplexChart Y}
    (ha : a ∈ e.val.source) (hfa : f a ∈ d.val.source) :
    ¬ ∀ᶠ z in 𝓝 (e.val a), coordinateMap e d f z = coordinateMap e d f (e.val a) := by
  intro h
  have hcoord : coordinateMap e d f (e.val a) = d.val (f a) := by
    simp only [coordinateMap, e.val.left_inv ha]
  rw [hcoord] at h
  have hlocal := (coordinate_eventually_constant_iff (hf a).1 ha hfa).mp h
  obtain ⟨U, hU, hoU, haU⟩ := eventually_nhds_iff.mp hlocal
  exact hnc ⟨f a, holomorphicMap_constant_of_open S T f hf U hoU ⟨a, haU⟩ (f a) hU⟩

theorem exists_unique_multiplicity :
    Specs.D12Complex.Ch20.MapsMultiplicity.exists_unique_multiplicity_type := by
  intro X Y _ _ S T f hf hnc a
  obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
  obtain ⟨d, hd, hfa⟩ := T.isAtlas.1 (f a)
  have heM := subset_maximalAtlas S.isAtlas he
  have hdM := subset_maximalAtlas T.isAtlas hd
  obtain ⟨m, hm, r, hr, U, φ, ψ, hU, hUΩ, hpair, hφ0, hform, horder⟩ :=
    LocalMappingNormalForm.exists_power_coordinate _ _ _
      (coordinate_holomorphicOn hf heM hdM) (mem_coordinateDomain ha hfa)
      (coordinate_not_eventually_constant hf hnc ha hfa)
  have hmorder : coordinateOrder e d f a = (m : ℕ∞) := by
    simpa only [coordinateOrder, coordinateMap, e.val.left_inv ha] using horder
  refine ⟨m, ⟨hm, ?_⟩, ?_⟩
  · intro e' he' d' hd' ha' hfa'
    exact (coordinate_order_chart_independent S T f a (hf a)
      e' he' d' hd' e heM d hdM ha' hfa' ha hfa).trans hmorder
  · intro n hn
    exact ENat.natCast_inj.mp ((hn.2 e heM d hdM ha hfa).symm.trans hmorder)

theorem local_power_form :
    Specs.D12Complex.Ch20.MapsMultiplicity.local_power_form_type := by
  intro X Y _ _ S T f hf hnc a m hm e he d hd ha hfa
  obtain ⟨n, hn, r, hr, U, φ, ψ, hU, hUΩ, hpair, hφ0, hform, horder⟩ :=
    LocalMappingNormalForm.exists_power_coordinate _ _ _
      (coordinate_holomorphicOn hf he hd) (mem_coordinateDomain ha hfa)
      (coordinate_not_eventually_constant hf hnc ha hfa)
  have hcoord : coordinateMap e d f (e.val a) = d.val (f a) := by
    simp only [coordinateMap, e.val.left_inv ha]
  have hnorder : coordinateOrder e d f a = (n : ℕ∞) := by
    simpa only [coordinateOrder, hcoord] using horder
  have hnm : n = m := ENat.natCast_inj.mp (hnorder.symm.trans (hm.2 e he d hd ha hfa))
  subst n
  exact ⟨r, hr, U, φ, ψ, hU, hUΩ, hpair, hφ0, by simpa only [hcoord] using hform⟩

lemma centered_order_one_deriv_ne_zero {F : ℂ → ℂ} {a : ℂ}
    (hF : HolomorphicGermAt F a)
    (ho : analyticOrderAt (fun z => F z - F a) a = 1) : deriv F a ≠ 0 := by
  have hA : AnalyticAt ℂ (fun z => F z - F a) a :=
    hF.analyticAt.sub (analyticAt_const (v := F a))
  obtain ⟨g, hg, hg0, heq⟩ := hA.analyticOrderAt_eq_natCast.mp ho
  have heq' : (fun z => F z - F a) =ᶠ[𝓝 a] (fun z => (z-a) * g z) := by
    filter_upwards [heq] with z hz
    simpa only [pow_one, smul_eq_mul] using hz
  have hder : deriv F a = g a := by
    calc
      deriv F a = deriv (fun z => F z - F a) a := by simp
      _ = deriv (fun z => (z-a) * g z) a := heq'.deriv_eq
      _ = g a := by
        rw [deriv_fun_mul (by fun_prop) hg.differentiableAt]
        simp
  rwa [hder]

theorem locally_biholomorphic_iff_multiplicity_one :
    Specs.D12Complex.Ch20.MapsMultiplicity.locally_biholomorphic_iff_multiplicity_one_type := by
  intro X Y _ _ S T f hf hnc a m hm
  constructor
  · rintro ⟨e, he, d, hd, ha, hfa, U, V, g, haU, hU, hV, hpair⟩
    have hder := biholomorphicPair_deriv_ne_zero hpair haU
    have hg : HolomorphicGermAt (coordinateMap e d f) (e.val a) := ⟨U, haU, hpair.1⟩
    have hc : coordinateMap e d f (e.val a) = d.val (f a) := by
      simp only [coordinateMap, e.val.left_inv ha]
    have horder : coordinateOrder e d f a = 1 := by
      simpa only [coordinateOrder, hc] using
        hg.analyticAt.analyticOrderAt_sub_eq_one_of_deriv_ne_zero hder
    exact ENat.natCast_inj.mp ((hm.2 e (subset_maximalAtlas S.isAtlas he)
      d (subset_maximalAtlas T.isAtlas hd) ha hfa).symm.trans horder)
  · intro hm1
    obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
    obtain ⟨d, hd, hfa⟩ := T.isAtlas.1 (f a)
    have heM := subset_maximalAtlas S.isAtlas he
    have hdM := subset_maximalAtlas T.isAtlas hd
    have hF := coordinate_holomorphicOn hf heM hdM
    have haΩ := mem_coordinateDomain ha hfa
    have hg : HolomorphicGermAt (coordinateMap e d f) (e.val a) :=
      ⟨coordinateDomain e d f, haΩ, hF⟩
    have hc : coordinateMap e d f (e.val a) = d.val (f a) := by
      simp only [coordinateMap, e.val.left_inv ha]
    have horder : analyticOrderAt
        (fun z => coordinateMap e d f z - coordinateMap e d f (e.val a)) (e.val a) = 1 := by
      simpa only [coordinateOrder, hc, hm1, Nat.cast_one] using hm.2 e heM d hdM ha hfa
    obtain ⟨U, V, g, haU, hfaV, hU, hpair, hder, hinvder⟩ :=
      LocalHolomorphicInverse.local_holomorphic_inverse _ _ _ hF haΩ
        (centered_order_one_deriv_ne_zero hg horder)
    refine ⟨e, he, d, hd, ha, hfa, U, V, g, haU, hU, ?_, hpair⟩
    intro w hw
    have hzU := hpair.2.2.2.1 hw
    have hzΩ := hU hzU
    have hr := hpair.2.2.2.2.2 hw
    rw [← hr]
    exact d.val.map_source hzΩ.2

theorem scalarMeromorphic_not_constant_infty :
    Specs.D12Complex.Ch20.MapsMultiplicity.scalarMeromorphic_not_constant_infty_type := by
  intro X _ S h
  let := S.connected
  obtain ⟨a⟩ := (inferInstance : Nonempty X)
  obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
  obtain ⟨b, hb, hfin⟩ := (h e he).2.2.2.2.2 (e.val a) (e.val.map_source ha)
  exact hfin rfl

theorem holomorphicMapAt_iff_chart :
    Specs.D12Complex.Ch20.MapsMultiplicity.holomorphicMapAt_iff_chart_type := by
  intro X Y _ _ S T f a e he d hd ha hfa
  refine ⟨fun hf => ⟨hf.1, holomorphicMapAt_chart_independent S T f a hf e he d hd ha hfa⟩, ?_⟩
  rintro ⟨hc, hh⟩
  obtain ⟨e', he', ha'⟩ := S.isAtlas.1 a
  obtain ⟨d', hd', hfa'⟩ := T.isAtlas.1 (f a)
  exact ⟨hc, e', he', d', hd', ha', hfa', coordinate_germ_change hc
    (compatibleCharts_symm (he e' he')) (hd d' hd') ha ha' hfa hfa' hh⟩

theorem scalarHolomorphic_chart_independent :
    Specs.D12Complex.Ch20.MapsMultiplicity.scalarHolomorphic_chart_independent_type := by
  intro X _ S f hf e he
  refine ⟨e.val.open_target, ?_⟩
  intro z hz
  obtain ⟨d, hd, hx⟩ := S.isAtlas.1 (e.val.symm z)
  have hx' := e.val.map_target hz
  have hg := compatibleCharts_germ (he d hd) hx' hx
  rw [e.val.right_inv hz] at hg
  have hfd : HolomorphicGermAt (f ∘ d.val.symm) (d.val (e.val.symm z)) :=
    ⟨d.val.target, d.val.map_source hx, hf.2 d hd⟩
  have hh := hfd.comp hg
  have heq : (fun w => (f ∘ d.val.symm) (d.val (e.val.symm w))) =ᶠ[𝓝 z]
      (f ∘ e.val.symm) := by
    filter_upwards [(e.val.continuousAt_symm hz) (d.val.open_source.mem_nhds hx)] with w hw
    change e.val.symm w ∈ d.val.source at hw
    simp only [Function.comp_def, d.val.left_inv hw]
  exact (hh.congr heq).differentiableAt

lemma planeSphereHolomorphicAt_comp {F : ℂ → RiemannSphere} {g : ℂ → ℂ} {a : ℂ}
    (hF : PlaneSphereHolomorphicAt F (g a)) (hg : HolomorphicGermAt g a) :
    PlaneSphereHolomorphicAt (F ∘ g) a := by
  obtain ⟨hc, d, hd, hh⟩ := hF
  exact ⟨hc.comp hg.differentiableAt.continuousAt, d, hd, hh.comp hg⟩

/-- Source-coordinate invariance for sphere-valued scalar expressions. -/
lemma sphere_coordinate_holomorphic {S : RiemannSurface X} {F : X → RiemannSphere}
    (h : ∀ e ∈ S.atlas, PlaneSphereHolomorphicOn e.val.target (F ∘ e.val.symm))
    {e : ComplexChart X} (he : e ∈ maximalAtlas S.atlas) :
    PlaneSphereHolomorphicOn e.val.target (F ∘ e.val.symm) := by
  refine ⟨e.val.open_target, ?_⟩
  intro z hz
  obtain ⟨d, hd, hx⟩ := S.isAtlas.1 (e.val.symm z)
  have hg := compatibleCharts_germ (he d hd) (e.val.map_target hz) hx
  rw [e.val.right_inv hz] at hg
  have hfd := (h d hd).2 (d.val (e.val.symm z)) (d.val.map_source hx)
  have hh := planeSphereHolomorphicAt_comp hfd hg
  apply hh.congr
  filter_upwards [(e.val.continuousAt_symm hz) (d.val.open_source.mem_nhds hx)] with w hw
  change e.val.symm w ∈ d.val.source at hw
  simp only [Function.comp_def, d.val.left_inv hw]

lemma scalarMeromorphic_coordinate_holomorphic {S : RiemannSurface X}
    {F : X → RiemannSphere} (h : ScalarMeromorphic S F) :
    ∀ e ∈ S.atlas, PlaneSphereHolomorphicOn e.val.target (F ∘ e.val.symm) := by
  intro e he
  exact (plane_scalar_sphere_bridge _ _ e.property).mpr (Or.inl (h e he))

/-- Scalar meromorphy excludes even a local neighborhood identically infinity. -/
lemma scalarMeromorphic_no_infty_germ {S : RiemannSurface X}
    {F : X → RiemannSphere} (h : ScalarMeromorphic S F) (a : X) :
    ¬ ∀ᶠ x in 𝓝 a, F x = sphereInfty := by
  intro hinf
  obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
  have hplane := scalarMeromorphic_coordinate_holomorphic h e he
  have hnot : ¬ EqOn (F ∘ e.val.symm) (fun _ => sphereInfty) e.val.target := by
    intro hh
    obtain ⟨b, hb, hfin⟩ := (h e he).2.2.2.2.2 (e.val a) (e.val.map_source ha)
    exact hfin (hh (connectedComponentIn_subset _ _ hb))
  have hi : ∀ᶠ z in 𝓝 (e.val a), (F ∘ e.val.symm) z = sphereInfty :=
    (e.val.tendsto_symm ha) hinf
  exact plane_no_infty_germ e.property hplane hnot (e.val a) (e.val.map_source ha) hi

theorem scalarMeromorphic_chart_independent :
    Specs.D12Complex.Ch20.MapsMultiplicity.scalarMeromorphic_chart_independent_type := by
  intro X _ S F h e he
  have hplane := sphere_coordinate_holomorphic (scalarMeromorphic_coordinate_holomorphic h) he
  rcases (plane_scalar_sphere_bridge _ _ e.property).mp hplane with hM | hInf
  · exact hM
  · obtain ⟨z, hz⟩ := e.property.1
    apply False.elim
    apply scalarMeromorphic_no_infty_germ h (e.val.symm z)
    filter_upwards [e.val.open_source.mem_nhds (e.val.map_target hz)] with x hx
    have hh := hInf (e.val.map_source hx)
    simpa only [Function.comp_def, e.val.left_inv hx] using hh

theorem scalarMeromorphic_sphereValuedHolomorphic :
    Specs.D12Complex.Ch20.MapsMultiplicity.scalarMeromorphic_sphereValuedHolomorphic_type := by
  intro X _ S F h
  have hplane := scalarMeromorphic_coordinate_holomorphic h
  refine ⟨continuous_iff_continuousAt.mpr fun a => ?_, hplane⟩
  obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
  have hc := ((hplane e he).2 (e.val a) (e.val.map_source ha)).1.comp (e.val.continuousAt ha)
  apply hc.congr_of_eventuallyEq
  filter_upwards [e.val.open_source.mem_nhds ha] with x hx
  simp only [Function.comp_def, e.val.left_inv hx]

theorem scalarHolomorphicOnSurface_univ :
    Specs.D12Complex.Ch20.MapsMultiplicity.scalarHolomorphicOnSurface_univ_type := by
  intro X _ S f
  simp only [ScalarHolomorphicOnSurface, ScalarHolomorphic, chartDomain,
    preimage_univ, inter_univ, isOpen_univ, true_and, continuousOn_univ]

theorem scalarMeromorphicOnSurface_univ :
    Specs.D12Complex.Ch20.MapsMultiplicity.scalarMeromorphicOnSurface_univ_type := by
  intro X _ S F
  simp only [ScalarMeromorphicOnSurface, ScalarMeromorphic, chartDomain,
    preimage_univ, inter_univ, isOpen_univ, true_and]

theorem scalarMeromorphicOnSurface_not_infty :
    Specs.D12Complex.Ch20.MapsMultiplicity.scalarMeromorphicOnSurface_not_infty_type := by
  rintro X _ S Ω ⟨a, haΩ⟩ h
  obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
  have hz : e.val a ∈ chartDomain e Ω :=
    ⟨e.val.map_source ha, by simpa only [mem_preimage, e.val.left_inv ha] using haΩ⟩
  obtain ⟨b, hb, hfin⟩ := (h.2 e he).2.2.2.2.2 (e.val a) hz
  exact hfin rfl

theorem sphereValuedHolomorphic_const :
    Specs.D12Complex.Ch20.MapsMultiplicity.sphereValuedHolomorphic_const_type := by
  intro X _ S c
  refine ⟨continuous_const, fun e he => ?_⟩
  exact planeSphereHolomorphicOn_const _ c e.val.open_target

end D12Complex.Surfaces

namespace D12Complex.Surfaces.Definitions

abbrev coordinateMap : Specs.D12Complex.Ch20.MapsMultiplicity.coordinateMap_type :=
  @D12Complex.Surfaces.coordinateMap

abbrev HolomorphicMapAt : Specs.D12Complex.Ch20.MapsMultiplicity.HolomorphicMapAt_type :=
  @D12Complex.Surfaces.HolomorphicMapAt

abbrev HolomorphicMap : Specs.D12Complex.Ch20.MapsMultiplicity.HolomorphicMap_type :=
  @D12Complex.Surfaces.HolomorphicMap

abbrev ScalarHolomorphic : Specs.D12Complex.Ch20.MapsMultiplicity.ScalarHolomorphic_type :=
  @D12Complex.Surfaces.ScalarHolomorphic

abbrev ScalarMeromorphic : Specs.D12Complex.Ch20.MapsMultiplicity.ScalarMeromorphic_type :=
  @D12Complex.Surfaces.ScalarMeromorphic

abbrev SphereValuedHolomorphic : Specs.D12Complex.Ch20.MapsMultiplicity.SphereValuedHolomorphic_type :=
  @D12Complex.Surfaces.SphereValuedHolomorphic

abbrev coordinateDomain : Specs.D12Complex.Ch20.MapsMultiplicity.coordinateDomain_type :=
  @D12Complex.Surfaces.coordinateDomain

abbrev coordinateOrder : Specs.D12Complex.Ch20.MapsMultiplicity.coordinateOrder_type :=
  @D12Complex.Surfaces.coordinateOrder

abbrev HasMultiplicity : Specs.D12Complex.Ch20.MapsMultiplicity.HasMultiplicity_type :=
  @D12Complex.Surfaces.HasMultiplicity

abbrev PowerCoordinates : Specs.D12Complex.Ch20.MapsMultiplicity.PowerCoordinates_type :=
  @D12Complex.Surfaces.PowerCoordinates

abbrev LocallyBiholomorphicAt : Specs.D12Complex.Ch20.MapsMultiplicity.LocallyBiholomorphicAt_type :=
  @D12Complex.Surfaces.LocallyBiholomorphicAt

abbrev chartDomain : Specs.D12Complex.Ch20.MapsMultiplicity.chartDomain_type :=
  @D12Complex.Surfaces.chartDomain

abbrev ScalarHolomorphicOnSurface : Specs.D12Complex.Ch20.MapsMultiplicity.ScalarHolomorphicOnSurface_type :=
  @D12Complex.Surfaces.ScalarHolomorphicOnSurface

abbrev ScalarMeromorphicOnSurface : Specs.D12Complex.Ch20.MapsMultiplicity.ScalarMeromorphicOnSurface_type :=
  @D12Complex.Surfaces.ScalarMeromorphicOnSurface

end D12Complex.Surfaces.Definitions
