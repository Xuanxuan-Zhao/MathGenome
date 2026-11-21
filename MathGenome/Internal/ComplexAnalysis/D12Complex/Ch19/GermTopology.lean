import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch19.GermTopology
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch19.GermsContinuation

open scoped Topology
open Set Filter
noncomputable section

namespace D12Complex.GermTopology

/-- Candidate-owned exports of the independent canonical constructions. -/
abbrev germSpace : Specs.D12Complex.Ch19.GermTopology.Space_type := Space
abbrev germProjection : Specs.D12Complex.Ch19.GermTopology.projection_type := projection
abbrev germBasicSet : Specs.D12Complex.Ch19.GermTopology.basicSet_type := basicSet
abbrev germBasicSets : Specs.D12Complex.Ch19.GermTopology.basicSets_type := basicSets
abbrev germTopology : Specs.D12Complex.Ch19.GermTopology.topology_type := topology
abbrev representativeSection : Specs.D12Complex.Ch19.GermTopology.sectionMap_type := @sectionMap
abbrev germFamilyLift : Specs.D12Complex.Ch19.GermTopology.lift_type := @lift

theorem germ_equality_persists :
    Specs.D12Complex.Ch19.GermTopology.germ_equality_persists_type := by
  intro a e d he hd h
  obtain ⟨W, ho, ha, hsub, heq⟩ := (elementGerm_eq_iff a e d he hd).mp h
  refine ⟨W, hsub, ho, ha, fun z hz => ?_⟩
  apply germOfFunction_congr
  exact Filter.eventually_of_mem (ho.mem_nhds hz) heq

/-- Restriction to a disk supplies a connected representative. -/
def diskElement (e : FunctionElement) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hsub : Metric.ball a r ⊆ e.domain) : FunctionElement where
  domain := Metric.ball a r
  isDomain := ⟨⟨a, Metric.mem_ball_self hr⟩, Metric.isOpen_ball,
    Metric.isPreconnected_ball⟩
  toFun := e.toFun
  holomorphic := ⟨Metric.isOpen_ball, fun z hz => e.holomorphic.2 z (hsub hz)⟩

lemma basicSet_restrict {Ω : Set ℂ} (e : FunctionElement) (a : ℂ) (r : ℝ)
    (hr : 0 < r) (hsub : Metric.ball a r ⊆ e.domain) :
    basicSet Ω (diskElement e a r hr hsub) ⊆ basicSet Ω e := by
  rintro p ⟨hp, heq⟩
  exact ⟨hsub hp, heq⟩

lemma exists_basicSet (Ω : Set ℂ) (hΩ : IsOpen Ω) (p : Space Ω) :
    ∃ e : FunctionElement, e.domain ⊆ Ω ∧ p ∈ basicSet Ω e := by
  obtain ⟨e, he, heq⟩ := exists_functionElement (p.1 : ℂ) p.2
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    ((e.holomorphic.1.inter hΩ).mem_nhds ⟨he, p.1.property⟩)
  let d := diskElement e p.1 r hr (fun z hz => (hsub hz).1)
  exact ⟨d, fun z hz => (hsub hz).2,
    Metric.mem_ball_self hr, heq.symm⟩

lemma basicSet_inter_refine {Ω : Set ℂ} (e d : FunctionElement)
    (he : e.domain ⊆ Ω) (_hd : d.domain ⊆ Ω) (p : Space Ω)
    (hp : p ∈ basicSet Ω e ∩ basicSet Ω d) :
    ∃ k : FunctionElement, k.domain ⊆ Ω ∧ p ∈ basicSet Ω k ∧
      basicSet Ω k ⊆ basicSet Ω e ∩ basicSet Ω d := by
  obtain ⟨ha, hpa⟩ := hp.1
  obtain ⟨hb, hpb⟩ := hp.2
  obtain ⟨W, hW, ho, haw, heq⟩ :=
    germ_equality_persists p.1 e d ha hb (hpa.symm.trans hpb)
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (ho.mem_nhds haw)
  let k := diskElement e p.1 r hr (fun z hz => (hW (hsub hz)).1)
  refine ⟨k, fun z hz => he ((hW (hsub hz)).1),
    ⟨Metric.mem_ball_self hr, hpa⟩, ?_⟩
  rintro q ⟨hq, hqeq⟩
  exact ⟨⟨(hW (hsub hq)).1, hqeq⟩,
    ⟨(hW (hsub hq)).2, hqeq.trans (heq q.1 (hsub hq))⟩⟩

theorem isTopologicalBasis :
    Specs.D12Complex.Ch19.GermTopology.isTopologicalBasis_type := by
  intro Ω hΩ
  refine ⟨?_, ?_, rfl⟩
  · rintro S ⟨e, he, rfl⟩ T ⟨d, hd, rfl⟩ p hp
    obtain ⟨k, hk, hp, hsub⟩ := basicSet_inter_refine e d he hd p hp
    exact ⟨_, ⟨k, hk, rfl⟩, hp, hsub⟩
  · apply Set.sUnion_eq_univ_iff.mpr
    intro p
    obtain ⟨e, he, hp⟩ := exists_basicSet Ω hΩ p
    exact ⟨_, ⟨e, he, rfl⟩, hp⟩

lemma isOpen_basicSet {Ω : Set ℂ} (e : FunctionElement) (h : e.domain ⊆ Ω) :
    IsOpen (basicSet Ω e) :=
  TopologicalSpace.isOpen_generateFrom_of_mem ⟨e, h, rfl⟩

lemma sectionMap_mem {Ω : Set ℂ} (e : FunctionElement) (h : e.domain ⊆ Ω)
    (z : e.domain) : sectionMap e h z ∈ basicSet Ω e :=
  ⟨z.property, rfl⟩

lemma sectionMap_preimage_open {Ω : Set ℂ} (e d : FunctionElement)
    (h : e.domain ⊆ Ω) : IsOpen (sectionMap e h ⁻¹' basicSet Ω d) := by
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hz, heq⟩
  obtain ⟨W, hW, ho, ha, heqW⟩ :=
    germ_equality_persists z e d z.property hz heq
  have hn : {w : e.domain | (w : ℂ) ∈ W} ∈ 𝓝 z :=
    (ho.preimage continuous_subtype_val).mem_nhds ha
  apply Filter.mem_of_superset hn
  intro w hw
  exact ⟨(hW hw).2, heqW w hw⟩

theorem continuous_sectionMap :
    Specs.D12Complex.Ch19.GermTopology.continuous_sectionMap_type := by
  intro Ω e h
  apply continuous_generateFrom_iff.mpr
  rintro S ⟨d, hd, rfl⟩
  exact sectionMap_preimage_open e d h

/-- A germ neighborhood can be shrunk to lie above any open base neighborhood. -/
lemma refine_over_open {Ω : Set ℂ} (e : FunctionElement) (he : e.domain ⊆ Ω)
    (p : Space Ω) (hp : p ∈ basicSet Ω e) (V : Set ℂ)
    (hV : IsOpen V) (hpV : (p.1 : ℂ) ∈ V) :
    ∃ d : FunctionElement, d.domain ⊆ Ω ∧ p ∈ basicSet Ω d ∧
      basicSet Ω d ⊆ basicSet Ω e ∩ {q | (q.1 : ℂ) ∈ V} := by
  obtain ⟨ha, heq⟩ := hp
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp
    ((e.holomorphic.1.inter hV).mem_nhds ⟨ha, hpV⟩)
  let d := diskElement e p.1 r hr (fun z hz => (hsub hz).1)
  refine ⟨d, fun z hz => he (hsub hz).1,
    ⟨Metric.mem_ball_self hr, heq⟩, ?_⟩
  rintro q ⟨hq, heqq⟩
  exact ⟨⟨(hsub hq).1, heqq⟩, (hsub hq).2⟩

theorem continuous_projection :
    Specs.D12Complex.Ch19.GermTopology.continuous_projection_type := by
  intro Ω hΩ
  apply Continuous.subtype_mk
  rw [continuous_def]
  intro V hV
  apply (isTopologicalBasis Ω hΩ).isOpen_iff.mpr
  intro p hp
  obtain ⟨e, he, hp'⟩ := exists_basicSet Ω hΩ p
  obtain ⟨d, hd, hpd, hsub⟩ := refine_over_open e he p hp' V hV hp
  exact ⟨_, ⟨d, hd, rfl⟩, hpd, fun q hq => (hsub hq).2⟩

/-- The inverse of a section on its image is precisely basepoint projection. -/
def chartEquiv {Ω : Set ℂ} (e : FunctionElement) (h : e.domain ⊆ Ω) :
    basicSet Ω e ≃ e.domain where
  toFun p := ⟨(p.val.1 : ℂ), p.property.choose⟩
  invFun z := ⟨sectionMap e h z, sectionMap_mem e h z⟩
  left_inv := by
    rintro ⟨⟨a, g⟩, hp⟩
    obtain ⟨ha, heq⟩ := hp
    apply Subtype.ext
    change (⟨a, e.germAt a ha⟩ : Space Ω) = ⟨a, g⟩
    change g = e.germAt a ha at heq
    rw [heq]
  right_inv := by intro z; rfl

theorem basic_chart : Specs.D12Complex.Ch19.GermTopology.basic_chart_type := by
  intro Ω hΩ e h
  let E : basicSet Ω e ≃ₜ e.domain :=
    { chartEquiv e h with
      continuous_toFun := Continuous.subtype_mk
        (((continuous_projection Ω hΩ).comp continuous_subtype_val).subtype_val) _
      continuous_invFun := Continuous.subtype_mk (continuous_sectionMap Ω e h) _ }
  exact ⟨E, fun p => rfl⟩

theorem local_projection_chart :
    Specs.D12Complex.Ch19.GermTopology.local_projection_chart_type := by
  intro Ω hΩ p
  obtain ⟨e, he, hp⟩ := exists_basicSet Ω hΩ p
  exact ⟨e, he, hp, isOpen_basicSet e he, basic_chart Ω hΩ e he⟩

theorem locallyRepresented_iff_continuous_lift :
    Specs.D12Complex.Ch19.GermTopology.locallyRepresented_iff_continuous_lift_type := by
  intro Ω hΩ γ hc hγ Φ
  constructor
  · intro hloc
    apply continuous_generateFrom_iff.mpr
    rintro S ⟨d, hd, rfl⟩
    rw [isOpen_iff_mem_nhds]
    intro s hs
    obtain ⟨U, f, hf, hrep⟩ := (locallyRepresented_iff γ Φ).mp hloc s
    obtain ⟨ha, heq⟩ := hrep.self_of_nhds
    obtain ⟨hb, hdeq⟩ := hs
    have heqd : HolomorphicGerm.ofFunction f hf ha = d.germAt (γ s) hb :=
      heq.symm.trans hdeq
    obtain ⟨W, ho, hsW, hW, heqW⟩ :=
      (germOfFunction_eq_iff (γ s) U d.domain f d.toFun hf d.holomorphic ha hb).mp heqd
    have hnear : ∀ᶠ t in 𝓝 s, γ t ∈ W :=
      hc.continuousAt.preimage_mem_nhds (ho.mem_nhds hsW)
    filter_upwards [hnear, hrep] with t ht hrt
    obtain ⟨htU, hΦ⟩ := hrt
    refine ⟨(hW ht).2, hΦ.trans ?_⟩
    apply germOfFunction_congr
    exact Filter.eventually_of_mem (ho.mem_nhds ht) heqW
  · intro hlift
    apply (locallyRepresented_iff γ Φ).mpr
    intro s
    obtain ⟨e, he, hs⟩ := exists_basicSet Ω hΩ (lift γ hγ Φ s)
    have hev : ∀ᶠ t in 𝓝 s, lift γ hγ Φ t ∈ basicSet Ω e :=
      hlift.continuousAt.preimage_mem_nhds ((isOpen_basicSet e he).mem_nhds hs)
    exact ⟨e.domain, e.toFun, e.holomorphic, hev⟩

theorem isContinuation_iff_continuous_lift :
    Specs.D12Complex.Ch19.GermTopology.isContinuation_iff_continuous_lift_type := by
  intro Ω γ hγ φ Φ
  constructor
  · rintro ⟨hΩ, hc, _, hφ, hloc⟩
    exact ⟨hΩ, hc, hφ,
      (locallyRepresented_iff_continuous_lift Ω hΩ.2.1 γ hc hγ Φ).mp hloc⟩
  · rintro ⟨hΩ, hc, hφ, hlift⟩
    exact ⟨hΩ, hc, hγ, hφ,
      (locallyRepresented_iff_continuous_lift Ω hΩ.2.1 γ hc hγ Φ).mpr hlift⟩

end D12Complex.GermTopology
