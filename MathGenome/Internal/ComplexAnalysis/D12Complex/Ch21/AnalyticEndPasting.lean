import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch21.AnalyticEndPasting
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch21.FiniteEndGluing
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch20.MapsMultiplicity
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.LocalQuotientsArithmetic

noncomputable section
open Set Filter Topology
namespace D12Complex.AnalyticEndPasting
open Surfaces FiniteEndGluing

universe u v w
variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]

@[simp] theorem transportChart_source {i : E → X} (hi : IsOpenEmbedding i)
    (e : ComplexChart E) : (transportChart hi e).val.source = i '' e.val.source := rfl

@[simp] theorem transportChart_target {i : E → X} (hi : IsOpenEmbedding i)
    (e : ComplexChart E) : (transportChart hi e).val.target = e.val.target := rfl

@[simp] theorem transportChart_apply {i : E → X} (hi : IsOpenEmbedding i)
    (e : ComplexChart E) (x : E) : (transportChart hi e).val (i x) = e.val x :=
  e.val.lift_openEmbedding_apply hi

@[simp] theorem transportChart_symm_apply {i : E → X} (hi : IsOpenEmbedding i)
    (e : ComplexChart E) (z : ℂ) : (transportChart hi e).val.symm z = i (e.val.symm z) := rfl

@[simp] theorem transportChart_transition {i : E → X} (hi : IsOpenEmbedding i)
    (e f : ComplexChart E) :
    (transportChart hi e).val.symm.trans (transportChart hi f).val =
      e.val.symm.trans f.val := e.val.lift_openEmbedding_trans f.val hi

theorem transportChart_compatible_iff {i : E → X} (hi : IsOpenEmbedding i)
    (e f : ComplexChart E) :
    CompatibleCharts (transportChart hi e) (transportChart hi f) ↔ CompatibleCharts e f := by
  simp only [CompatibleCharts, transportChart_transition]

theorem transportChart_mem_source_iff {i : E → X} (hi : IsOpenEmbedding i)
    (e : ComplexChart E) (x : E) :
    i x ∈ (transportChart hi e).val.source ↔ x ∈ e.val.source := by
  simp only [transportChart_source, hi.injective.mem_set_image]

/-- Ordered transition differentiability at each actual overlap point suffices. -/
theorem compatibleCharts_of_germs (e f : ComplexChart X)
    (h : ∀ x ∈ e.val.source, x ∈ f.val.source →
      HolomorphicGermAt (fun z => f.val (e.val.symm z)) (e.val x))
    (h' : ∀ x ∈ f.val.source, x ∈ e.val.source →
      HolomorphicGermAt (fun z => e.val (f.val.symm z)) (f.val x)) :
    CompatibleCharts e f := by
  let t := e.val.symm.trans f.val
  refine ⟨⟨t.open_source, ?_⟩, ⟨t.open_target, ?_⟩,
    t.mapsTo, t.symm.mapsTo, t.leftInvOn, t.rightInvOn⟩
  · intro z hz
    have hx := e.val.map_target hz.1
    have hh := h (e.val.symm z) hx hz.2
    rw [e.val.right_inv hz.1] at hh
    exact hh.differentiableAt
  · intro z hz
    have hx := f.val.map_target hz.1
    have hh := h' (f.val.symm z) hx hz.2
    rw [f.val.right_inv hz.1] at hh
    exact hh.differentiableAt


theorem inclusion_coordinate_eq {i : E → X} (hi : IsOpenEmbedding i)
    (e : ComplexChart E) {z : ℂ} (hz : z ∈ e.val.target) :
    coordinateMap e (transportChart hi e) i z = z := by
  simp only [coordinateMap, transportChart_apply, e.val.right_inv hz]

theorem inclusion_coordinate_holomorphic {i : E → X} (hi : IsOpenEmbedding i)
    (e : ComplexChart E) :
    HolomorphicOn e.val.target (coordinateMap e (transportChart hi e) i) := by
  refine ⟨e.val.open_target, fun z hz => ?_⟩
  apply differentiableAt_id.congr_of_eventuallyEq
  filter_upwards [e.val.open_target.mem_nhds hz] with w hw
  exact inclusion_coordinate_eq hi e hw

/-- Any surface atlas containing the transported old atlas preserves old holomorphy. -/
theorem inclusion_holomorphicMap {i : E → X} (hi : IsOpenEmbedding i)
    (S : RiemannSurface E) (T : RiemannSurface X)
    (hatlas : ∀ e ∈ S.atlas, transportChart hi e ∈ T.atlas) :
    HolomorphicMap S T i := by
  intro a
  obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
  refine ⟨hi.continuous.continuousAt, e, he,
    transportChart hi e, hatlas e he, ha, ?_, ?_⟩
  · exact mem_image_of_mem i ha
  · exact ⟨e.val.target, e.val.map_source ha, inclusion_coordinate_holomorphic hi e⟩

theorem inclusion_locallyBiholomorphicAt {i : E → X} (hi : IsOpenEmbedding i)
    (S : RiemannSurface E) (T : RiemannSurface X)
    (hatlas : ∀ e ∈ S.atlas, transportChart hi e ∈ T.atlas) (a : E) :
    LocallyBiholomorphicAt S T i a := by
  obtain ⟨e, he, ha⟩ := S.isAtlas.1 a
  refine ⟨e, he,
    transportChart hi e, hatlas e he, ha, ?_,
    e.val.target, e.val.target, id, ?_, ?_, ?_, ?_⟩
  · exact mem_image_of_mem i ha
  · exact e.val.map_source ha
  · intro z hz
    exact ⟨hz, mem_image_of_mem i (e.val.map_target hz)⟩
  · exact Subset.rfl
  · refine ⟨inclusion_coordinate_holomorphic hi e,
      ⟨e.val.open_target, fun _ _ => differentiableAt_id⟩, ?_, ?_, ?_, ?_⟩
    · intro z hz; simpa only [inclusion_coordinate_eq hi e hz] using hz
    · exact mapsTo_id _
    · intro z hz; exact inclusion_coordinate_eq hi e hz
    · intro z hz; exact inclusion_coordinate_eq hi e hz


/-- Compose transitions through a third chart on an actual common neighborhood. -/
theorem transition_germ_via_chart {e f g : ComplexChart X} {a : X}
    (hae : a ∈ e.val.source) (haf : a ∈ f.val.source) (hag : a ∈ g.val.source)
    (heg : CompatibleCharts e g) (hgf : CompatibleCharts g f) :
    HolomorphicGermAt (fun z => f.val (e.val.symm z)) (e.val a) := by
  have h₁ := compatibleCharts_germ heg hae hag
  have h₂ : HolomorphicGermAt (fun z => f.val (g.val.symm z))
      (g.val (e.val.symm (e.val a))) := by
    simpa only [e.val.left_inv hae] using compatibleCharts_germ hgf hag haf
  apply (h₂.comp h₁).congr
  have hh : ∀ᶠ z in 𝓝 (e.val a), e.val.symm z ∈ g.val.source :=
    (e.val.tendsto_symm hae) (g.val.open_source.mem_nhds hag)
  filter_upwards [hh] with z hz
  simp only [g.val.left_inv hz]

/-- Compatibility of all transported old charts forces exactly the old structure. -/
theorem maximalAtlas_of_transport {i : E → X} (hi : IsOpenEmbedding i)
    (S : RiemannSurface E) (T : RiemannSurface X)
    (hatlas : ∀ e ∈ S.atlas, transportChart hi e ∈ T.atlas)
    (e : ComplexChart E) (he : transportChart hi e ∈ maximalAtlas T.atlas) :
    e ∈ maximalAtlas S.atlas := by
  intro f hf
  exact (transportChart_compatible_iff hi e f).mp (he _ (hatlas f hf))


/-- Scalar meromorphy can be tested in a collection of atlas charts which
covers every point. Neither all charts nor a global no-infinity certificate
are needed as input. -/
theorem scalarMeromorphic_of_local_charts {S : RiemannSurface X}
    {F : X → RiemannSphere}
    (h : ∀ a : X, ∃ e ∈ S.atlas, a ∈ e.val.source ∧
      ScalarMeromorphicOn e.val.target (F ∘ e.val.symm)) :
    ScalarMeromorphic S F := by
  have hlocal : ∀ a : X, ¬ ∀ᶠ x in 𝓝 a, F x = sphereInfty := by
    intro a hinf
    obtain ⟨e, he, ha, hF⟩ := h a
    have hplane := scalarMeromorphic_planeSphereHolomorphic hF
    have hnot : ¬ EqOn (F ∘ e.val.symm) (fun _ => sphereInfty) e.val.target := by
      intro hh
      obtain ⟨b, hb, hfin⟩ := hF.2.2.2.2.2 (e.val a) (e.val.map_source ha)
      exact hfin (hh (connectedComponentIn_subset _ _ hb))
    have hi : ∀ᶠ z in 𝓝 (e.val a), (F ∘ e.val.symm) z = sphereInfty :=
      (e.val.tendsto_symm ha) hinf
    exact plane_no_infty_germ e.property hplane hnot (e.val a)
      (e.val.map_source ha) hi
  intro e he
  apply plane_scalarMeromorphic_of_no_infty_germ
  · refine ⟨e.val.open_target, ?_⟩
    intro z hz
    obtain ⟨d, hd, hx, hfd⟩ := h (e.val.symm z)
    have hg := compatibleCharts_germ (S.isAtlas.2 e he d hd) (e.val.map_target hz) hx
    rw [e.val.right_inv hz] at hg
    have hFd := (scalarMeromorphic_planeSphereHolomorphic hfd).2
      (d.val (e.val.symm z)) (d.val.map_source hx)
    have hh := planeSphereHolomorphicAt_comp hFd hg
    apply hh.congr
    filter_upwards [(e.val.continuousAt_symm hz) (d.val.open_source.mem_nhds hx)] with w hw
    change e.val.symm w ∈ d.val.source at hw
    simp only [Function.comp_def, d.val.left_inv hw]
  · intro z hz hinf
    apply hlocal (e.val.symm z)
    have hc : Tendsto e.val (𝓝 (e.val.symm z)) (𝓝 z) := by
      simpa only [e.val.right_inv hz] using
        (e.val.continuousAt (e.val.map_target hz)).tendsto
    have hi := hc hinf
    filter_upwards [e.val.open_source.mem_nhds (e.val.map_target hz), hi] with x hx hi
    change F (e.val.symm (e.val x)) = sphereInfty at hi
    simpa only [e.val.left_inv hx] using hi


section Attachment
variable {J : Type v} {B : Type w} [TopologicalSpace B]
  (d : Data E J B) (S : RiemannSurface E) (a : AnalyticParameters d S)
variable [TopologicalSpace (E ⊕ J)]

structure DiskCharts where
  chart : J → ComplexChart (E ⊕ J)
  source : ∀ j, (chart j).val.source = range (d.psi j)
  target : ∀ j, (chart j).val.target = Metric.ball (0 : ℂ) (d.radius j)
  apply_disk : ∀ j (t : FullDisk (d.radius j)), (chart j).val (d.psi j t) = (t : ℂ)
  symm_disk : ∀ j (t : FullDisk (d.radius j)), (chart j).val.symm (t : ℂ) = d.psi j t

variable (p : DiskCharts d)

lemma parameterChart_on_old (j : J) {x : E} (hx : x ∈ range (d.theta j)) :
    (p.chart j).val (Sum.inl x) = (a.chart j).val x := by
  obtain ⟨t, rfl⟩ := hx
  rw [← d.psi_puncture j t, p.apply_disk, a.apply_theta]
  rfl

lemma parameterChart_symm_on_puncture (j : J) {z : ℂ}
    (hz : 0 < ‖z‖ ∧ ‖z‖ < d.radius j) :
    (p.chart j).val.symm z = Sum.inl ((a.chart j).val.symm z) := by
  let t : Parameter (d.radius j) := ⟨z, hz⟩
  change (p.chart j).val.symm (t : ℂ) = Sum.inl ((a.chart j).val.symm (t : ℂ))
  rw [a.symm_parameter j t]
  exact (p.symm_disk j (punctureInclusion t)).trans (d.psi_puncture j t)

lemma parameterChart_old_source (j : J) (x : E) :
    Sum.inl x ∈ (p.chart j).val.source ↔ x ∈ range (d.theta j) := by
  rw [p.source, d.range_psi]
  simp

lemma old_parameter_compatible (hi : IsOpenEmbedding (Sum.inl : E → E ⊕ J)) (j : J) (e : ComplexChart E)
    (he : CompatibleCharts e (a.chart j)) :
    CompatibleCharts (transportChart hi e) (p.chart j) := by
  apply compatibleCharts_of_germs
  · intro x hx hp
    obtain ⟨y, hy, rfl⟩ := hx
    have hyj : y ∈ (a.chart j).val.source := by
      rw [a.source]
      exact (parameterChart_old_source d p j y).mp hp
    have hg := compatibleCharts_germ he hy hyj
    rw [transportChart_apply]
    apply hg.congr
    have hnear : ∀ᶠ z in 𝓝 (e.val y), e.val.symm z ∈ (a.chart j).val.source :=
      (e.val.tendsto_symm hy) ((a.chart j).val.open_source.mem_nhds hyj)
    filter_upwards [hnear] with z hz
    exact (parameterChart_on_old d S a p j (by rwa [← a.source])).symm
  · intro x hp hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyj : y ∈ (a.chart j).val.source := by
      rw [a.source]
      exact (parameterChart_old_source d p j y).mp hp
    have hg := compatibleCharts_germ (compatibleCharts_symm he) hyj hy
    rw [parameterChart_on_old d S a p j (by rwa [← a.source])]
    apply hg.congr
    have hnear := (a.chart j).val.open_target.mem_nhds ((a.chart j).val.map_source hyj)
    filter_upwards [hnear] with z hz
    rw [a.target] at hz
    rw [parameterChart_symm_on_puncture d S a p j hz, transportChart_apply]

lemma parameterChart_new_source (j k : J) :
    Sum.inr k ∈ (p.chart j).val.source ↔ k = j := by
  rw [p.source, d.range_psi]
  simp [eq_comm]

include S a in
lemma parameter_compatible (hi : IsOpenEmbedding (Sum.inl : E → E ⊕ J))
    (j k : J) : CompatibleCharts (p.chart j) (p.chart k) := by
  by_cases hjk : j = k
  · subst k
    exact compatibleCharts_refl _
  have hg (j : J) (e : ComplexChart E) (he : e ∈ S.atlas) :
      CompatibleCharts (transportChart hi e) (p.chart j) :=
    old_parameter_compatible d S a p hi j e (compatibleCharts_symm (a.compatible j e he))
  apply compatibleCharts_of_germs
  · intro x hxj hxk
    cases x with
    | inl y =>
      obtain ⟨e, he, hy⟩ := S.isAtlas.1 y
      exact transition_germ_via_chart hxj hxk (mem_image_of_mem Sum.inl hy)
        (compatibleCharts_symm (hg j e he)) (hg k e he)
    | inr l =>
      have hlj := (parameterChart_new_source d p j l).mp hxj
      have hlk := (parameterChart_new_source d p k l).mp hxk
      exact (hjk (hlj.symm.trans hlk)).elim
  · intro x hxk hxj
    cases x with
    | inl y =>
      obtain ⟨e, he, hy⟩ := S.isAtlas.1 y
      exact transition_germ_via_chart hxk hxj (mem_image_of_mem Sum.inl hy)
        (compatibleCharts_symm (hg k e he)) (hg j e he)
    | inr l =>
      have hlj := (parameterChart_new_source d p j l).mp hxj
      have hlk := (parameterChart_new_source d p k l).mp hxk
      exact (hjk (hlj.symm.trans hlk)).elim

def attachmentAtlas (hi : IsOpenEmbedding (Sum.inl : E → E ⊕ J)) :
    Set (ComplexChart (E ⊕ J)) :=
  (transportChart hi '' S.atlas) ∪ range p.chart

include a in
lemma attachment_isAtlas (hi : IsOpenEmbedding (Sum.inl : E → E ⊕ J)) :
    IsAtlas (attachmentAtlas d S p hi) := by
  constructor
  · rintro (x | j)
    · obtain ⟨e, he, hx⟩ := S.isAtlas.1 x
      exact ⟨transportChart hi e, Or.inl ⟨e, he, rfl⟩, mem_image_of_mem Sum.inl hx⟩
    · refine ⟨p.chart j, Or.inr ⟨j, rfl⟩, ?_⟩
      exact (parameterChart_new_source d p j j).mpr rfl
  · rintro e (⟨e, he, rfl⟩ | ⟨j, rfl⟩) f (⟨f, hf, rfl⟩ | ⟨k, rfl⟩)
    · exact (transportChart_compatible_iff hi e f).mpr (S.isAtlas.2 e he f hf)
    · exact old_parameter_compatible d S a p hi k e (compatibleCharts_symm (a.compatible k e he))
    · exact compatibleCharts_symm
        (old_parameter_compatible d S a p hi j f (compatibleCharts_symm (a.compatible j f hf)))
    · exact parameter_compatible d S a p hi j k

include a in
lemma attachment_old_structure (hi : IsOpenEmbedding (Sum.inl : E → E ⊕ J))
    (e : ComplexChart E) :
    e ∈ maximalAtlas S.atlas ↔
      transportChart hi e ∈ maximalAtlas (attachmentAtlas d S p hi) := by
  constructor
  · intro he
    rintro f (⟨f, hf, rfl⟩ | ⟨j, rfl⟩)
    · exact (transportChart_compatible_iff hi e f).mpr (he f hf)
    · have hmax := maximalAtlas_isAtlas S.isAtlas
      have hc : a.chart j ∈ maximalAtlas S.atlas := a.compatible j
      exact old_parameter_compatible d S a p hi j e (hmax.2 e he (a.chart j) hc)
  · intro he f hf
    exact (transportChart_compatible_iff hi e f).mp (he _ (Or.inl ⟨f, hf, rfl⟩))

end Attachment

theorem exists_diskCharts {J : Type v} {B : Type w} [TopologicalSpace B]
    (d : Data E J B) : letI := d.topology; Nonempty (DiskCharts d) := by
  let := d.topology
  have hc (j : J) := d.parameter_chart j
  choose e hs ht hf hg using hc
  refine ⟨⟨fun j => ⟨e j, ?_⟩, hs, ht, hf, hg⟩⟩
  rw [ht]
  exact ⟨⟨0, Metric.mem_ball_self (d.radius_pos j)⟩, Metric.isOpen_ball,
    (convex_ball (0 : ℂ) (d.radius j)).isPreconnected⟩



section ScalarPasting
variable {E : Type u} {J : Type v} {B : Type w}
  [TopologicalSpace E] [TopologicalSpace B] (d : Data E J B)

lemma paste_psi (F : E → RiemannSphere) (G : J → ℂ → RiemannSphere)
    (hmatch : ∀ (j : J) (t : Parameter (d.radius j)), G j t = F (d.theta j t))
    (j : J) (t : FullDisk (d.radius j)) :
    paste F G (d.psi j t) = G j t := by
  classical
  by_cases ht : (t : ℂ) = 0
  · have htc : t = d.center j := Subtype.ext ht
    subst t
    rw [d.psi_center]
    rfl
  · rw [d.psi_of_ne_zero j t ht]
    exact (hmatch j ⟨t, norm_pos_iff.mpr ht,
      by simpa only [Metric.mem_ball, dist_zero_right] using t.property⟩).symm

variable [TopologicalSpace (E ⊕ J)]

theorem scalarMeromorphic_paste
    (S : RiemannSurface E) (T : RiemannSurface (E ⊕ J))
    (hi : IsOpenEmbedding (Sum.inl : E → E ⊕ J))
    (p : J → ComplexChart (E ⊕ J))
    (hA : T.atlas = transportChart hi '' S.atlas ∪ range p)
    (ht : ∀ j, (p j).val.target = Metric.ball (0 : ℂ) (d.radius j))
    (hinv : ∀ j (t : FullDisk (d.radius j)), (p j).val.symm t = d.psi j t)
    (F : E → RiemannSphere) (G : J → ℂ → RiemannSphere)
    (hF : ScalarMeromorphic S F)
    (hG : ∀ j, ScalarMeromorphicOn (Metric.ball (0 : ℂ) (d.radius j)) (G j))
    (hmatch : ∀ j (t : Parameter (d.radius j)), G j t = F (d.theta j t)) :
    ScalarMeromorphic T (paste F G) := by
  intro e he
  rw [hA] at he
  rcases he with ⟨e, he, rfl⟩ | ⟨j, rfl⟩
  · exact LocalQuotientsArithmetic.scalar_congr (hF e he) (by
      intro z hz
      rfl)
  · rw [ht]
    apply LocalQuotientsArithmetic.scalar_congr (hG j)
    intro z hz
    change G j z = paste F G ((p j).val.symm z)
    rw [hinv j ⟨z, hz⟩]
    exact (paste_psi d F G hmatch j ⟨z, hz⟩).symm


end ScalarPasting

/-- Extend the old complex structure across the exact finite-end attachment.
The topology is the previously constructed final topology, and the atlas is
chosen before (and independently of) every scalar function to be pasted. -/
theorem analytic_end_pasting :
    Specs.D12Complex.Ch21.AnalyticEndPasting.analytic_end_pasting_type := by
  intro E J B _ _ _ _ d S a
  let := d.topology
  let := S.connected
  let := S.hausdorff
  let := S.secondCountable
  obtain ⟨p⟩ := exists_diskCharts d
  let hi := d.old_openEmbedding
  let T : RiemannSurface (E ⊕ J) :=
    { connected := d.connected
      hausdorff := d.hausdorff
      secondCountable := d.secondCountable
      atlas := attachmentAtlas d S p hi
      isAtlas := attachment_isAtlas d S a p hi }
  have h_old (e : ComplexChart E) (he : e ∈ S.atlas) :
      transportChart hi e ∈ T.atlas := Or.inl ⟨e, he, rfl⟩
  refine ⟨{
    oldEmbedding := hi
    surface := T
    parameterChart := p.chart
    atlas_eq := rfl
    parameter_source := p.source
    parameter_target := p.target
    parameter_center := ?_
    parameter_apply := p.apply_disk
    parameter_symm := p.symm_disk
    old_holomorphic := inclusion_holomorphicMap hi S T h_old
    old_locallyBiholomorphic := inclusion_locallyBiholomorphicAt hi S T h_old
    old_structure := attachment_old_structure d S a p hi
    meromorphic_paste := ?_ }⟩
  · intro j
    have h := p.apply_disk j (d.center j)
    rw [d.psi_center] at h
    exact h
  · intro F G hF hG hm
    exact scalarMeromorphic_paste d S T hi p.chart rfl p.target p.symm_disk F G hF hG hm

end D12Complex.AnalyticEndPasting
