import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TorusSurface
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.LatticeGeometry
import Mathlib.Analysis.Normed.Module.Convex
import Batteries.Tactic.OpenPrivate
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Tactic.Linarith

noncomputable section
open Set
open scoped Topology

namespace D12Complex.TorusSurface
open private periodBasis lattice_eq_span_basis from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.LatticeGeometry

variable {ω₁ ω₂ : ℂ}

theorem quotient_topology : Specs.D12Complex.Ch22.TorusSurface.quotient_topology_type := by
  intro ω₁ ω₂
  exact ⟨QuotientAddGroup.isOpenQuotientMap_mk, inferInstance⟩

lemma closed_lattice (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    IsClosed (lattice ω₁ ω₂ : Set ℂ) := by
  let :=  D12Complex.Ch22.LatticeGeometry.discrete ω₁ ω₂ h₁ h₂
  exact @AddSubgroup.isClosed_of_discreteTopology _ _ _ _ _
    (lattice ω₁ ω₂).toAddSubgroup inferInstance

theorem metric : Specs.D12Complex.Ch22.TorusSurface.metric_type := by
  intro ω₁ ω₂ h₁ h₂
  let :=  closed_lattice h₁ h₂
  exact ⟨inferInstance, rfl⟩

lemma distance_eq_infDist (z w : ℂ) :
    dist (projection ω₁ ω₂ z) (projection ω₁ ω₂ w) =
      Metric.infDist (z - w) (lattice ω₁ ω₂) := by
  rw [dist_eq_norm, ← map_sub]
  exact QuotientAddGroup.norm_mk _

theorem distance_minimum : Specs.D12Complex.Ch22.TorusSurface.distance_minimum_type := by
  intro ω₁ ω₂ h₁ h₂ z w
  obtain ⟨l, hl, hmin⟩ := (closed_lattice h₁ h₂).exists_infDist_eq_dist
    ⟨0, (lattice ω₁ ω₂).zero_mem⟩ (z - w)
  refine ⟨l, hl, ?_, ?_⟩
  · rw [distance_eq_infDist, hmin, dist_eq_norm]
  · intro k hk
    rw [← dist_eq_norm, ← hmin]
    simpa [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := z - w) hk

lemma periodic_projection (ω₁ ω₂ : ℂ) : Periodic ω₁ ω₂ (projection ω₁ ω₂) := by
  intro z l hl
  simp [map_add, projection, hl]

theorem topology : Specs.D12Complex.Ch22.TorusSurface.topology_type := by
  intro ω₁ ω₂ h₁ h₂
  let :=  closed_lattice h₁ h₂
  let :=  D12Complex.Ch22.LatticeGeometry.discrete ω₁ ω₂ h₁ h₂
  let : IsZLattice ℝ (lattice ω₁ ω₂) := ⟨by
    change Submodule.span ℝ (Ch22.LatticeGeometry.lattice ω₁ ω₂ : Set ℂ) = ⊤
    rw [lattice_eq_span_basis h₁ h₂]
    exact ZSpan.span_top _⟩
  have hc := IsZLattice.isCompact_range_of_periodic (lattice ω₁ ω₂)
    (projection ω₁ ω₂) QuotientAddGroup.continuous_mk (periodic_projection ω₁ ω₂)
  have hsur : Function.Surjective (projection ω₁ ω₂) := QuotientAddGroup.mk'_surjective _
  have : CompactSpace (Torus ω₁ ω₂) := ⟨by simpa [hsur.range_eq] using hc⟩
  have : ConnectedSpace (Torus ω₁ ω₂) :=
    hsur.connectedSpace QuotientAddGroup.continuous_mk
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

lemma projection_eq_iff (z w : ℂ) :
    projection ω₁ ω₂ z = projection ω₁ ω₂ w ↔ z - w ∈ lattice ω₁ ω₂ :=
  QuotientAddGroup.eq_iff_sub_mem

lemma projection_injOn_ball {d : ℝ} (hd : Separation ω₁ ω₂ d)
    (a : ℂ) {r : ℝ} (hr : r < d / 3) :
    InjOn (projection ω₁ ω₂) (Metric.ball a r) := by
  intro z hz w hw heq
  by_contra hne
  have hl := hd.2 (z - w) ((projection_eq_iff z w).mp heq) (sub_ne_zero.mpr hne)
  have hdist := dist_triangle z a w
  have hz' := Metric.mem_ball.mp hz
  have hw' := Metric.mem_ball.mp hw
  rw [dist_comm a w] at hdist
  rw [← dist_eq_norm] at hl
  linarith [hd.1]

/-- The inverse chart is literally the quotient projection on its disk. -/
def diskProjection (a : ℂ) {r d : ℝ} (hd : Separation ω₁ ω₂ d) (hr : r < d / 3) :
    OpenPartialHomeomorph ℂ (Torus ω₁ ω₂) :=
  OpenPartialHomeomorph.ofContinuousOpen
    ((projection_injOn_ball hd a hr).toPartialEquiv (projection ω₁ ω₂) (Metric.ball a r))
    QuotientAddGroup.continuous_mk.continuousOn QuotientAddGroup.isOpenMap_coe Metric.isOpen_ball

lemma diskProjection_source (a : ℂ) {r d : ℝ} (hd : Separation ω₁ ω₂ d) (hr : r < d / 3) :
    (diskProjection a hd hr).source = Metric.ball a r := rfl

lemma diskProjection_target (a : ℂ) {r d : ℝ} (hd : Separation ω₁ ω₂ d) (hr : r < d / 3) :
    (diskProjection a hd hr).target = projection ω₁ ω₂ '' Metric.ball a r := rfl

lemma diskProjection_apply (a : ℂ) {r d : ℝ} (hd : Separation ω₁ ω₂ d) (hr : r < d / 3)
    (z : ℂ) : diskProjection a hd hr z = projection ω₁ ω₂ z := rfl

def diskChart (a : ℂ) {r d : ℝ} (hd : Separation ω₁ ω₂ d)
    (hr₀ : 0 < r) (hr : r < d / 3) : Surfaces.ComplexChart (Torus ω₁ ω₂) :=
  ⟨(diskProjection a hd hr).symm,
    ⟨⟨a, Metric.mem_ball_self hr₀⟩, Metric.isOpen_ball, (convex_ball a r).isPreconnected⟩⟩

theorem disk_charts : Specs.D12Complex.Ch22.TorusSurface.disk_charts_type := by
  intro ω₁ ω₂ _ _ d hd a r hr₀ hr
  refine ⟨diskChart a hd hr₀ hr, ⟨a, r, hr₀, hr, rfl, ?_⟩, rfl, rfl, ?_, ?_⟩
  · intro z _; rfl
  · intro z _; rfl
  · intro z hz
    exact (diskProjection a hd hr).left_inv hz

lemma chart_lift {d : ℝ} {e : Surfaces.ComplexChart (Torus ω₁ ω₂)}
    (he : e ∈ quotientAtlas ω₁ ω₂ d) :
    EqOn e.val.symm (projection ω₁ ω₂) e.val.target := by
  obtain ⟨a, r, _, _, ht, hi⟩ := he
  simpa [ht] using hi

lemma transition_difference_mem {d : ℝ} {e f : Surfaces.ComplexChart (Torus ω₁ ω₂)}
    (he : e ∈ quotientAtlas ω₁ ω₂ d) (hf : f ∈ quotientAtlas ω₁ ω₂ d)
    {z : ℂ} (hz : z ∈ (e.val.symm.trans f.val).source) :
    (e.val.symm.trans f.val) z - z ∈ lattice ω₁ ω₂ := by
  apply (projection_eq_iff _ _).mp
  calc
    projection ω₁ ω₂ ((e.val.symm.trans f.val) z) =
        f.val.symm (f.val (e.val.symm z)) :=
      (chart_lift hf (f.val.map_source hz.2)).symm
    _ = e.val.symm z := f.val.left_inv hz.2
    _ = projection ω₁ ω₂ z := chart_lift he hz.1

theorem translations : Specs.D12Complex.Ch22.TorusSurface.translations_type := by
  intro ω₁ ω₂ h₁ h₂ d e he f hf C hC hc
  let :=  Ch22.LatticeGeometry.discrete ω₁ ω₂ h₁ h₂
  have hl : IsDiscrete (lattice ω₁ ω₂ : Set ℂ) :=
    isDiscrete_iff_discreteTopology.mpr inferInstance
  let t := e.val.symm.trans f.val
  obtain ⟨l, hl, heq⟩ := hc.eqOn_const_of_mapsTo hl
    ((t.continuousOn.sub continuousOn_id).mono hC)
    (fun z hz => transition_difference_mem he hf (hC hz))
    ⟨0, (lattice ω₁ ω₂).zero_mem⟩
  refine ⟨l, hl, fun z hz => ?_⟩
  have hz' : t z - z = l := heq hz
  exact (sub_eq_iff_eq_add.mp hz').trans (add_comm _ _)

lemma holomorphic_transition (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {d : ℝ} {e f : Surfaces.ComplexChart (Torus ω₁ ω₂)}
    (he : e ∈ quotientAtlas ω₁ ω₂ d) (hf : f ∈ quotientAtlas ω₁ ω₂ d) :
    HolomorphicOn (e.val.symm.trans f.val).source (e.val.symm.trans f.val) := by
  let t := e.val.symm.trans f.val
  refine ⟨t.open_source, fun z hz => ?_⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp t.open_source z hz
  obtain ⟨l, _, hl⟩ := translations ω₁ ω₂ h₁ h₂ d e he f hf
    (Metric.ball z r) hsub (convex_ball z r).isPreconnected
  apply (differentiableAt_id.add_const l).congr_of_eventuallyEq
  exact Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨Metric.ball z r, Metric.ball_mem_nhds z hr, hl⟩

lemma atlas_isAtlas (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {d : ℝ} (hd : Separation ω₁ ω₂ d) : Surfaces.IsAtlas (quotientAtlas ω₁ ω₂ d) := by
  refine ⟨fun x => ?_, fun e he f hf => ?_⟩
  · obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup x
    obtain ⟨e, he, _, hs, _⟩ := disk_charts ω₁ ω₂ h₁ h₂ d hd a (d / 4)
      (by linarith [hd.1]) (by linarith [hd.1])
    refine ⟨e, he, ?_⟩
    rw [hs]
    exact ⟨a, Metric.mem_ball_self (by linarith [hd.1]), rfl⟩
  · let t := e.val.symm.trans f.val
    refine ⟨holomorphic_transition h₁ h₂ he hf, ?_,
      t.mapsTo, t.symm.mapsTo, t.leftInvOn, t.rightInvOn⟩
    exact holomorphic_transition h₁ h₂ hf he

theorem surface : Specs.D12Complex.Ch22.TorusSurface.surface_type := by
  intro ω₁ ω₂ h₁ h₂ d hd
  obtain ⟨hc, hT, hs, _⟩ := topology ω₁ ω₂ h₁ h₂
  exact ⟨⟨hc, hT, hs, quotientAtlas ω₁ ω₂ d, atlas_isAtlas h₁ h₂ hd⟩, rfl⟩

theorem compact_surface : Specs.D12Complex.Ch22.TorusSurface.compact_surface_type := by
  intro ω₁ ω₂ h₁ h₂
  obtain ⟨d, hd, l, hl, hl₀, hld, hsep⟩ :=
    Ch22.LatticeGeometry.minimum_distance ω₁ ω₂ h₁ h₂
  have hs : Separation ω₁ ω₂ d := ⟨hd, fun k hk hk₀ => by
    simpa using hsep k hk 0 (lattice ω₁ ω₂).zero_mem hk₀⟩
  obtain ⟨S, hS⟩ := surface ω₁ ω₂ h₁ h₂ d hs
  exact ⟨d, hs, ⟨l, hl, hl₀, hld⟩, S, hS, (topology ω₁ ω₂ h₁ h₂).2.2.2⟩

theorem locally_biholomorphic : Specs.D12Complex.Ch22.TorusSurface.locally_biholomorphic_type := by
  intro ω₁ ω₂ h₁ h₂ d hd a r hr₀ hr
  obtain ⟨e, he, ht, hs, _, hid⟩ := disk_charts ω₁ ω₂ h₁ h₂ d hd a r hr₀ hr
  refine ⟨e, he, ht, hs, ⟨Metric.isOpen_ball, fun z hz => ?_⟩,
    ⟨Metric.isOpen_ball, fun _ _ => differentiableAt_id⟩,
    (fun z hz => ?_), (fun _ hz => hz), (fun z hz => ?_), (fun z hz => ?_)⟩
  · apply differentiableAt_id.congr_of_eventuallyEq (𝕜 := ℂ)
    exact (Metric.isOpen_ball.eventually_mem hz).mono fun w hw => hid w hw
  · change e.val (projection ω₁ ω₂ z) ∈ Metric.ball a r
    rw [hid z hz]
    exact hz
  · exact hid z hz
  · exact hid z hz

lemma periodic_eq_of_projection_eq {A : Type*} {f : ℂ → A} (hf : Periodic ω₁ ω₂ f)
    {z w : ℂ} (h : projection ω₁ ω₂ z = projection ω₁ ω₂ w) : f z = f w := by
  simpa using hf w (z - w) ((projection_eq_iff z w).mp h)

theorem descent : Specs.D12Complex.Ch22.TorusSurface.descent_type := by
  intro ω₁ ω₂ A f hf
  have hsur : Function.Surjective (projection ω₁ ω₂) := QuotientAddGroup.mk'_surjective _
  obtain ⟨s, hs⟩ := hsur.hasRightInverse
  let F : Torus ω₁ ω₂ → A := fun x => f (s x)
  have hF : F ∘ projection ω₁ ω₂ = f := by
    funext z
    exact periodic_eq_of_projection_eq hf (hs (projection ω₁ ω₂ z))
  refine ⟨F, hF, fun G hG => ?_⟩
  funext x
  obtain ⟨z, rfl⟩ := hsur x
  exact (congrFun hG z).trans (congrFun hF z).symm

/-- In every quotient disk coordinate the descended function is the original function. -/
lemma descent_in_chart {A : Type*} {f : ℂ → A} {F : Torus ω₁ ω₂ → A}
    (hF : F ∘ projection ω₁ ω₂ = f) {d : ℝ}
    {e : Surfaces.ComplexChart (Torus ω₁ ω₂)} (he : e ∈ quotientAtlas ω₁ ω₂ d) :
    EqOn (F ∘ e.val.symm) f e.val.target := by
  intro z hz
  change F (e.val.symm z) = f z
  rw [chart_lift he hz]
  exact congrFun hF z

theorem holomorphic_descent : Specs.D12Complex.Ch22.TorusSurface.holomorphic_descent_type := by
  intro ω₁ ω₂ f hf hh
  obtain ⟨F, hF, _⟩ := descent ω₁ ω₂ ℂ f hf
  refine ⟨F, hF, fun d e he => ⟨e.val.open_target, fun z hz => ?_⟩⟩
  apply (hh.2 z (mem_univ z)).congr_of_eventuallyEq
  exact (e.val.open_target.eventually_mem hz).mono fun w hw => descent_in_chart hF he hw

theorem meromorphic_descent : Specs.D12Complex.Ch22.TorusSurface.meromorphic_descent_type := by
  intro ω₁ ω₂ f hf hm
  obtain ⟨F, hF, _⟩ := descent ω₁ ω₂ ℂ f hf
  refine ⟨F, hF, fun d e he z hz => ?_⟩
  apply (hm z).congr
  exact ((e.val.open_target.eventually_mem hz).mono
    fun w hw => (descent_in_chart hF he hw).symm).filter_mono nhdsWithin_le_nhds

end D12Complex.TorusSurface

namespace D12Complex.TorusSurface.Definitions
abbrev Torus : Specs.D12Complex.Ch22.TorusSurface.Torus_type := D12Complex.TorusSurface.Torus
abbrev projection : Specs.D12Complex.Ch22.TorusSurface.projection_type :=
  D12Complex.TorusSurface.projection
abbrev Periodic : Specs.D12Complex.Ch22.TorusSurface.Periodic_type :=
  @D12Complex.TorusSurface.Periodic
abbrev Separation : Specs.D12Complex.Ch22.TorusSurface.Separation_type :=
  D12Complex.TorusSurface.Separation
abbrev quotientAtlas : Specs.D12Complex.Ch22.TorusSurface.quotientAtlas_type :=
  D12Complex.TorusSurface.quotientAtlas
end D12Complex.TorusSurface.Definitions
