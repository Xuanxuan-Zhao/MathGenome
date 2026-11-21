import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch07.ScalarSphereBridge
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.Meromorphic
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic
import Mathlib.Analysis.Complex.Liouville
import Batteries.Tactic.OpenPrivate

noncomputable section
open Filter Set
open scoped Topology
namespace D12Complex

open private coordinate_open coordinate_inverse_continuous coordinate_continuousAt
  coordinate_exists from MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.SphereHolomorphic

lemma sphere_eq_finiteCoordinate_of_ne_infty {p : RiemannSphere} (hp : p ≠ sphereInfty) :
    p = sphereFinite (finiteCoordinate p) := by
  induction p using OnePoint.rec with
  | infty => exact (hp rfl).elim
  | coe z => rfl

lemma infinityCoordinate_eq_zero_iff {p : RiemannSphere} (hp : p ≠ sphereFinite 0) :
    infinityCoordinate p = 0 ↔ p = sphereInfty := by
  induction p using OnePoint.rec with
  | infty => simp [infinityCoordinate, sphereInfty]
  | coe z =>
    have hz : z ≠ 0 := fun h => hp (congrArg sphereFinite h)
    simp [infinityCoordinate, sphereInfty, hz]

lemma PlaneSphereHolomorphicAt.congr {F G : ℂ → RiemannSphere} {a : ℂ}
    (hF : PlaneSphereHolomorphicAt F a) (he : F =ᶠ[𝓝 a] G) :
    PlaneSphereHolomorphicAt G a := by
  obtain ⟨hc, d, hd, hg⟩ := hF
  refine ⟨hc.congr_of_eventuallyEq he.symm, d, ?_, ?_⟩
  · rwa [← he.self_of_nhds]
  · exact hg.congr (he.mono fun _ h => congrArg (sphereCoordinate d) h)

lemma SphereHolomorphicAt.plane_chart {F : RiemannSphere → RiemannSphere}
    {p : RiemannSphere} (hF : SphereHolomorphicAt F p) (c : SphereCoordinate)
    (hc : p ∈ (sphereCoordinate c).source) :
    PlaneSphereHolomorphicAt (F ∘ (sphereCoordinate c).symm) (sphereCoordinate c p) := by
  obtain ⟨d, hd⟩ := coordinate_exists (F p)
  obtain ⟨hcont, hg⟩ := (sphereHolomorphicAt_iff_charts F p c d hc hd).mp hF
  have hi := (sphereCoordinate c).left_inv hc
  refine ⟨?_, d, ?_, hg⟩
  · apply ContinuousAt.comp _ (coordinate_inverse_continuous c).continuousAt
    simpa only [hi] using hcont
  · simpa only [Function.comp_apply, hi] using hd

lemma planeSphereHolomorphicAt_of_sphere_chart {F : RiemannSphere → RiemannSphere}
    {p : RiemannSphere} (c : SphereCoordinate) (hc : p ∈ (sphereCoordinate c).source)
    (hF : PlaneSphereHolomorphicAt (F ∘ (sphereCoordinate c).symm) (sphereCoordinate c p)) :
    SphereHolomorphicAt F p := by
  obtain ⟨hcont, d, hd, hg⟩ := hF
  have hi := (sphereCoordinate c).left_inv hc
  refine ⟨?_, c, d, hc, ?_, hg⟩
  · have ht := hcont.comp (coordinate_continuousAt c p hc)
    apply ht.congr_of_eventuallyEq
    filter_upwards [(coordinate_open c).mem_nhds hc] with q hq
    exact congrArg F ((sphereCoordinate c).left_inv hq).symm
  · simpa only [Function.comp_apply, hi] using hd

lemma planeSphereHolomorphicAt_finite {F : ℂ → RiemannSphere} {a : ℂ}
    (hF : PlaneSphereHolomorphicAt F a) (ha : F a ≠ sphereInfty) :
    HolomorphicGermAt (scalarFinitePart F) a :=
  ((planeSphereHolomorphicAt_iff_chart F a .finite ha).mp hF).2

lemma sphereHolomorphicOn_chart (U : Set RiemannSphere) (F : RiemannSphere → RiemannSphere)
    (hF : SphereHolomorphicOn U F) (c : SphereCoordinate) :
    PlaneSphereHolomorphicOn ((sphereCoordinate c).symm ⁻¹' U)
      (F ∘ (sphereCoordinate c).symm) := by
  refine ⟨hF.1.preimage (coordinate_inverse_continuous c), fun z hz => ?_⟩
  have hp := (sphereCoordinate c).map_target (show z ∈ (sphereCoordinate c).target by
    cases c <;> trivial)
  have h := (hF.2 _ hz).plane_chart c hp
  simpa only [(sphereCoordinate c).right_inv (show z ∈ (sphereCoordinate c).target by
    cases c <;> trivial)] using h

lemma finiteCoordinate_eq_inv_infinityCoordinate (p : RiemannSphere) :
    finiteCoordinate p = (infinityCoordinate p)⁻¹ := by
  induction p using OnePoint.rec with
  | infty => simp [finiteCoordinate, infinityCoordinate]
  | coe z => exact (inv_inv z).symm

lemma HolomorphicGermAt.analyticAt {g : ℂ → ℂ} {a : ℂ}
    (hg : HolomorphicGermAt g a) : AnalyticAt ℂ g a :=
  (LocalZeroFactorization.holomorphicNear_iff_analyticAt g a).mp hg

lemma poleAt_inv_of_zero {g : ℂ → ℂ} {a : ℂ}
    (hg : HolomorphicGermAt g a) (hg0 : g a = 0)
    (hnot : ¬ ∀ᶠ z in 𝓝 a, g z = 0) : PoleAt (fun z => (g z)⁻¹) a := by
  obtain hzero | ⟨_, m, hm, _⟩ := LocalZeroFactorization.local_zero_factorization g a hg
  · exact (hnot hzero.1).elim
  have hmpos : 1 ≤ m := (LocalZeroFactorization.finiteOrder_zero_iff g a m hm).mp hg0
  obtain ⟨u, hu, hu0, he⟩ := hm
  have hune : ∀ᶠ z in 𝓝 a, u z ≠ 0 := (HolomorphicGermAt.analyticAt hu).continuousAt.eventually_ne hu0
  have hud : ∀ᶠ z in 𝓝 a, DifferentiableAt ℂ u z :=
    (holomorphicGermAt_iff_eventually u a).mp hu
  have hgd := (holomorphicGermAt_iff_eventually g a).mp hg
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (he.and (hune.and (hud.and hgd)))
  have hinv : HolomorphicOn (Metric.ball a r) (fun z => (u z)⁻¹) :=
    ⟨Metric.isOpen_ball, fun z hz => (hball z hz).2.2.1.inv (hball z hz).2.1⟩
  have hiso : IsolatedSingularityAt (fun z => (g z)⁻¹) a := by
    refine ⟨r, hr, ?_, fun z hz => ?_⟩
    · exact isOpen_lt continuous_const (continuous_norm.comp (continuous_id.sub continuous_const)) |>.inter
        (isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const)
    · have hzb : z ∈ Metric.ball a r := by simpa [Metric.mem_ball, dist_eq_norm] using hz.2
      have hz0 : z - a ≠ 0 := norm_pos_iff.mp hz.1
      have hgne : g z ≠ 0 := by
        rw [(hball z hzb).1]
        exact mul_ne_zero (pow_ne_zero m hz0) (hball z hzb).2.1
      exact (hball z hzb).2.2.2.inv hgne
  refine ⟨m, hmpos, hiso, r, hr, (fun z => (u z)⁻¹), hinv, inv_ne_zero hu0, ?_⟩
  intro z hz
  have hzb : z ∈ Metric.ball a r := by simpa [Metric.mem_ball, dist_eq_norm] using hz.2
  change (g z)⁻¹ = ((z - a) ^ m)⁻¹ * (u z)⁻¹
  rw [(hball z hzb).1, mul_inv_rev, mul_comm]

/-- At an infinite value, the reciprocal chart distinguishes a locally infinite
map from a genuine finite-order pole; the alternative never assumes meromorphy. -/
lemma plane_infty_germ_or_pole {F : ℂ → RiemannSphere} {a : ℂ}
    (hF : PlaneSphereHolomorphicAt F a) (ha : F a = sphereInfty) :
    (∀ᶠ z in 𝓝 a, F z = sphereInfty) ∨
      (PoleAt (scalarFinitePart F) a ∧ ∀ᶠ z in 𝓝[≠] a, F z ≠ sphereInfty) := by
  have hg := ((planeSphereHolomorphicAt_infty F a ha).1.mp hF).2
  have havoid : ∀ᶠ z in 𝓝 a, F z ≠ sphereFinite 0 :=
    hF.1.eventually_ne (by rw [ha]; exact OnePoint.infty_ne_coe 0)
  by_cases hzero : ∀ᶠ z in 𝓝 a, infinityCoordinate (F z) = 0
  · left
    filter_upwards [hzero, havoid] with z hz hza
    exact (infinityCoordinate_eq_zero_iff hza).mp hz
  · right
    have h0 : infinityCoordinate (F a) = 0 := by rw [ha, infinityCoordinate_sphereInfty]
    have hPole := poleAt_inv_of_zero hg h0 hzero
    have heq : (fun z => (infinityCoordinate (F z))⁻¹) = scalarFinitePart F := by
      funext z; exact (finiteCoordinate_eq_inv_infinityCoordinate (F z)).symm
    rw [heq] at hPole
    refine ⟨hPole, ?_⟩
    have hn := hg.analyticAt.eventually_eq_zero_or_eventually_ne_zero.resolve_left hzero
    filter_upwards [hn] with z hz hInf
    exact hz (by rw [hInf, infinityCoordinate_sphereInfty])

/-- A purely topological propagation argument. The analytic input is exactly
local constancy or isolation of each infinite value. -/
lemma no_infty_germ_of_connected {X : Type*} [TopologicalSpace X]
    {U : Set X} {F : X → RiemannSphere} (_hU : IsOpen U) (hconn : IsPreconnected U)
    (hcont : ∀ a ∈ U, ContinuousAt F a)
    (hdich : ∀ a ∈ U, F a = sphereInfty →
      (∀ᶠ z in 𝓝 a, F z = sphereInfty) ∨
      ∀ᶠ z in 𝓝 a, z ≠ a → F z ≠ sphereInfty)
    (hnot : ¬ EqOn F (fun _ => sphereInfty) U) :
    ∀ a ∈ U, ¬ ∀ᶠ z in 𝓝 a, F z = sphereInfty := by
  have : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hconn
  let H : U → RiemannSphere := fun a => F a
  let E : Set U := {a | ∀ᶠ z in 𝓝 a, H z = sphereInfty}
  have ho : IsOpen E := isOpen_iff_eventually.mpr fun a ha =>
    eventually_eventually_nhds.mpr ha
  have hc : IsClosed E := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_eventually.mpr
    intro a ha
    have hca : ContinuousAt H a := (hcont a a.property).comp continuous_subtype_val.continuousAt
    by_cases hinf : H a = sphereInfty
    · rcases hdich a a.property hinf with he | hn
      · exact (ha (continuous_subtype_val.continuousAt he)).elim
      · have ht := continuous_subtype_val.continuousAt hn
        filter_upwards [ht] with b hb
        by_cases he : b = a
        · simpa only [he] using ha
        · intro hzero
          exact hb (fun h => he (Subtype.ext h)) hzero.self_of_nhds
    · filter_upwards [hca.eventually_ne hinf] with b hb hzero
      exact hb hzero.self_of_nhds
  intro a ha he
  have hea : (⟨a, ha⟩ : U) ∈ E := by
    change ∀ᶠ z : U in 𝓝 (⟨a, ha⟩ : U), F z = sphereInfty
    exact (continuous_subtype_val.continuousAt : ContinuousAt (Subtype.val : U → X) ⟨a, ha⟩) he
  have hall : E = univ := (show IsClopen E from ⟨hc, ho⟩).eq_univ ⟨_, hea⟩
  apply hnot
  intro b hb
  have : (⟨b, hb⟩ : U) ∈ E := hall ▸ mem_univ _
  exact this.self_of_nhds

lemma plane_no_infty_germ {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hΩ : IsDomain Ω) (hF : PlaneSphereHolomorphicOn Ω F)
    (hnot : ¬ EqOn F (fun _ => sphereInfty) Ω) :
    ∀ a ∈ Ω, ¬ ∀ᶠ z in 𝓝 a, F z = sphereInfty := by
  apply no_infty_germ_of_connected hΩ.2.1 hΩ.2.2 (fun a ha => (hF.2 a ha).1) _ hnot
  intro a ha hinf
  rcases plane_infty_germ_or_pole (hF.2 a ha) hinf with h | h
  · exact Or.inl h
  · exact Or.inr (eventually_nhdsWithin_iff.mp h.2)

lemma sphere_infty_germ_or_isolated {F : RiemannSphere → RiemannSphere}
    {p : RiemannSphere} (hF : SphereHolomorphicAt F p) (hinf : F p = sphereInfty) :
    (∀ᶠ q in 𝓝 p, F q = sphereInfty) ∨
      ∀ᶠ q in 𝓝 p, q ≠ p → F q ≠ sphereInfty := by
  obtain ⟨c, hc⟩ := coordinate_exists p
  have hi := (sphereCoordinate c).left_inv hc
  have hchart := hF.plane_chart c hc
  have hic : (F ∘ (sphereCoordinate c).symm) (sphereCoordinate c p) = sphereInfty := by
    simpa only [Function.comp_apply, hi] using hinf
  rcases plane_infty_germ_or_pole hchart hic with h | h
  · left
    filter_upwards [(coordinate_continuousAt c p hc) h,
      (coordinate_open c).mem_nhds hc] with q hq hqc
    change F ((sphereCoordinate c).symm (sphereCoordinate c q)) = sphereInfty at hq
    rwa [(sphereCoordinate c).left_inv hqc] at hq
  · right
    have ht := (coordinate_continuousAt c p hc) (eventually_nhdsWithin_iff.mp h.2)
    filter_upwards [ht, (coordinate_open c).mem_nhds hc] with q hq hqc hqp
    have hne : sphereCoordinate c q ≠ sphereCoordinate c p := by
      intro he
      apply hqp
      exact ((sphereCoordinate c).left_inv hqc).symm.trans
        ((congrArg (sphereCoordinate c).symm he).trans hi)
    have hh := hq hne
    change F ((sphereCoordinate c).symm (sphereCoordinate c q)) ≠ sphereInfty at hh
    rwa [(sphereCoordinate c).left_inv hqc] at hh

lemma sphere_no_infty_germ {U : Set RiemannSphere} {F : RiemannSphere → RiemannSphere}
    (hU : IsOpen U) (hconn : IsPreconnected U) (hF : SphereHolomorphicOn U F)
    (hnot : ¬ EqOn F (fun _ => sphereInfty) U) :
    ∀ p ∈ U, ¬ ∀ᶠ q in 𝓝 p, F q = sphereInfty :=
  no_infty_germ_of_connected hU hconn (fun p hp => (hF.2 p hp).1)
    (fun p hp hinf => sphere_infty_germ_or_isolated (hF.2 p hp) hinf) hnot

lemma plane_scalarMeromorphic_of_no_infty_germ {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : PlaneSphereHolomorphicOn Ω F)
    (hno : ∀ a ∈ Ω, ¬ ∀ᶠ z in 𝓝 a, F z = sphereInfty) : ScalarMeromorphicOn Ω F := by
  have hpole : ∀ a ∈ Ω, F a = sphereInfty →
      PoleAt (scalarFinitePart F) a ∧ ∀ᶠ z in 𝓝[≠] a, F z ≠ sphereInfty := by
    intro a ha hinf
    exact (plane_infty_germ_or_pole (hF.2 a ha) hinf).resolve_left (hno a ha)
  refine ⟨hF.1, ?_, ?_, ?_, (fun a ha hinf => (hpole a ha hinf).1), ?_⟩
  · have hc : Continuous (fun a : Ω => F a) :=
      (planeSphereHolomorphicOn_continuousOn Ω F hF).domRestrict
    exact isClosed_singleton.preimage hc
  · apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    intro a ha
    have hn := eventually_nhdsWithin_iff.mp (hpole a ha.1 ha.2).2
    obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp hn
    refine ⟨Metric.ball a r, Metric.isOpen_ball, ?_⟩
    ext z
    constructor
    · rintro ⟨hz, hzΩ, hzinf⟩
      apply mem_singleton_iff.mpr
      by_contra hza
      exact hb z hz hza hzinf
    · intro hz
      have hza : z = a := mem_singleton_iff.mp hz
      subst z
      exact ⟨Metric.mem_ball_self hr, ha⟩
  · refine ⟨?_, fun a ha => (planeSphereHolomorphicAt_finite (hF.2 a ha.1) ha.2).differentiableAt⟩
    exact (planeSphereHolomorphicOn_continuousOn Ω F hF).isOpen_inter_preimage hF.1
      isClosed_singleton.isOpen_compl
  · intro a ha
    by_cases hfin : F a ≠ sphereInfty
    · exact ⟨a, mem_connectedComponentIn ha, hfin⟩
    · have hinf := not_ne_iff.mp hfin
      have hn := (hpole a ha hinf).2
      have hc : ∀ᶠ z in 𝓝[≠] a, z ∈ connectedComponentIn Ω a :=
        nhdsWithin_le_nhds ((hF.1.connectedComponentIn).mem_nhds (mem_connectedComponentIn ha))
      obtain ⟨b, hbfin, hbcomp⟩ := (hn.and hc).exists
      exact ⟨b, hbcomp, hbfin⟩

lemma planeSphereHolomorphicAt_of_finite_germ {F : ℂ → RiemannSphere} {a : ℂ}
    (hg : HolomorphicGermAt (scalarFinitePart F) a)
    (hfinite : ∀ᶠ z in 𝓝 a, F z ≠ sphereInfty) : PlaneSphereHolomorphicAt F a := by
  have he : F =ᶠ[𝓝 a] (fun z => sphereFinite (scalarFinitePart F z)) :=
    hfinite.mono fun _ hz => sphere_eq_finiteCoordinate_of_ne_infty hz
  have hc : ContinuousAt F a :=
    (continuous_sphereFinite.continuousAt.comp hg.differentiableAt.continuousAt).congr_of_eventuallyEq he
  exact ⟨hc, .finite, hfinite.self_of_nhds, hg⟩

lemma planeSphereHolomorphicAt_of_reciprocal_lift {F : ℂ → RiemannSphere} {g : ℂ → ℂ} {a : ℂ}
    (hg : HolomorphicGermAt g a) (hg0 : g a = 0)
    (he : F =ᶠ[𝓝 a] (fun z => infinityParametrization (g z))) :
    PlaneSphereHolomorphicAt F a := by
  have hc : ContinuousAt F a :=
    (continuous_infinityParametrization.continuousAt.comp hg.differentiableAt.continuousAt).congr_of_eventuallyEq he
  have hinf : F a = sphereInfty := by
    calc F a = infinityParametrization (g a) := he.self_of_nhds
         _ = sphereInfty := by rw [hg0, infinityParametrization_zero]
  refine ⟨hc, .reciprocal, ?_, hg.congr ?_⟩
  · rw [hinf]; exact OnePoint.infty_ne_coe 0
  · filter_upwards [he] with z hz
    rw [hz]
    exact (infinityChart.right_inv (mem_univ (g z))).symm

lemma scalarMeromorphic_planeSphereHolomorphic {Ω : Set ℂ} {F : ℂ → RiemannSphere}
    (hF : ScalarMeromorphicOn Ω F) : PlaneSphereHolomorphicOn Ω F := by
  refine ⟨hF.1, fun a ha => ?_⟩
  by_cases hinf : F a = sphereInfty
  · obtain ⟨m, hmpos, _, R, hR, u, hu, hu0, he⟩ := hF.2.2.2.2.1 a ha hinf
    have haPole : a ∈ scalarPoleSet Ω F := ⟨ha, hinf⟩
    obtain ⟨V, hV, hVe⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hF.2.2.1 a haPole
    have haV : a ∈ V := by have := hVe ▸ (mem_singleton a); exact this.1
    have hune : ∀ᶠ z in 𝓝 a, u z ≠ 0 :=
      (hu.2 a (Metric.mem_ball_self hR)).continuousAt.eventually_ne hu0
    let g : ℂ → ℂ := fun z => (z - a)^m * (u z)⁻¹
    have hg : HolomorphicGermAt g a := by
      rw [holomorphicGermAt_iff_eventually]
      filter_upwards [Metric.ball_mem_nhds a hR, hune] with z hz hzne
      exact (((differentiableAt_id.sub_const a).pow m).mul ((hu.2 z hz).inv hzne))
    have hg0 : g a = 0 := by simp [g, zero_pow (by omega : m ≠ 0)]
    apply planeSphereHolomorphicAt_of_reciprocal_lift hg hg0
    filter_upwards [Metric.ball_mem_nhds a hR, hF.1.mem_nhds ha, hV.mem_nhds haV, hune]
      with z hz hzΩ hzV hzu
    by_cases hza : z = a
    · simpa only [hza, hg0, infinityParametrization_zero] using hinf
    · have hzfin : F z ≠ sphereInfty := by
        intro hzinf
        have hzP : z ∈ V ∩ scalarPoleSet Ω F := ⟨hzV, hzΩ, hzinf⟩
        rw [hVe] at hzP
        exact hza (mem_singleton_iff.mp hzP)
      have hpow : (z - a)^m ≠ 0 := pow_ne_zero m (sub_ne_zero.mpr hza)
      have hgn : g z ≠ 0 := mul_ne_zero hpow (inv_ne_zero hzu)
      rw [infinityParametrization_ne_zero _ hgn]
      have hzp : z ∈ puncturedDisk a R :=
        ⟨norm_pos_iff.mpr (sub_ne_zero.mpr hza), by simpa [Metric.mem_ball, dist_eq_norm] using hz⟩
      have hgeq : (g z)⁻¹ = scalarFinitePart F z := by
        simp only [g, mul_inv_rev, inv_inv]
        rw [he z hzp, mul_comm]
      rw [hgeq]
      exact sphere_eq_finiteCoordinate_of_ne_infty hzfin
  · have hf := hF.2.2.2.1
    have hmem : a ∈ {z | z ∈ Ω ∧ F z ≠ sphereInfty} := ⟨ha, hinf⟩
    exact planeSphereHolomorphicAt_of_finite_germ ⟨_, hmem, hf⟩
      (Filter.mem_of_superset (hf.1.mem_nhds hmem) fun _ hz => hz.2)

lemma SphereHolomorphicAt.congr {F G : RiemannSphere → RiemannSphere} {p : RiemannSphere}
    (hF : SphereHolomorphicAt F p) (he : F =ᶠ[𝓝 p] G) : SphereHolomorphicAt G p := by
  obtain ⟨hc, c, d, hcs, hds, hg⟩ := hF
  refine ⟨hc.congr_of_eventuallyEq he.symm, c, d, hcs, ?_, hg.congr ?_⟩
  · rwa [← he.self_of_nhds]
  · have hi := (sphereCoordinate c).left_inv hcs
    have ht : Tendsto (sphereCoordinate c).symm (𝓝 (sphereCoordinate c p)) (𝓝 p) := by
      have ht := (coordinate_inverse_continuous c).continuousAt (x := sphereCoordinate c p)
      change Tendsto _ _ (𝓝 ((sphereCoordinate c).symm (sphereCoordinate c p))) at ht
      rwa [hi] at ht
    exact Filter.mem_of_superset (ht he) fun z hz => congrArg (sphereCoordinate d) hz

theorem plane_scalar_sphere_bridge :
    Specs.D12Complex.Ch07.ScalarSphereBridge.plane_scalar_sphere_bridge_type := by
  intro Ω F hΩ
  constructor
  · intro hF
    by_cases hconst : EqOn F (fun _ => sphereInfty) Ω
    · exact Or.inr hconst
    · exact Or.inl (plane_scalarMeromorphic_of_no_infty_germ hF (plane_no_infty_germ hΩ hF hconst))
  · rintro (hscalar | hconst)
    · exact scalarMeromorphic_planeSphereHolomorphic hscalar
    · refine ⟨hΩ.2.1, fun a ha => ?_⟩
      apply ((planeSphereHolomorphicOn_const Ω sphereInfty hΩ.2.1).2 a ha).congr
      exact Filter.mem_of_superset (hΩ.2.1.mem_nhds ha) fun _ hz => (hconst hz).symm

theorem plane_infinite_values_are_poles :
    Specs.D12Complex.Ch07.ScalarSphereBridge.plane_infinite_values_are_poles_type := by
  intro Ω F hΩ hF hnot
  have hs := ((plane_scalar_sphere_bridge Ω F hΩ).mp hF).resolve_right hnot
  exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2.2.1⟩

lemma sphere_eventually_infty_of_chart {F : RiemannSphere → RiemannSphere}
    (c : SphereCoordinate) (z : ℂ)
    (he : ∀ᶠ w in 𝓝 z, (F ∘ (sphereCoordinate c).symm) w = sphereInfty) :
    ∀ᶠ p in 𝓝 ((sphereCoordinate c).symm z), F p = sphereInfty := by
  have ht : z ∈ (sphereCoordinate c).target := by cases c <;> trivial
  have hp := (sphereCoordinate c).map_target ht
  have hi := (sphereCoordinate c).right_inv ht
  have hc := coordinate_continuousAt c ((sphereCoordinate c).symm z) hp
  change Tendsto _ _ (𝓝 (sphereCoordinate c ((sphereCoordinate c).symm z))) at hc
  rw [hi] at hc
  filter_upwards [hc he, (coordinate_open c).mem_nhds hp] with p hpe hpc
  change F ((sphereCoordinate c).symm (sphereCoordinate c p)) = sphereInfty at hpe
  rwa [(sphereCoordinate c).left_inv hpc] at hpe

lemma sphere_scalarMeromorphic_of_not_const {U : Set RiemannSphere}
    {F : RiemannSphere → RiemannSphere} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hF : SphereHolomorphicOn U F) (hnot : ¬ EqOn F (fun _ => sphereInfty) U) :
    ScalarMeromorphicOnSphere U F := by
  have hno := sphere_no_infty_germ hU hconn hF hnot
  have hs : ∀ c : SphereCoordinate,
      ScalarMeromorphicOn ((sphereCoordinate c).symm ⁻¹' U) (F ∘ (sphereCoordinate c).symm) := by
    intro c
    apply plane_scalarMeromorphic_of_no_infty_germ (sphereHolomorphicOn_chart U F hF c)
    intro z hz he
    exact hno _ hz (sphere_eventually_infty_of_chart c z he)
  exact ⟨hU, hs .finite, hs .reciprocal⟩

lemma scalarMeromorphic_sphereHolomorphic {U : Set RiemannSphere}
    {F : RiemannSphere → RiemannSphere} (hF : ScalarMeromorphicOnSphere U F) :
    SphereHolomorphicOn U F := by
  have hs : ∀ c : SphereCoordinate,
      PlaneSphereHolomorphicOn ((sphereCoordinate c).symm ⁻¹' U) (F ∘ (sphereCoordinate c).symm) := by
    intro c
    apply scalarMeromorphic_planeSphereHolomorphic
    cases c
    · exact hF.2.1
    · exact hF.2.2
  refine ⟨hF.1, fun p hp => ?_⟩
  obtain ⟨c, hc⟩ := coordinate_exists p
  apply planeSphereHolomorphicAt_of_sphere_chart c hc
  apply (hs c).2
  change (sphereCoordinate c).symm (sphereCoordinate c p) ∈ U
  rwa [(sphereCoordinate c).left_inv hc]

theorem sphere_scalar_sphere_bridge :
    Specs.D12Complex.Ch07.ScalarSphereBridge.sphere_scalar_sphere_bridge_type := by
  intro U F hU hconn
  constructor
  · intro hF
    by_cases hconst : EqOn F (fun _ => sphereInfty) U
    · exact Or.inr hconst
    · exact Or.inl (sphere_scalarMeromorphic_of_not_const hU hconn.2 hF hconst)
  · rintro (hscalar | hconst)
    · exact scalarMeromorphic_sphereHolomorphic hscalar
    · refine ⟨hU, fun p hp => ?_⟩
      apply ((sphereHolomorphicOn_const U sphereInfty hU).2 p hp).congr
      exact Filter.mem_of_superset (hU.mem_nhds hp) fun _ hq => (hconst hq).symm

theorem sphere_infinite_values_are_poles :
    Specs.D12Complex.Ch07.ScalarSphereBridge.sphere_infinite_values_are_poles_type := by
  intro U F hU hconn hF hnot
  have hs := sphere_scalarMeromorphic_of_not_const hU hconn.2 hF hnot
  have hno := sphere_no_infty_germ hU hconn.2 hF hnot
  refine ⟨?_, ?_, ?_⟩
  · have hc : Continuous (fun p : U => F p) :=
      (sphereHolomorphicOn_continuousOn U F hF).domRestrict
    exact isClosed_singleton.preimage hc
  · apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
    intro p hp
    have hn := (sphere_infty_germ_or_isolated (hF.2 p hp.1) hp.2).resolve_left (hno p hp.1)
    obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp hn
    refine ⟨V, hVo, ?_⟩
    ext q
    constructor
    · rintro ⟨hqV, hqU, hqinf⟩
      apply mem_singleton_iff.mpr
      by_contra hqp
      exact hV hqV hqp hqinf
    · intro hq
      have he : q = p := mem_singleton_iff.mp hq
      subst q
      exact ⟨hpV, hp⟩
  · intro c p hp hc hinf
    have hscalar : ScalarMeromorphicOn ((sphereCoordinate c).symm ⁻¹' U)
        (F ∘ (sphereCoordinate c).symm) := by
      cases c
      · exact hs.2.1
      · exact hs.2.2
    have hi := (sphereCoordinate c).left_inv hc
    apply hscalar.2.2.2.2.1 (sphereCoordinate c p)
    · change (sphereCoordinate c).symm (sphereCoordinate c p) ∈ U
      rwa [hi]
    · simpa only [Function.comp_apply, hi] using hinf

/-- Compactness supplies a bounded scalar range; Liouville applies to its finite
source coordinate, and density supplies the value at source infinity. -/
theorem finite_valued_sphere_holomorphic_constant :
    Specs.D12Complex.Ch07.ScalarSphereBridge.finite_valued_sphere_holomorphic_constant_type := by
  intro f hf
  have hcf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have h := (hf.2 p (mem_univ p)).1
    have ht : ContinuousAt (fun q => finiteCoordinate ((sphereFinite ∘ f) q)) p :=
      (show ContinuousAt finiteCoordinate ((sphereFinite ∘ f) p) from
        coordinate_continuousAt .finite (sphereFinite (f p)) (OnePoint.coe_ne_infty (f p))).comp h
    exact ht
  have hdiff : Differentiable ℂ (fun z => f (sphereFinite z)) := by
    intro z
    have hg := (hf.2 (sphereFinite z) (mem_univ _)).plane_chart .finite
      (OnePoint.coe_ne_infty z)
    exact (planeSphereHolomorphicAt_finite hg (OnePoint.coe_ne_infty _)).differentiableAt
  have hb : Bornology.IsBounded (range (fun z => f (sphereFinite z))) := by
    exact (isCompact_univ.image hcf).isBounded.subset (by
      rintro _ ⟨z, rfl⟩; exact ⟨sphereFinite z, mem_univ _, rfl⟩)
  obtain ⟨c, hc⟩ := hdiff.exists_const_forall_eq_of_bounded hb
  refine ⟨c, ?_⟩
  have he : f = fun _ => c := sphereFinite_denseRange.equalizer hcf continuous_const (funext hc)
  exact congrFun he

theorem sphere_holomorphic_omitting_infty_constant :
    Specs.D12Complex.Ch07.ScalarSphereBridge.sphere_holomorphic_omitting_infty_constant_type := by
  intro F hF hfin
  let f : RiemannSphere → ℂ := fun p => finiteCoordinate (F p)
  have he : sphereFinite ∘ f = F := by
    funext p
    exact (sphere_eq_finiteCoordinate_of_ne_infty (hfin p)).symm
  have hf : SphereHolomorphicOn univ (sphereFinite ∘ f) := by rwa [he]
  obtain ⟨c, hc⟩ := finite_valued_sphere_holomorphic_constant f hf
  exact ⟨c, fun p => (sphere_eq_finiteCoordinate_of_ne_infty (hfin p)).trans
    (congrArg sphereFinite (hc p))⟩

end D12Complex
