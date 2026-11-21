import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.WeierstrassDegreeBranching
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.HalfPeriodValues
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch07.ScalarSphereBridge
import Mathlib.Analysis.Calculus.Deriv.Shift

noncomputable section
open Set Filter
open scoped Topology Classical

namespace D12Complex.Ch22.WeierstrassDegreeBranching
open TorusSurface
open Specs.D12Complex.Ch22.WeierstrassDegreeBranching
open Specs.D12Complex.Ch22.HalfPeriodValues (halfPeriod branchValue)
open WeierstrassSeries (weierstrassP periodPair)

lemma planeMap_eq_fill {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    planeMap ω₁ ω₂ = LocalQuotientsArithmetic.fill (weierstrassP ω₁ ω₂) := by
  funext z
  by_cases hz : z ∈ lattice ω₁ ω₂
  · simp only [planeMap, ite_eq_left hz]
    exact (LocalQuotientsArithmetic.fill_eq_infty_iff _ _).mpr (by
      rw [WeierstrassSeries.pole_order ω₁ ω₂ h₁ h₂ z hz]
      exact WithTop.coe_lt_coe.mpr (by norm_num : (-2 : ℤ) < 0)) |>.symm
  · rw [planeMap, ite_eq_right hz]
    exact (LocalQuotientsArithmetic.fill_of_analyticAt
      ((periodPair h₁ h₂).analyticOnNhd_weierstrassP z hz)).symm

lemma planeMap_periodic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    Periodic ω₁ ω₂ (planeMap ω₁ ω₂) := by
  intro z l hl
  have hm : z + l ∈ lattice ω₁ ω₂ ↔ z ∈ lattice ω₁ ω₂ :=
    add_mem_cancel_right hl
  change (if z + l ∈ lattice ω₁ ω₂ then sphereInfty else
    sphereFinite (weierstrassP ω₁ ω₂ (z+l))) =
    (if z ∈ lattice ω₁ ω₂ then sphereInfty else sphereFinite (weierstrassP ω₁ ω₂ z))
  rw [hm]
  split_ifs
  · rfl
  · exact congrArg sphereFinite ((periodPair h₁ h₂).weierstrassP_add_coe z ⟨l, hl⟩)

lemma planeMap_holomorphic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    PlaneSphereHolomorphicOn univ (planeMap ω₁ ω₂) := by
  rw [planeMap_eq_fill h₁ h₂]
  exact (plane_scalar_sphere_bridge univ _ ⟨⟨0, trivial⟩, isOpen_univ,
    isPreconnected_univ⟩).mpr (Or.inl
      (LocalQuotientsArithmetic.scalarMeromorphicOn_fill univ isOpen_univ _
        (fun z _ => (periodPair h₁ h₂).meromorphic_weierstrassP z)))

/-- The local finite order is two at critical points and one elsewhere. -/
lemma finite_order {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {a : ℂ} (ha : a ∉ lattice ω₁ ω₂) :
    analyticOrderAt (fun z => weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ a) a =
      (multiplicity ω₁ ω₂ (projection ω₁ ω₂ a) : ℕ∞) := by
  let L := periodPair h₁ h₂
  have han := L.analyticOnNhd_weierstrassP a ha
  have hz : projection ω₁ ω₂ a ≠ 0 :=
    (HalfPeriodValues.projection_zero_iff a).not.mpr ha
  by_cases hd : deriv (weierstrassP ω₁ ω₂) a = 0
  · obtain ⟨i, hi⟩ := (HalfPeriodValues.zeros ω₁ ω₂ h₁ h₂ a ha).mp hd
    have hdo : analyticOrderAt (deriv L.weierstrassP) a = 1 :=
      HalfPeriodValues.analytic_order_of_meromorphic han.deriv (n := 1)
        (HalfPeriodValues.all_simple_zeros ω₁ ω₂ h₁ h₂ a ha hd)
    have hm : multiplicity ω₁ ω₂ (projection ω₁ ω₂ a) = 2 := by
      apply ite_eq_left
      exact Or.inr ⟨i, hi.symm⟩
    rw [hm]
    have he := han.analyticOrderAt_deriv_add_one
    rw [hdo] at he
    exact he.symm
  · have hdo : analyticOrderAt (deriv L.weierstrassP) a = 0 :=
      han.deriv.analyticOrderAt_eq_zero.mpr hd
    have hm : multiplicity ω₁ ω₂ (projection ω₁ ω₂ a) = 1 := by
      apply ite_eq_right
      rintro (h | ⟨i, hi⟩)
      · exact hz h
      · exact hd ((HalfPeriodValues.zeros ω₁ ω₂ h₁ h₂ a ha).mpr ⟨i, hi.symm⟩)
    rw [hm]
    have he := han.analyticOrderAt_deriv_add_one
    rw [hdo] at he
    exact he.symm

/-- At a pole the reciprocal target coordinate has a zero of order two. -/
lemma reciprocal_order {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {a : ℂ} (ha : a ∈ lattice ω₁ ω₂) :
    analyticOrderAt (fun z => infinityCoordinate (planeMap ω₁ ω₂ z)) a = 2 := by
  have hInf : planeMap ω₁ ω₂ a = sphereInfty := by simp [planeMap, ha]
  have hg := ((planeSphereHolomorphicAt_infty _ _ hInf).1.mp
    ((planeMap_holomorphic h₁ h₂).2 a trivial)).2
  have han : AnalyticAt ℂ (fun z => infinityCoordinate (planeMap ω₁ ω₂ z)) a :=
    Complex.analyticAt_iff_eventually_differentiableAt.mpr
      ((holomorphicGermAt_iff_eventually _ _).mp hg)
  apply HalfPeriodValues.analytic_order_of_meromorphic han (n := 2)
  have he : (fun z => infinityCoordinate (planeMap ω₁ ω₂ z)) =ᶠ[𝓝[≠] a]
      (fun z => (weierstrassP ω₁ ω₂ z)⁻¹) := by
    rw [planeMap_eq_fill h₁ h₂]
    filter_upwards [(periodPair h₁ h₂).meromorphic_weierstrassP a |>.eventually_analyticAt]
      with z hz
    change AnalyticAt ℂ (weierstrassP ω₁ ω₂) z at hz
    rw [LocalQuotientsArithmetic.fill_of_analyticAt hz, infinityCoordinate_sphereFinite]
  rw [meromorphicOrderAt_congr he]
  change meromorphicOrderAt (weierstrassP ω₁ ω₂)⁻¹ a = _
  rw [meromorphicOrderAt_inv, WeierstrassSeries.pole_order ω₁ ω₂ h₁ h₂ a ha]
  rfl

lemma finite_coordinate_germ {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {a : ℂ} (ha : a ∉ lattice ω₁ ω₂) :
    (fun z => finiteCoordinate (planeMap ω₁ ω₂ z)) =ᶠ[𝓝 a] weierstrassP ω₁ ω₂ := by
  filter_upwards [((periodPair h₁ h₂).isClosed_lattice.isOpen_compl.mem_nhds ha)] with z hz
  change z ∉ lattice ω₁ ω₂ at hz
  simp [planeMap, hz, finiteCoordinate_sphereFinite]

lemma descended_holomorphic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {d : ℝ} {S : Surfaces.RiemannSurface (Torus ω₁ ω₂)}
    (hS : S.atlas = quotientAtlas ω₁ ω₂ d)
    {F : Torus ω₁ ω₂ → RiemannSphere}
    (hF : F ∘ projection ω₁ ω₂ = planeMap ω₁ ω₂) :
    Surfaces.SphereValuedHolomorphic S F := by
  have hp := planeMap_holomorphic h₁ h₂
  constructor
  · apply QuotientAddGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff.mpr
    change Continuous (F ∘ projection ω₁ ω₂)
    rw [hF]
    exact continuous_iff_continuousAt.mpr (fun z => (hp.2 z trivial).1)
  · intro e he
    rw [hS] at he
    refine ⟨e.val.open_target, fun z hz => ?_⟩
    apply (hp.2 z trivial).congr
    exact (e.val.open_target.eventually_mem hz).mono fun w hw =>
      (descent_in_chart hF he hw).symm

lemma descent_apply {ω₁ ω₂ : ℂ} {F : Torus ω₁ ω₂ → RiemannSphere}
    (hF : F ∘ projection ω₁ ω₂ = planeMap ω₁ ω₂) (a : ℂ) :
    F (projection ω₁ ω₂ a) = planeMap ω₁ ω₂ a := congrFun hF a

lemma descended_poles {ω₁ ω₂ : ℂ} {F : Torus ω₁ ω₂ → RiemannSphere}
    (hF : F ∘ projection ω₁ ω₂ = planeMap ω₁ ω₂) (q : Torus ω₁ ω₂) :
    F q = sphereInfty ↔ q = 0 := by
  classical
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup q
  change F (projection ω₁ ω₂ a) = sphereInfty ↔ projection ω₁ ω₂ a = 0
  rw [descent_apply hF a, HalfPeriodValues.projection_zero_iff]
  simp only [planeMap]
  split_ifs with ha
  · simp [ha]
  · simp [ha, sphereFinite, sphereInfty]

lemma coordinate_orders {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {d : ℝ} {e : Surfaces.ComplexChart (Torus ω₁ ω₂)}
    (he : e ∈ quotientAtlas ω₁ ω₂ d) {F : Torus ω₁ ω₂ → RiemannSphere}
    (hF : F ∘ projection ω₁ ω₂ = planeMap ω₁ ω₂)
    {q : Torus ω₁ ω₂} (hq : q ∈ e.val.source) :
    (F q ≠ sphereInfty →
      analyticOrderAt (fun z => finiteCoordinate (F (e.val.symm z)) -
        finiteCoordinate (F q)) (e.val q) = (multiplicity ω₁ ω₂ q : ℕ∞)) ∧
    (F q = sphereInfty →
      analyticOrderAt (fun z => infinityCoordinate (F (e.val.symm z)))
        (e.val q) = 2) := by
  have hq' : projection ω₁ ω₂ (e.val q) = q :=
    (chart_lift he (e.val.map_source hq)).symm.trans (e.val.left_inv hq)
  have hFa : F q = planeMap ω₁ ω₂ (e.val q) := by
    exact (congrArg F hq').symm.trans (descent_apply hF _)
  have hg : (F ∘ e.val.symm) =ᶠ[𝓝 (e.val q)] planeMap ω₁ ω₂ :=
    (e.val.open_target.eventually_mem (e.val.map_source hq)).mono
      (fun z hz => descent_in_chart hF he hz)
  constructor
  · intro hfin
    have ha : e.val q ∉ lattice ω₁ ω₂ := by
      intro ha
      exact hfin (hFa.trans (by simp [planeMap, ha]))
    have hval : finiteCoordinate (F q) = weierstrassP ω₁ ω₂ (e.val q) := by
      rw [hFa]; simp [planeMap, ha, finiteCoordinate_sphereFinite]
    have hfg₀ : (fun z => finiteCoordinate (F (e.val.symm z))) =ᶠ[𝓝 (e.val q)]
        (fun z => finiteCoordinate (planeMap ω₁ ω₂ z)) :=
      hg.mono fun z hz => congrArg finiteCoordinate hz
    have hfg := hfg₀.trans (finite_coordinate_germ h₁ h₂ ha)
    have hcenter : (fun z => finiteCoordinate (F (e.val.symm z)) - finiteCoordinate (F q))
        =ᶠ[𝓝 (e.val q)] (fun z => weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ (e.val q)) :=
      hfg.mono fun z hz => congrArg₂ (· - ·) hz hval
    exact (analyticOrderAt_congr hcenter).trans (by
      simpa only [hq'] using finite_order h₁ h₂ ha)
  · intro hinf
    have ha : e.val q ∈ lattice ω₁ ω₂ := by
      apply (HalfPeriodValues.projection_zero_iff _).mp
      rw [hq']; exact (descended_poles hF q).mp hinf
    have heq : (fun z => infinityCoordinate (F (e.val.symm z))) =ᶠ[𝓝 (e.val q)]
        (fun z => infinityCoordinate (planeMap ω₁ ω₂ z)) :=
      hg.mono fun z hz => congrArg infinityCoordinate hz
    exact (analyticOrderAt_congr heq).trans (reciprocal_order h₁ h₂ ha)

/-- Fibre divisors have the actual local coordinate orders as coefficients. -/
lemma finite_fiber_divisor {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {F : Torus ω₁ ω₂ → RiemannSphere}
    (hF : F ∘ projection ω₁ ω₂ = planeMap ω₁ ω₂) (c : ℂ) :
    ∃ D : Torus ω₁ ω₂ →₀ ℕ,
      (∀ q, D q ≠ 0 ↔ F q = sphereFinite c) ∧
      (∀ q, F q = sphereFinite c → D q = multiplicity ω₁ ω₂ q) ∧
      D.sum (fun _ n => n) = 2 := by
  classical
  let L := periodPair h₁ h₂
  obtain ⟨D, hD, ht⟩ := HalfPeriodValues.shifted_divisor h₁ h₂ c
  have hpos (a : ℂ) (ha : a ∉ lattice ω₁ ω₂) :
      D (projection ω₁ ω₂ a) ≠ 0 ↔ weierstrassP ω₁ ω₂ a = c := by
    rw [(hD a).2, ← Nat.pos_iff_ne_zero, HalfPeriodValues.nat_order_pos (hD a).1]
    have han : AnalyticAt ℂ (fun z => weierstrassP ω₁ ω₂ z - c) a :=
      (L.analyticOnNhd_weierstrassP a ha).sub analyticAt_const
    exact (HalfPeriodValues.analytic_zero_iff_order_pos han).symm.trans sub_eq_zero
  have hpole (a : ℂ) (ha : a ∈ lattice ω₁ ω₂) : D (projection ω₁ ω₂ a) = 0 := by
    have hm : MeromorphicAt (weierstrassP ω₁ ω₂) a := L.meromorphic_weierstrassP a
    have hp : meromorphicOrderAt (weierstrassP ω₁ ω₂) a < 0 := by
      rw [WeierstrassSeries.pole_order ω₁ ω₂ h₁ h₂ a ha]
      exact WithTop.coe_lt_coe.mpr (by norm_num : (-2 : ℤ) < 0)
    rw [(hD a).2, (DivisorDegree.pole_order_sub_const hm c).2 hp,
      WeierstrassSeries.pole_order ω₁ ω₂ h₁ h₂ a ha]
    rfl
  refine ⟨D, ?_, ?_, ht⟩
  · intro q
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup q
    change D (projection ω₁ ω₂ a) ≠ 0 ↔ F (projection ω₁ ω₂ a) = sphereFinite c
    rw [descent_apply hF a]
    by_cases ha : a ∈ lattice ω₁ ω₂
    · simp [hpole a ha, planeMap, ha, sphereFinite, sphereInfty]
    · simpa [planeMap, ha, sphereFinite_injective.eq_iff] using hpos a ha
  · intro q hqc
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (lattice ω₁ ω₂).toAddSubgroup q
    change F (projection ω₁ ω₂ a) = sphereFinite c at hqc
    change D (projection ω₁ ω₂ a) = multiplicity ω₁ ω₂ (projection ω₁ ω₂ a)
    have ha : a ∉ lattice ω₁ ω₂ := by
      intro ha
      have hc := (congrFun hF a).symm.trans hqc
      simpa [planeMap, ha, sphereFinite, sphereInfty] using hc
    have hac : weierstrassP ω₁ ω₂ a = c := by
      have hc := (congrFun hF a).symm.trans hqc
      simpa [planeMap, ha, sphereFinite_injective.eq_iff] using hc
    have han : AnalyticAt ℂ (fun z => weierstrassP ω₁ ω₂ z - weierstrassP ω₁ ω₂ a) a :=
      (L.analyticOnNhd_weierstrassP a ha).sub analyticAt_const
    rw [(hD a).2, ← hac, han.meromorphicOrderAt_eq, finite_order h₁ h₂ ha]
    simp

lemma multiplicity_zero (ω₁ ω₂ : ℂ) : multiplicity ω₁ ω₂ 0 = 2 := by
  classical
  exact ite_eq_left (Or.inl rfl)

lemma ramification_classes (ω₁ ω₂ : ℂ) :
    {q | 1 < multiplicity ω₁ ω₂ q} = ramificationClasses ω₁ ω₂ := by
  classical
  ext q
  change (1 < if q ∈ ramificationClasses ω₁ ω₂ then 2 else 1) ↔
    q ∈ ramificationClasses ω₁ ω₂
  split_ifs <;> simp_all

theorem degree_branching :
    Specs.D12Complex.Ch22.WeierstrassDegreeBranching.degree_branching_type := by
  classical
  intro ω₁ ω₂ h₁ h₂
  obtain ⟨d, hd, _, S, hS, _⟩ := compact_surface ω₁ ω₂ h₁ h₂
  obtain ⟨F, hF, _⟩ := descent ω₁ ω₂ RiemannSphere (planeMap ω₁ ω₂)
    (planeMap_periodic h₁ h₂)
  have hInf := descended_poles hF
  have h0 : F 0 = sphereInfty := (hInf 0).mpr rfl
  have hhalf (i : Fin 3) : F (projection ω₁ ω₂ (halfPeriod ω₁ ω₂ i)) =
      sphereFinite (branchValue ω₁ ω₂ i) := by
    rw [descent_apply hF _]
    exact ite_eq_right ((HalfPeriodValues.classes ω₁ ω₂ h₁ h₂).2.1 i)
  refine ⟨d, S, F, hd, hS, hF, descended_holomorphic h₁ h₂ hS hF, hInf, hhalf,
    ?_, ?_, ramification_classes ω₁ ω₂, ?_⟩
  · intro e he q hq
    rw [hS] at he
    exact coordinate_orders h₁ h₂ he hF hq
  · intro b
    rcases sphere_eq_infty_or_finite b with rfl | ⟨c, rfl⟩
    · refine ⟨Finsupp.single 0 2, ?_, ?_, by simp⟩
      · intro q
        rw [hInf]
        by_cases hq : q = 0 <;> simp [hq, Finsupp.single_eq_of_ne]
      · intro q hq
        rw [(hInf q).mp hq, multiplicity_zero]
        simp
    · exact finite_fiber_divisor h₁ h₂ hF c
  · rw [ramification_classes, ramificationClasses, image_union, image_singleton, h0,
      ← range_comp]
    congr 1
    ext p
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, (hhalf i).symm.trans hi⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, (hhalf i).trans hi⟩


end D12Complex.Ch22.WeierstrassDegreeBranching
