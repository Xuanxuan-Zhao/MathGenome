import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch22.TorusCubicLocalMap
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.TorusSurface
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.WeierstrassEquations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch22.CubicInfinityChart
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch05.LocalHolomorphicInverse
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! The literal quotient map to the associated cubic, with actual holomorphic
local inverses. At infinity regularized Weierstrass sums give analytic numerator
and denominator functions; Taylor factorization proves the two remainder orders.
Finite points use x if wp' is nonzero, and y at its simple zeros. -/

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.TorusCubicLocalMap
open D12Complex.Ch22.WeierstrassSeries (weierstrassP periodPair)
open D12Complex.Ch22
abbrev lattice := TorusSurface.lattice
open WeierstrassEquations (g₂ g₃)
open CubicFiniteCharts CubicInfinityChart
abbrev E (ω₁ ω₂ : ℂ) := Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)

lemma planeMap_mem {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) (z : ℂ) :
    OnCubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) (planeMap ω₁ ω₂ z) := by
  classical
  unfold planeMap
  split_ifs with hz
  · exact O_onCubic _ _
  · exact (onCubic_affinePoint_iff _ _ _ _).mpr
      (WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ z hz)

lemma planeMap_periodic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    TorusSurface.Periodic ω₁ ω₂ (planeMap ω₁ ω₂) := by
  classical
  intro z l hl
  have hmem : z + l ∈ lattice ω₁ ω₂ ↔ z ∈ lattice ω₁ ω₂ := by
    exact (lattice ω₁ ω₂).add_mem_iff_left hl
  unfold planeMap
  by_cases hz : z ∈ lattice ω₁ ω₂
  · simp [hz, hmem.mpr hz]
  · have hp : weierstrassP ω₁ ω₂ (z+l) = weierstrassP ω₁ ω₂ z :=
      (periodPair h₁ h₂).weierstrassP_add_coe z ⟨l, hl⟩
    have hq : deriv (weierstrassP ω₁ ω₂) (z+l) = deriv (weierstrassP ω₁ ω₂) z := by
      change deriv (periodPair h₁ h₂).weierstrassP (z+l) =
        deriv (periodPair h₁ h₂).weierstrassP z
      rw [(periodPair h₁ h₂).deriv_weierstrassP]
      exact (periodPair h₁ h₂).derivWeierstrassP_add_coe z ⟨l, hl⟩
    simp [hz, hmem.not.mpr hz, hp, hq]

lemma phi_projection {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) (z : ℂ) :
    phi ω₁ ω₂ (TorusSurface.projection ω₁ ω₂ z) = planeMap ω₁ ω₂ z := by
  apply TorusSurface.periodic_eq_of_projection_eq (planeMap_periodic h₁ h₂)
  exact Quotient.out_eq _

lemma phi_onCubic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (x : TorusSurface.Torus ω₁ ω₂) : OnCubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) (phi ω₁ ω₂ x) :=
  planeMap_mem h₁ h₂ _

def map {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (x : TorusSurface.Torus ω₁ ω₂) : E ω₁ ω₂ :=
  ⟨phi ω₁ ω₂ x, phi_onCubic h₁ h₂ x⟩

def lift {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (z : ℂ) : E ω₁ ω₂ := map h₁ h₂ (TorusSurface.projection ω₁ ω₂ z)

lemma lift_val {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) (z : ℂ) :
    (lift h₁ h₂ z).val = planeMap ω₁ ω₂ z := phi_projection h₁ h₂ z

lemma phi_finite {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {z : ℂ} (hz : z ∉ lattice ω₁ ω₂) :
    phi ω₁ ω₂ (TorusSurface.projection ω₁ ω₂ z) =
      affinePoint (weierstrassP ω₁ ω₂ z) (deriv (weierstrassP ω₁ ω₂) z) := by
  rw [phi_projection h₁ h₂]
  simp [planeMap, hz]

lemma lift_finite {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {z : ℂ} (hz : z ∉ lattice ω₁ ω₂) :
    (lift h₁ h₂ z).val =
      affinePoint (weierstrassP ω₁ ω₂ z) (deriv (weierstrassP ω₁ ω₂) z) :=
  phi_finite h₁ h₂ hz

lemma phi_zero {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    phi ω₁ ω₂ (0 : TorusSurface.Torus ω₁ ω₂) = O := by
  have hp : TorusSurface.projection ω₁ ω₂ 0 = 0 := map_zero _
  rw [← hp, phi_projection h₁ h₂]
  simp [planeMap]

lemma lift_zero {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im) :
    (lift h₁ h₂ 0).val = O := by
  simpa only [lift, map, map_zero] using phi_zero h₁ h₂

end D12Complex.TorusCubicLocalMap

namespace D12Complex.Ch22.TorusCubicLocalMap
abbrev planeMap : Specs.D12Complex.Ch22.TorusCubicLocalMap.planeMap_type :=
  _root_.D12Complex.TorusCubicLocalMap.planeMap
abbrev phi : Specs.D12Complex.Ch22.TorusCubicLocalMap.phi_type :=
  _root_.D12Complex.TorusCubicLocalMap.phi
end D12Complex.Ch22.TorusCubicLocalMap

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.TorusCubicLocalMap
open CubicFiniteCharts
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂ g₃)
open TorusSurface (lattice)

lemma wp_derivative_holomorphic {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) :
    HolomorphicOn (lattice ω₁ ω₂ : Set ℂ)ᶜ (deriv (weierstrassP ω₁ ω₂)) := by
  have hh := Ch22.WeierstrassSeries.holomorphic ω₁ ω₂ h₁ h₂
  refine ⟨hh.1, fun z hz => ?_⟩
  have hd : DifferentiableOn ℂ (weierstrassP ω₁ ω₂) (lattice ω₁ ω₂ : Set ℂ)ᶜ :=
    fun z hz => (hh.2 z hz).differentiableWithinAt
  exact (hd.analyticAt (hh.1.mem_nhds hz)).deriv.differentiableAt

lemma wp_second_derivative_ne_zero {ω₁ ω₂ a : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (ha : a ∉ lattice ω₁ ω₂)
    (hd : deriv (weierstrassP ω₁ ω₂) a = 0) :
    deriv (deriv (weierstrassP ω₁ ω₂)) a ≠ 0 := by
  have heq := Ch22.WeierstrassEquations.first_equation ω₁ ω₂ h₁ h₂ a ha
  have hroot : q (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) (weierstrassP ω₁ ω₂ a) = 0 := by
    simpa [hd, q] using heq.symm
  have hn := cubic_derivative_ne_zero (Ch22.HalfPeriodValues.discriminant ω₁ ω₂ h₁ h₂) hroot
  rw [Ch22.WeierstrassEquations.second_equation ω₁ ω₂ h₁ h₂ a ha]
  intro hz
  apply hn
  linear_combination 2 * hz

lemma finite_lift_continuousAt {ω₁ ω₂ a : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (ha : a ∉ lattice ω₁ ω₂)
    (F : ℂ → Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂))
    (hF : ∀ z ∉ lattice ω₁ ω₂,
      (F z).val = affinePoint (weierstrassP ω₁ ω₂ z)
        (deriv (weierstrassP ω₁ ω₂) z)) : ContinuousAt F a := by
  apply tendsto_subtype_rng.mpr
  have hh := Ch22.WeierstrassSeries.holomorphic ω₁ ω₂ h₁ h₂
  have hy := wp_derivative_holomorphic h₁ h₂
  have hc := continuous_affinePoint.continuousAt.comp
    ((hh.2 a ha).continuousAt.prodMk (hy.2 a ha).continuousAt)
  apply hc.congr_of_eventuallyEq
  exact (hh.1.eventually_mem ha).mono fun z hz => hF z hz

lemma finite_chart_inverse {ω₁ ω₂ a : ℂ} (h₁ : ω₁ ≠ 0)
    (h₂ : 0 < (ω₂ / ω₁).im) (ha : a ∉ lattice ω₁ ω₂)
    (F : ℂ → Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂))
    (hF : ∀ z ∉ lattice ω₁ ω₂,
      (F z).val = affinePoint (weierstrassP ω₁ ω₂ z)
        (deriv (weierstrassP ω₁ ω₂) z)) :
    ∃ e : OpenPartialHomeomorph (Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)) ℂ,
      IsFiniteChart (g₂ ω₁ ω₂) (g₃ ω₁ ω₂)
        (if deriv (weierstrassP ω₁ ω₂) a = 0 then false else true) e ∧
      ∃ (U V : Set ℂ) (h : ℂ → ℂ), a ∈ U ∧
        MapsTo F U e.source ∧ BiholomorphicPair U V (e ∘ F) h := by
  have hh := Ch22.WeierstrassSeries.holomorphic ω₁ ω₂ h₁ h₂
  have hy := wp_derivative_holomorphic h₁ h₂
  have hp : F a ∈ finitePatch (g₂ ω₁ ω₂) (g₃ ω₁ ω₂) := by
    change (F a).val ∈ ProjectivePlaneTopology.coordinatePatch 0
    rw [hF a ha]
    exact affinePoint_mem_patch _ _
  have hya : finiteY (F a).val = deriv (weierstrassP ω₁ ω₂) a := by
    rw [hF a ha]
    simp
  obtain ⟨e, hea, he⟩ := finite_charts ω₁ ω₂ h₁ h₂ (F a) hp
  rw [hya] at he
  let Ω := {z | z ∉ lattice ω₁ ω₂ ∧ F z ∈ e.source}
  have hΩ : IsOpen Ω := by
    have hc : ContinuousOn F (lattice ω₁ ω₂ : Set ℂ)ᶜ :=
      fun z hz => (finite_lift_continuousAt h₁ h₂ hz F hF).continuousWithinAt
    exact hc.isOpen_inter_preimage hh.1 e.open_source
  have haΩ : a ∈ Ω := ⟨ha, hea⟩
  let axis := if deriv (weierstrassP ω₁ ω₂) a = 0 then false else true
  let f : ℂ → ℂ := fun z => if axis then weierstrassP ω₁ ω₂ z
    else deriv (weierstrassP ω₁ ω₂) z
  have hf : HolomorphicOn Ω f := by
    cases hc : axis
    · exact ⟨hΩ, fun z hz => by simpa [f, hc] using hy.2 z hz.1⟩
    · exact ⟨hΩ, fun z hz => by simpa [f, hc] using hh.2 z hz.1⟩
  have hEq : EqOn (e ∘ F) f Ω := by
    intro z hz
    change e (F z) = f z
    rw [he.2.1 (F z) hz.2, hF z hz.1]
    change coordinate axis (affinePoint (weierstrassP ω₁ ω₂ z)
      (deriv (weierstrassP ω₁ ω₂) z)) = f z
    cases hc : axis <;> simp [coordinate, f, hc]
  have hhol : HolomorphicOn Ω (e ∘ F) := by
    refine ⟨hΩ, fun z hz => ?_⟩
    apply (hf.2 z hz).congr_of_eventuallyEq
    exact (hΩ.eventually_mem hz).mono fun w hw => hEq hw
  have hne : deriv (e ∘ F) a ≠ 0 := by
    have hdEq : deriv (e ∘ F) a = deriv f a :=
      Filter.EventuallyEq.deriv_eq ((hΩ.eventually_mem haΩ).mono fun z hz => hEq hz)
    rw [hdEq]
    by_cases hd : deriv (weierstrassP ω₁ ω₂) a = 0
    · simpa [f, axis, hd] using wp_second_derivative_ne_zero h₁ h₂ ha hd
    · simp [f, axis, hd]
  obtain ⟨U, V, h, haU, _, hUΩ, hbi, _⟩ :=
    LocalHolomorphicInverse.local_holomorphic_inverse Ω (e ∘ F) a hhol haΩ hne
  exact ⟨e, he, U, V, h, haU, fun z hz => (hUΩ hz).2, hbi⟩

end D12Complex.TorusCubicLocalMap

noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace D12Complex.TorusCubicLocalMap.InfinityCoordinates

def numerator (L : PeriodPair) (z : ℂ) : ℂ := 1 + z^2 * L.weierstrassPExcept 0 z
def denominator (L : PeriodPair) (z : ℂ) : ℂ := -2 + z^3 * L.derivWeierstrassPExcept 0 z
def u (L : PeriodPair) (z : ℂ) : ℂ := z * numerator L z / denominator L z
def v (L : PeriodPair) (z : ℂ) : ℂ := z^3 / denominator L z

@[simp] theorem numerator_zero (L : PeriodPair) : numerator L 0 = 1 := by simp [numerator]
@[simp] theorem denominator_zero (L : PeriodPair) : denominator L 0 = -2 := by simp [denominator]
@[simp] theorem u_zero (L : PeriodPair) : u L 0 = 0 := by simp [u]
@[simp] theorem v_zero (L : PeriodPair) : v L 0 = 0 := by simp [v]

theorem numerator_analytic (L : PeriodPair) : AnalyticAt ℂ (numerator L) 0 := by
  unfold numerator
  exact analyticAt_const.add ((analyticAt_id.pow 2).mul (L.analyticAt_weierstrassPExcept 0))
theorem denominator_analytic (L : PeriodPair) : AnalyticAt ℂ (denominator L) 0 := by
  unfold denominator
  exact analyticAt_const.add ((analyticAt_id.pow 3).mul (L.analyticAt_derivWeierstrassPExcept 0))
theorem u_analytic (L : PeriodPair) : AnalyticAt ℂ (u L) 0 := by
  exact (analyticAt_id.mul (numerator_analytic L)).div (denominator_analytic L) (by simp)
theorem v_analytic (L : PeriodPair) : AnalyticAt ℂ (v L) 0 := by
  exact (analyticAt_id.pow 3).div (denominator_analytic L) (by simp)

theorem u_hasDerivAt (L : PeriodPair) : HasDerivAt (u L) (-1/2) 0 := by
  have h := (((hasDerivAt_id (0:ℂ)).mul (numerator_analytic L).differentiableAt.hasDerivAt).div
    (denominator_analytic L).differentiableAt.hasDerivAt (by simp : denominator L 0 ≠ 0))
  convert h using 1
  · rfl
  · norm_num

theorem regular_factorizations (L : PeriodPair) :
    ∃ a b : ℂ → ℂ, AnalyticAt ℂ a 0 ∧ AnalyticAt ℂ b 0 ∧
      (∀ᶠ z in 𝓝 (0:ℂ), L.weierstrassPExcept 0 z = z^2*a z) ∧
      (∀ᶠ z in 𝓝 (0:ℂ), L.derivWeierstrassPExcept 0 z = z*b z) := by
  obtain ⟨a, ha, hpa⟩ := (L.analyticAt_weierstrassPExcept 0).exists_eventuallyEq_sum_add_pow_mul 2
  obtain ⟨b, hb, hpb⟩ := (L.analyticAt_derivWeierstrassPExcept 0).exists_eventuallyEq_sum_add_pow_mul 1
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · filter_upwards [hpa] with z hz
    simpa [Finset.sum_range_succ, iteratedDeriv_one] using hz
  · filter_upwards [hpb] with z hz
    simpa using hz

theorem coordinate_eq (L : PeriodPair) {z : ℂ} (hz : z ≠ 0) :
    u L z = L.weierstrassP z / deriv L.weierstrassP z ∧
    v L z = 1 / deriv L.weierstrassP z := by
  have hp := L.weierstrassPExcept_add (0 : L.lattice) z
  have hq := L.derivWeierstrassPExcept_sub (0 : L.lattice) z
  simp only [Submodule.coe_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), div_zero,
    sub_zero] at hp hq
  rw [L.deriv_weierstrassP]
  rw [← hp, ← hq]
  unfold u v numerator denominator
  constructor <;> field_simp <;> ring

theorem expansions (L : PeriodPair) :
    (fun z => u L z + z/2) =O[𝓝 (0:ℂ)] (fun z => z^5) ∧
    (fun z => v L z + z^3/2) =O[𝓝 (0:ℂ)] (fun z => z^7) := by
  obtain ⟨a,b,ha,hb,hpa,hpb⟩ := regular_factorizations L
  let A : ℂ → ℂ := fun z => (2*a z + b z)/(2*denominator L z)
  let B : ℂ → ℂ := fun z => b z/(2*denominator L z)
  have hA : ContinuousAt A 0 := by
    dsimp [A]
    apply ContinuousAt.div
    · fun_prop
    · exact continuousAt_const.mul (denominator_analytic L).continuousAt
    · simp
  have hB : ContinuousAt B 0 := by
    dsimp [B]
    apply ContinuousAt.div hb.continuousAt
      (continuousAt_const.mul (denominator_analytic L).continuousAt)
    simp
  have hn : ∀ᶠ z in 𝓝 (0:ℂ), denominator L z ≠ 0 :=
    (denominator_analytic L).continuousAt.eventually_ne (by simp)
  have heA : (fun z => u L z + z/2) =ᶠ[𝓝 (0:ℂ)] (fun z => z^5*A z) := by
    filter_upwards [hpa,hpb,hn] with z hp hq hz
    dsimp [u,numerator, A]
    field_simp
    dsimp [denominator]
    rw [hp,hq]
    ring
  have heB : (fun z => v L z + z^3/2) =ᶠ[𝓝 (0:ℂ)] (fun z => z^7*B z) := by
    filter_upwards [hpb,hn] with z hq hz
    dsimp [v,B]
    field_simp
    dsimp [denominator]
    rw [hq]
    ring
  constructor
  · have h := (isBigO_refl (fun z:ℂ => z^5) (𝓝 (0:ℂ))).mul
      (isBigO_const_of_tendsto hA (by norm_num : (1:ℂ) ≠ 0))
    simpa only [mul_one] using h.congr' heA.symm Filter.EventuallyEq.rfl
  · have h := (isBigO_refl (fun z:ℂ => z^7) (𝓝 (0:ℂ))).mul
      (isBigO_const_of_tendsto hB (by norm_num : (1:ℂ) ≠ 0))
    simpa only [mul_one] using h.congr' heB.symm Filter.EventuallyEq.rfl

end D12Complex.TorusCubicLocalMap.InfinityCoordinates

noncomputable section
open Set Filter Asymptotics
open scoped Topology
namespace D12Complex.TorusCubicLocalMap.InfinityLocal
open D12Complex D12Complex.CubicFiniteCharts D12Complex.CubicInfinityChart
open D12Complex.ProjectivePlaneTopology
open D12Complex.TorusCubicLocalMap.InfinityCoordinates

theorem denominator_eq (L : PeriodPair) {z : ℂ} (hz : z ≠ 0) :
    denominator L z = z^3 * deriv L.weierstrassP z := by
  have hq := L.derivWeierstrassPExcept_sub (0 : L.lattice) z
  simp only [Submodule.coe_zero, sub_zero] at hq
  rw [L.deriv_weierstrassP, ← hq]
  unfold denominator
  field_simp
  ring

theorem value_eventually (L : PeriodPair) {G H : ℂ} (F : ℂ → Cubic G H)
    (hF0 : (F 0).val = O)
    (hF : ∀ z, z ∉ L.lattice → (F z).val = affinePoint
      (L.weierstrassP z) (deriv L.weierstrassP z)) :
    ∀ᶠ z in 𝓝 (0:ℂ), (F z).val = infinityPoint (u L z) (v L z) := by
  have hn : ∀ᶠ z in 𝓝 (0:ℂ), denominator L z ≠ 0 :=
    (denominator_analytic L).continuousAt.eventually_ne (by simp)
  filter_upwards [L.compl_lattice_sdiff_singleton_mem_nhds 0, hn] with z hz hnz
  by_cases hz0 : z = 0
  · simp [hz0,hF0]
  have hzL : z ∉ L.lattice := by simpa [Set.mem_sdiff, hz0] using hz
  have hdn : deriv L.weierstrassP z ≠ 0 := by
    intro hd
    rw [denominator_eq L hz0, hd, mul_zero] at hnz
    exact hnz rfl
  rw [hF z hzL]
  have hp2 : affinePoint (L.weierstrassP z) (deriv L.weierstrassP z) ∈ coordinatePatch 2 :=
    (affinePoint_mem_infinity_iff _ _).mpr hdn
  conv_lhs => rw [← infinityPoint_coordinates hp2]
  simp only [infinityU_affinePoint, infinityV_affinePoint]
  rw [(coordinate_eq L hz0).1, (coordinate_eq L hz0).2]

theorem continuousAt_F_zero (L : PeriodPair) {G H : ℂ} (F : ℂ → Cubic G H)
    (hF0 : (F 0).val = O)
    (hF : ∀ z, z ∉ L.lattice → (F z).val = affinePoint
      (L.weierstrassP z) (deriv L.weierstrassP z)) : ContinuousAt F 0 := by
  have heq : (fun z => (F z).val) =ᶠ[𝓝 (0:ℂ)]
      (fun z => infinityPoint (u L z) (v L z)) := value_eventually L F hF0 hF
  have hc := continuous_infinityPoint.continuousAt.comp
    ((u_analytic L).continuousAt.prodMk (v_analytic L).continuousAt)
  apply tendsto_subtype_rng.mpr
  have hc' : Tendsto (fun z => infinityPoint (u L z) (v L z))
      (𝓝 (0:ℂ)) (𝓝 O) := by simpa [Function.comp_def] using hc.tendsto
  have h := hc'.congr' heq.symm
  simpa only [hF0] using h

theorem infinity_local (L : PeriodPair) {G H : ℂ} (F : ℂ → Cubic G H)
    (hF0 : (F 0).val = O)
    (hF : ∀ z, z ∉ L.lattice → (F z).val = affinePoint
      (L.weierstrassP z) (deriv L.weierstrassP z)) :
    ∃ (e : OpenPartialHomeomorph (Cubic G H) ℂ) (U V : Set ℂ) (h : ℂ → ℂ),
      IsInfinityChart G H e ∧ (0:ℂ) ∈ U ∧ MapsTo F U e.source ∧
      BiholomorphicPair U V (fun z => e (F z)) h := by
  obtain ⟨A, W, V, e, hAo, hA0, hWo, hW0, hV, hV0, hmap, hgraph,
      hbig, he, het, hes, hei, heO⟩ := infinity_chart G H
  have hs0 : F 0 ∈ e.source := (heO (F 0) hF0).1
  have hFc := continuousAt_F_zero L F hF0 hF
  have hsource : ∀ᶠ z in 𝓝 (0:ℂ), F z ∈ e.source :=
    hFc (e.open_source.mem_nhds hs0)
  have heq : (fun z => e (F z)) =ᶠ[𝓝 (0:ℂ)] u L := by
    filter_upwards [hsource, value_eventually L F hF0 hF] with z hs hz
    rw [he.2.1 (F z) hs, hz, infinityU_infinityPoint]
  have ha : AnalyticAt ℂ (fun z => e (F z)) 0 := (u_analytic L).congr heq.symm
  have hd : HasDerivAt (fun z => e (F z)) (-1/2) 0 :=
    (u_hasDerivAt L).congr_of_eventuallyEq heq
  obtain ⟨N, hNs, hNo, hN0⟩ := mem_nhds_iff.mp hsource
  let Ω : Set ℂ := {z | AnalyticAt ℂ (fun z => e (F z)) z} ∩ N
  have hΩ : HolomorphicOn Ω (fun z => e (F z)) :=
    ⟨(isOpen_analyticAt ℂ (fun z => e (F z))).inter hNo,
      fun z hz => hz.1.differentiableAt⟩
  have hΩ0 : (0:ℂ) ∈ Ω := ⟨ha,hN0⟩
  have hdn : deriv (fun z => e (F z)) 0 ≠ 0 := by rw [hd.deriv]; norm_num
  obtain ⟨U,T,h,hU0,hT0,hUΩ,hbi,hn,hi⟩ :=
    LocalHolomorphicInverse.local_holomorphic_inverse Ω (fun z => e (F z)) 0 hΩ hΩ0 hdn
  exact ⟨e,U,T,h,he,hU0,fun z hz => hNs (hUΩ hz).2,hbi⟩

end D12Complex.TorusCubicLocalMap.InfinityLocal

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.TorusCubicLocalMap

lemma translate_biholomorphic_pair {U V : Set ℂ} {f h : ℂ → ℂ} {a : ℂ}
    (hbi : BiholomorphicPair U V f h) (hper : ∀ z, f (z+a) = f z) :
    BiholomorphicPair {z | z-a ∈ U} V f (fun w => h w+a) := by
  have hminus (z : ℂ) : f (z-a) = f z := by
    simpa using (hper (z-a)).symm
  refine ⟨⟨hbi.1.1.preimage (continuous_id.sub continuous_const), fun z hz => ?_⟩,
    ⟨hbi.2.1.1, fun w hw => (hbi.2.1.2 w hw).add_const a⟩,
    ?_, ?_, ?_, ?_⟩
  · have hc := (hbi.1.2 (z-a) hz).comp z (differentiableAt_id.sub_const a)
    exact hc.congr_of_eventuallyEq (Eventually.of_forall fun z => (hminus z).symm)
  · intro z hz
    rw [← hminus z]
    exact hbi.2.2.1 hz
  · intro w hw
    change h w+a-a ∈ U
    simpa using hbi.2.2.2.1 hw
  · intro z hz
    change h (f z)+a=z
    rw [← hminus z, hbi.2.2.2.2.1 hz, sub_add_cancel]
  · intro w hw
    change f (h w+a)=w
    rw [hper, hbi.2.2.2.2.2 hw]

lemma translate_local_inverse_data {Y : Type*} [TopologicalSpace Y]
    (F : ℂ → Y) (e : OpenPartialHomeomorph Y ℂ) {a : ℂ}
    (hper : ∀ z, F (z+a) = F z)
    (U V : Set ℂ) (h : ℂ → ℂ) (hU : (0:ℂ) ∈ U)
    (hmap : MapsTo F U e.source) (hbi : BiholomorphicPair U V (e ∘ F) h) :
    ∃ U' V' : Set ℂ, ∃ h' : ℂ → ℂ, a∈U' ∧
      MapsTo F U' e.source ∧ BiholomorphicPair U' V' (e ∘ F) h' := by
  refine ⟨{z | z-a∈U}, V, fun w => h w+a, by simpa using hU, ?_, ?_⟩
  · intro z hz
    have hp : F (z-a) = F z := by simpa using (hper (z-a)).symm
    rw [← hp]
    exact hmap hz
  · exact translate_biholomorphic_pair hbi (fun z => congrArg e (hper z))

lemma translate_continuousAt {Y : Type*} [TopologicalSpace Y]
    (F : ℂ → Y) {a : ℂ} (hper : ∀ z, F (z+a) = F z)
    (hF : ContinuousAt F 0) : ContinuousAt F a := by
  have heq : (fun z => F (z-a)) =ᶠ[𝓝 a] F :=
    Eventually.of_forall fun z => by simpa using (hper (z-a)).symm
  have hc : ContinuousAt (fun z => F (z-a)) a := by
    have hh : ContinuousAt F (a-a) := by simpa using hF
    have hs : ContinuousAt (fun z : ℂ => z-a) a := continuousAt_id.sub_const a
    exact hh.comp (f := fun z : ℂ => z-a) hs
  exact hc.congr heq

lemma plane_local_at_lattice {ω₁ ω₂ G H a : ℂ}
    {F : ℂ → CubicFiniteCharts.Cubic G H}
    (hF : TorusSurface.Periodic ω₁ ω₂ F) (ha : a ∈ TorusSurface.lattice ω₁ ω₂)
    (hzero : PlaneLocalInverseAt F 0) : PlaneLocalInverseAt F a := by
  obtain ⟨e, he, U, V, h, hU, hmap, hbi⟩ := hzero
  obtain ⟨U', V', h', haU', hmap', hbi'⟩ :=
    translate_local_inverse_data F e (fun z => hF z a ha) U V h hU hmap hbi
  exact ⟨e, he, U', V', h', haU', hmap', hbi'⟩

end D12Complex.TorusCubicLocalMap

noncomputable section
open Set Filter
open scoped Topology
namespace D12Complex.TorusCubicLocalMap
open CubicFiniteCharts CubicInfinityChart

lemma biholomorphicPair_restrict {U V W : Set ℂ} {f h : ℂ → ℂ}
    (hb : BiholomorphicPair U V f h) (hW : IsOpen W) (hWU : W ⊆ U) :
    BiholomorphicPair W (V ∩ h ⁻¹' W) f h := by
  have hc : ContinuousOn h V := fun z hz => (hb.2.1.2 z hz).continuousAt.continuousWithinAt
  refine ⟨⟨hW, fun z hz => hb.1.2 z (hWU hz)⟩,
    ⟨hc.isOpen_inter_preimage hb.2.1.1 hW, fun z hz => hb.2.1.2 z hz.1⟩,
    ?_, (fun z hz => hz.2), (fun z hz => hb.2.2.2.2.1 (hWU hz)), ?_⟩
  · intro z hz
    exact ⟨hb.2.2.1 (hWU hz), by simpa only [mem_preimage, hb.2.2.2.2.1 (hWU hz)]⟩
  · intro z hz
    exact hb.2.2.2.2.2 hz.1

lemma biholomorphicPair_congr_left {U V : Set ℂ} {f g h : ℂ → ℂ}
    (hb : BiholomorphicPair U V f h) (heq : EqOn g f U) :
    BiholomorphicPair U V g h := by
  refine ⟨⟨hb.1.1, fun z hz => ?_⟩, hb.2.1, ?_, hb.2.2.2.1, ?_, ?_⟩
  · apply (hb.1.2 z hz).congr_of_eventuallyEq
    filter_upwards [hb.1.1.mem_nhds hz] with w hw
    exact heq hw
  · intro z hz
    simpa only [heq hz] using hb.2.2.1 hz
  · intro z hz
    simpa only [heq hz] using hb.2.2.2.2.1 hz
  · intro z hz
    rw [heq (hb.2.2.2.1 hz)]
    exact hb.2.2.2.2.2 hz

lemma continuousAt_of_plane_local {G H : ℂ} {F : ℂ → Cubic G H} {a : ℂ}
    (ha : PlaneLocalInverseAt F a) : ContinuousAt F a := by
  obtain ⟨e, _, U, V, h, ha, hmap, hb⟩ := ha
  have hc0 : ContinuousAt (fun z => e (F z)) a := (hb.1.2 a ha).continuousAt
  have hc : ContinuousAt (fun z => e.symm (e (F z))) a :=
    (e.continuousAt_symm (e.map_source (hmap ha))).comp (f := fun z : ℂ => e (F z)) hc0
  apply hc.congr_of_eventuallyEq
  filter_upwards [hb.1.1.mem_nhds ha] with z hz
  exact (e.left_inv (hmap hz)).symm

lemma continuous_of_plane_local {ω₁ ω₂ G H : ℂ}
    {F : TorusSurface.Torus ω₁ ω₂ → Cubic G H}
    (hF : ∀ a : ℂ, PlaneLocalInverseAt (F ∘ TorusSurface.projection ω₁ ω₂) a) :
    Continuous F := by
  apply (TorusSurface.quotient_topology ω₁ ω₂).1.isQuotientMap.continuous_iff.mpr
  exact continuous_iff_continuousAt.mpr fun a => continuousAt_of_plane_local (hF a)

lemma quotient_local_of_plane_local {ω₁ ω₂ G H : ℂ}
    (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    {F : TorusSurface.Torus ω₁ ω₂ → Cubic G H}
    (hF : ∀ a : ℂ, PlaneLocalInverseAt (F ∘ TorusSurface.projection ω₁ ω₂) a) :
    ∀ t, QuotientLocalInverseAt F t := by
  intro t
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (TorusSurface.lattice ω₁ ω₂).toAddSubgroup t
  obtain ⟨d, hd, _, _, _, _⟩ := TorusSurface.compact_surface ω₁ ω₂ h₁ h₂
  obtain ⟨s, hs, hst, hss, hsym, hid⟩ := TorusSurface.disk_charts ω₁ ω₂ h₁ h₂ d hd a (d/4)
    (by linarith [hd.1]) (by linarith [hd.1])
  obtain ⟨e, he, U, V, h, ha, hmap, hb⟩ := hF a
  let W := U ∩ Metric.ball a (d/4)
  have hW : IsOpen W := hb.1.1.inter Metric.isOpen_ball
  have haW : a ∈ W := ⟨ha, Metric.mem_ball_self (by linarith [hd.1])⟩
  have hbW := biholomorphicPair_restrict hb hW (show W ⊆ U from inter_subset_left)
  have hWst : W ⊆ s.val.target := by simpa only [hst] using (inter_subset_right : W ⊆ Metric.ball a (d/4))
  have hidW : EqOn (s.val.symm : ℂ → TorusSurface.Torus ω₁ ω₂)
      (TorusSurface.projection ω₁ ω₂) W := fun z hz => hsym hz.2
  refine ⟨d, hd, s, hs, ?_, e, he, W, V ∩ h ⁻¹' W, h, ?_, hWst, ?_, ?_⟩
  · rw [hss]
    exact ⟨a, Metric.mem_ball_self (by linarith [hd.1]), rfl⟩
  · change s.val (TorusSurface.projection ω₁ ω₂ a) ∈ W
    rw [hid a (Metric.mem_ball_self (by linarith [hd.1]))]
    exact haW
  · intro z hz
    change F (s.val.symm z) ∈ e.source
    rw [hidW hz]
    exact hmap hz.1
  · apply biholomorphicPair_congr_left hbW
    intro z hz
    change e (F (s.val.symm z)) = e (F (TorusSurface.projection ω₁ ω₂ z))
    rw [hidW hz]

end D12Complex.TorusCubicLocalMap

namespace D12Complex.TorusCubicLocalMap
open TorusSurface CubicFiniteCharts CubicInfinityChart
open Specs.D12Complex.Ch22.WeierstrassSeries (weierstrassP)
open Specs.D12Complex.Ch22.WeierstrassEquations (g₂ g₃)
open Ch22.WeierstrassSeries (periodPair)

/-- All translations, including designated pole values, give the same
projective point. -/
theorem periodic : Specs.D12Complex.Ch22.TorusCubicLocalMap.periodic_type := by
  intro ω₁ ω₂ h₁ h₂
  exact planeMap_periodic h₁ h₂

theorem projection_formula :
    Specs.D12Complex.Ch22.TorusCubicLocalMap.projection_formula_type := by
  intro ω₁ ω₂ h₁ h₂ z
  exact phi_projection h₁ h₂ z

theorem formulas : Specs.D12Complex.Ch22.TorusCubicLocalMap.formulas_type := by
  intro ω₁ ω₂ h₁ h₂
  exact ⟨fun z hz => phi_finite h₁ h₂ hz, phi_zero h₁ h₂, phi_onCubic h₁ h₂⟩

theorem construction : Specs.D12Complex.Ch22.TorusCubicLocalMap.construction_type := by
  intro ω₁ ω₂ h₁ h₂
  refine ⟨map h₁ h₂, fun _ => rfl, ?_⟩
  intro F hF
  funext t
  exact Subtype.ext (hF t)

lemma lift_formula {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (F : Torus ω₁ ω₂ → Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂))
    (hF : ∀ t, (F t).val = phi ω₁ ω₂ t) :
    ∀ z ∉ lattice ω₁ ω₂, (F (projection ω₁ ω₂ z)).val =
      affinePoint (weierstrassP ω₁ ω₂ z) (deriv (weierstrassP ω₁ ω₂) z) := by
  intro z hz
  rw [hF, phi_finite h₁ h₂ hz]

lemma lift_origin {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (F : Torus ω₁ ω₂ → Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂))
    (hF : ∀ t, (F t).val = phi ω₁ ω₂ t) :
    (F (projection ω₁ ω₂ 0)).val = O := by
  rw [map_zero, hF, phi_zero h₁ h₂]

theorem infinity_bridge : Specs.D12Complex.Ch22.TorusCubicLocalMap.infinity_bridge_type := by
  intro ω₁ ω₂ h₁ h₂ F hF
  let L := periodPair h₁ h₂
  refine ⟨InfinityCoordinates.u L, InfinityCoordinates.v L,
    InfinityCoordinates.u_analytic L, InfinityCoordinates.v_analytic L,
    InfinityCoordinates.u_zero L, InfinityCoordinates.v_zero L,
    InfinityCoordinates.u_hasDerivAt L, ?_,
    (InfinityCoordinates.expansions L).1, (InfinityCoordinates.expansions L).2, ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact InfinityCoordinates.coordinate_eq L hz
  · exact InfinityLocal.value_eventually L (F ∘ projection ω₁ ω₂)
      (lift_origin h₁ h₂ F hF) (lift_formula h₁ h₂ F hF)

theorem finite_local : Specs.D12Complex.Ch22.TorusCubicLocalMap.finite_local_type := by
  intro ω₁ ω₂ h₁ h₂ F hF a ha
  exact finite_chart_inverse h₁ h₂ ha (F ∘ projection ω₁ ω₂) (lift_formula h₁ h₂ F hF)

lemma plane_local {ω₁ ω₂ : ℂ} (h₁ : ω₁ ≠ 0) (h₂ : 0 < (ω₂ / ω₁).im)
    (F : Torus ω₁ ω₂ → Cubic (g₂ ω₁ ω₂) (g₃ ω₁ ω₂))
    (hF : ∀ t, (F t).val = phi ω₁ ω₂ t) :
    ∀ a, PlaneLocalInverseAt (F ∘ projection ω₁ ω₂) a := by
  let L := periodPair h₁ h₂
  have hzero : PlaneLocalInverseAt (F ∘ projection ω₁ ω₂) 0 := by
    obtain ⟨e, U, V, h, he, hU, hmap, hbi⟩ := InfinityLocal.infinity_local L
      (F ∘ projection ω₁ ω₂) (lift_origin h₁ h₂ F hF) (lift_formula h₁ h₂ F hF)
    exact ⟨e, Or.inl he, U, V, h, hU, hmap, hbi⟩
  have hper : Periodic ω₁ ω₂ (F ∘ projection ω₁ ω₂) := by
    intro z l hl
    apply Subtype.ext
    change (F (projection ω₁ ω₂ (z+l))).val = (F (projection ω₁ ω₂ z)).val
    rw [hF, hF, phi_projection h₁ h₂, phi_projection h₁ h₂]
    exact planeMap_periodic h₁ h₂ z l hl
  intro a
  by_cases ha : a ∈ lattice ω₁ ω₂
  · exact plane_local_at_lattice hper ha hzero
  · obtain ⟨e, he, U, V, h, hU, hmap, hbi⟩ :=
      finite_chart_inverse h₁ h₂ ha (F ∘ projection ω₁ ω₂) (lift_formula h₁ h₂ F hF)
    exact ⟨e, Or.inr ⟨_, he⟩, U, V, h, hU, hmap, hbi⟩

/-- The actual map is continuous and has holomorphic inverse branches in the
quotient-disk and cubic coordinates at every point, including [0]. -/
theorem locally_biholomorphic :
    Specs.D12Complex.Ch22.TorusCubicLocalMap.locally_biholomorphic_type := by
  intro ω₁ ω₂ h₁ h₂ F hF
  have hp := plane_local h₁ h₂ F hF
  exact ⟨continuous_of_plane_local hp, quotient_local_of_plane_local h₁ h₂ hp⟩

end D12Complex.TorusCubicLocalMap
