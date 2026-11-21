import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.DampedPendulum
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.Lyapunov
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.Lasalle
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.FirstIntegral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity

noncomputable section
open Set Filter Metric
open scoped Topology

namespace D13Unified.Ch12.DampedPendulum
open Specs.D13Unified.Ch12.DampedPendulum
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch11.Invariant
open Specs.D13Unified.Ch12.StabilityDefinitions
open Ch06.StateDerivative

@[simp] lemma eval_pendulum (c : ℝ) (z : Plane) : (pendulum c).eval z = vectorField c z := by
  simp [AutonomousODE.eval, autonomousEvalValue, pendulum]

lemma field_smooth (c : ℝ) : ContDiff ℝ 1 (vectorField c) := by
  unfold vectorField
  fun_prop

lemma pendulum_smooth (c : ℝ) : ContDiffOn ℝ 1 (pendulum c).eval (pendulum c).domain := by
  rw [show (pendulum c).eval = vectorField c from funext (eval_pendulum c)]
  exact (field_smooth c).contDiffOn

lemma energy_smooth : ContDiff ℝ 1 energy := by
  unfold energy
  fun_prop

@[simp] lemma energy_zero : energy 0 = 0 := by simp [energy]
@[simp] lemma field_zero (c : ℝ) : (pendulum c).eval 0 = 0 := by
  simp [vectorField]

lemma energy_derivative (z : Plane) :
    HasFDerivAt energy
      ((z.2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ +
        Real.sin z.1 • ContinuousLinearMap.fst ℝ ℝ ℝ) z := by
  have h₁ := (hasFDerivAt_snd (𝕜 := ℝ) (p := z)).pow 2
  have h₂ := (Real.hasDerivAt_cos z.1).comp_hasFDerivAt z
    (hasFDerivAt_fst (𝕜 := ℝ) (p := z))
  convert ((HasFDerivAt.const_mul h₁ (1/2 : ℝ)).add_const 1).sub h₂ using 1 <;>
    ext v <;> simp [energy] <;> ring

theorem dissipation : Dissipation := by
  intro c z
  rw [(energy_derivative z).fderiv]
  simp [vectorField]
  ring

lemma energy_nonnegative (z : Plane) : 0 ≤ energy z := by
  have := Real.cos_le_one z.1
  dsimp [energy]
  nlinarith [sq_nonneg z.2]

lemma energy_positive {z : Plane} (hz : z ∈ ball (0 : Plane) (Real.pi / 2))
    (hne : z ≠ 0) : 0 < energy z := by
  have hn : ‖z‖ < Real.pi / 2 := by simpa using hz
  have hx : |z.1| < Real.pi / 2 := lt_of_le_of_lt (by simpa using norm_fst_le z) hn
  by_cases hx0 : z.1 = 0
  · have hy : z.2 ≠ 0 := fun hy => hne (Prod.ext hx0 hy)
    simp only [energy, hx0, Real.cos_zero]
    nlinarith [sq_pos_of_ne_zero hy]
  · have hcos : Real.cos z.1 < 1 := lt_of_le_of_ne (Real.cos_le_one _) (by
      intro hc
      apply hx0
      exact (Real.cos_eq_one_iff_of_lt_of_lt
        (by linarith [(abs_lt.mp hx).1, Real.pi_pos])
        (by linarith [(abs_lt.mp hx).2, Real.pi_pos])).mp hc)
    dsimp [energy]
    nlinarith [sq_nonneg z.2]

lemma energy_decreases (c : ℝ) (hc : 0 ≤ c) (z : Plane) :
    Specs.D13Unified.Ch12.Lyapunov.lieDerivative (pendulum c) energy z ≤ 0 := by
  change (fderiv ℝ energy z) ((pendulum c).eval z) ≤ 0
  rw [eval_pendulum, dissipation]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (sq_nonneg _)

/-- A concrete restricted sublevel, with a strict energy barrier on its sphere. -/
lemma small_sublevel (c : ℝ) (hc : 0 ≤ c) (ε : ℝ) (hε : 0 < ε) :
    ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
      IsCompact (sublevel r a) ∧ positiveInvariantValue (pendulum c) (sublevel r a) ∧
      ball 0 δ ⊆ sublevel r a ∧ sublevel r a ⊆ ball 0 (min ε (Real.pi / 2)) := by
  let R := min ε (Real.pi / 2)
  have hR : 0 < R := lt_min hε (half_pos Real.pi_pos)
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hrR : r < R := by dsimp [r]; linarith
  have hb : closedBall (0 : Plane) r ⊆ ball 0 (Real.pi / 2) :=
    (closedBall_subset_ball hrR).trans (ball_subset_ball (min_le_right _ _))
  obtain ⟨m, hm, hmV⟩ := (isCompact_sphere (0 : Plane) r).exists_forall_le'
    energy_smooth.continuous.continuousOn (a := 0) (by
      intro z hz
      apply energy_positive (hb (sphere_subset_closedBall hz))
      intro hz0
      have : (0 : ℝ) = r := by simpa [hz0] using hz
      linarith)
  let a := m / 2
  have ha : 0 < a := half_pos hm
  have hmargin : ∀ z ∈ closedBall (0 : Plane) r, energy z ≤ a → ‖z‖ < r := by
    intro z hz hv
    have hn : ‖z‖ ≤ r := by simpa using hz
    apply lt_of_le_of_ne hn
    intro he
    have hzs : z ∈ sphere (0 : Plane) r := by simpa using he
    have := hmV z hzs
    dsimp [a] at hv
    linarith
  have hInv : positiveInvariantValue (pendulum c) (sublevel r a) :=
    Lyapunov.sublevel_positivelyInvariant (pendulum c) (pendulum_smooth c)
      isOpen_univ (fun _ _ => mem_univ _) energy_smooth.contDiffOn
      (fun z _ => energy_decreases c hc z) (fun _ _ => mem_univ _) hmargin
  have hclosed : IsClosed (sublevel r a) :=
    isClosed_closedBall.inter (isClosed_Iic.preimage energy_smooth.continuous)
  have hnear : ∀ᶠ z in 𝓝 (0 : Plane), energy z < a :=
    energy_smooth.continuous.continuousAt.eventually
      (Iio_mem_nhds (by simpa using ha))
  obtain ⟨d, hd, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨r, a, min d r, hr, ha, lt_min hd hr,
    (isCompact_closedBall 0 r).of_isClosed_subset hclosed inter_subset_left, hInv, ?_, ?_⟩
  · intro z hz
    have hzd := (mem_ball.mp hz).trans_le (min_le_left d r)
    have hzr := (mem_ball.mp hz).trans_le (min_le_right d r)
    exact ⟨hzr.le, (hsmall hzd).le⟩
  · exact fun z hz => closedBall_subset_ball hrR hz.1

lemma zeroSet_eq (c : ℝ) (hc : 0 < c) (K : Set Plane) :
    Specs.D13Unified.Ch12.Lasalle.zeroSet (pendulum c) K energy =
      {z | z ∈ K ∧ z.2 = 0} := by
  ext z
  have he : Specs.D13Unified.Ch12.Lasalle.lieDerivative (pendulum c) energy z =
      -c * z.2 ^ 2 := by
    change (fderiv ℝ energy z) ((pendulum c).eval z) = _
    rw [eval_pendulum, dissipation]
  simp only [Specs.D13Unified.Ch12.Lasalle.zeroSet, mem_ofPred_eq, he]
  constructor
  · rintro ⟨hz, h⟩
    exact ⟨hz, (sq_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr hc.ne')) )⟩
  · rintro ⟨hz, h⟩
    exact ⟨hz, by simp [h]⟩

/-- A complete orbit with identically zero velocity is an equilibrium; in
this ball the only zero of sine is zero. -/
lemma core_subset_origin (c : ℝ) {K : Set Plane}
    (hK : K ⊆ ball 0 (Real.pi / 2)) :
    Specs.D13Unified.Ch12.Lasalle.completeCore (pendulum c) {z | z ∈ K ∧ z.2 = 0} ⊆ {0} := by
  intro z hz
  have hivp := flow_ivp (pendulum c) (pendulum_smooth c) (mem_univ z)
  have hv : ∀ t : ℝ, (flow (pendulum c) t z).2 = 0 := fun t => (hz.2.2 t).2
  have hd := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt 0
    (hivp.1.2.2 0 hivp.2.1)
  have hd' : HasDerivAt (fun t => (flow (pendulum c) t z).2)
      (-Real.sin z.1 - c * z.2) 0 := by
    simpa [AutonomousODE.toODE_eval, hivp.2.2, vectorField] using! hd
  have hs : Real.sin z.1 = 0 := by
    have hh := hd'.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq
      (Eventually.of_forall hv))
    rw [hz.1.2, mul_zero, sub_zero, neg_eq_zero] at hh
    exact hh
  have hn : ‖z‖ < Real.pi / 2 := by simpa using hK hz.1.1
  have hx : |z.1| < Real.pi / 2 := lt_of_le_of_lt (by simpa using norm_fst_le z) hn
  have hx0 : z.1 = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt
    (by linarith [(abs_lt.mp hx).1, Real.pi_pos])
    (by linarith [(abs_lt.mp hx).2, Real.pi_pos])).mp hs
  exact Prod.ext hx0 hz.1.2

lemma sublevel_core (c : ℝ) (hc : 0 < c) {r a δ : ℝ}
    (hδ : 0 < δ) (hK : IsCompact (sublevel r a))
    (hInv : positiveInvariantValue (pendulum c) (sublevel r a))
    (hδK : ball 0 δ ⊆ sublevel r a)
    (hsmall : sublevel r a ⊆ ball 0 (Real.pi / 2)) :
    Specs.D13Unified.Ch12.Lasalle.completeCore (pendulum c)
      {z | z ∈ sublevel r a ∧ z.2 = 0} = {0} := by
  have h := Lasalle.lasalle (pendulum c) (pendulum_smooth c) _ hK hInv energy univ
    isOpen_univ (subset_univ _) energy_smooth.contDiffOn (fun z _ => energy_decreases c hc.le z)
  have hne := h.2.2.2.2.1 ⟨0, hδK (by simpa using hδ)⟩
  rw [zeroSet_eq c hc] at hne
  have hsub := core_subset_origin c hsmall
  apply Subset.antisymm hsub
  obtain ⟨z, hz⟩ := hne
  have hz0 : z = 0 := hsub hz
  simpa [hz0] using singleton_subset_iff.mpr hz

theorem trapping : Trapping := by
  intro c hc ε hε
  obtain ⟨r, a, δ, hr, ha, hδ, hK, hInv, hδK, hsmall⟩ := small_sublevel c hc.le ε hε
  exact ⟨r, a, δ, hr, ha, hδ, hK, hInv, hδK, hsmall,
    sublevel_core c hc hδ hK hInv hδK (hsmall.trans (ball_subset_ball (min_le_right _ _)))⟩

theorem asymptotic_stability : AsymptoticStability := by
  intro c hc
  have hstable := Lyapunov.stability (pendulum c) (pendulum_smooth c) (mem_univ 0)
    (field_zero c) (ball 0 (Real.pi / 2)) isOpen_ball (by simpa using half_pos Real.pi_pos)
    (subset_univ _) energy (energy_smooth.contDiffOn) energy_zero
    (fun z hz hne => energy_positive hz hne) (fun z _ => energy_decreases c hc.le z)
  refine ⟨?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, h⟩ := hstable ε hε
    exact ⟨δ, hδ, fun z hz => h z (mem_univ z) hz⟩
  · obtain ⟨r, a, δ, _, _, hδ, hK, hInv, hδK, _, hcore⟩ := trapping c hc 1 zero_lt_one
    refine ⟨δ, hδ, ?_⟩
    intro z hz
    have hc0 : Specs.D13Unified.Ch12.Lasalle.completeCore (pendulum c)
        (Specs.D13Unified.Ch12.Lasalle.zeroSet (pendulum c) (sublevel r a) energy) = {0} := by
      rwa [zeroSet_eq c hc]
    have h := Lasalle.singleton_convergence (pendulum c) (pendulum_smooth c) _ hK hInv
      energy univ isOpen_univ (subset_univ _) energy_smooth.contDiffOn
      (fun z _ => energy_decreases c hc.le z) 0 (mem_univ 0) (field_zero c) hc0
      z (hδK (by simpa using hz))
    exact ⟨fun t ht => ⟨mem_univ z, h.1 ht⟩, h.2⟩

theorem undamped_conservation : UndampedConservation := by
  exact Ch11.FirstIntegral.conservation (pendulum 0) (pendulum_smooth 0) energy energy_smooth.contDiffOn
    (fun z _ => by
      change (fderiv ℝ energy z) ((pendulum 0).eval z) = 0
      rw [eval_pendulum, dissipation]
      simp)

theorem undamped_nonconvergence : UndampedNonconvergence := by
  obtain ⟨r, a, δ, _, _, hδ, hK, hInv, hδK, _⟩ := small_sublevel 0 le_rfl 1 zero_lt_one
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  have hxK : z ∈ sublevel r a := hδK (by simpa using hz)
  have hcomp := Ch11.Invariant.compact_forward_complete (pendulum 0) (pendulum_smooth 0)
    _ hK hInv z hxK
  refine ⟨fun t ht => ⟨mem_univ z, hcomp.1 ht⟩, ?_⟩
  intro hnon hlim
  have henergy := (Ch11.FirstIntegral.flow_first_integral_iff (pendulum 0) (pendulum_smooth 0)
    energy energy_smooth.contDiffOn).mpr (fun z _ => by
      change (fderiv ℝ energy z) ((pendulum 0).eval z) = 0
      rw [eval_pendulum, dissipation]
      simp)
  have hconst : (fun t : ℝ => energy (flow (pendulum 0) t z)) =ᶠ[atTop] fun _ => energy z := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact henergy z (mem_univ z) t (hcomp.1 ht)
  have hzero : Tendsto (fun t : ℝ => energy (flow (pendulum 0) t z)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, energy_zero] using! energy_smooth.continuous.continuousAt.tendsto.comp hlim
  have hcst : Tendsto (fun t : ℝ => energy (flow (pendulum 0) t z)) atTop (𝓝 (energy z)) :=
    tendsto_const_nhds.congr' hconst.symm
  exact hnon (tendsto_nhds_unique hcst hzero)

end D13Unified.Ch12.DampedPendulum
