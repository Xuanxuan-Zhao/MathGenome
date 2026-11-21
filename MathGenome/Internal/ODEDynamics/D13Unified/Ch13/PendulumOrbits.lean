import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.PendulumOrbits
import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.PendulumPortrait
import MathGenome.Internal.ODEDynamics.D13Unified.Ch13.PoincareBendixson
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Module.Equiv.Pi

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric
open scoped Topology
namespace D13Unified.Ch13.PendulumOrbits
open PendulumPortrait Ch06.StateDerivative Ch11.Orbits
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch11.Invariant Specs.D13Unified.Ch11.OmegaTopology

lemma ovalPoint_mem (k : ℤ) {e : ℝ} (he : 0 ≤ e) : ovalPoint k e ∈ oval k e := by
  constructor
  · simp only [ovalPoint, energy, Matrix.cons_val_zero, Matrix.cons_val_one,
      cos_center]
    rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * e)]
    ring
  · simp [ovalPoint, Real.pi_pos.le]

lemma energy_nonnegative (z : Plane) : 0 ≤ energy z := by
  dsimp [energy]
  nlinarith [sq_nonneg (z 1), Real.cos_le_one (z 0)]

lemma energy_boundary (k : ℤ) {z : Plane}
    (hz : |z 0 - 2 * (k : ℝ) * Real.pi| = Real.pi) : 2 ≤ energy z := by
  have hc : Real.cos (z 0) = -1 := by
    rcases (abs_eq (Real.pi_pos.le)).mp hz with h | h
    · have he : z 0 = (2 * (k : ℝ) + 1) * Real.pi := by linarith
      rw [he, cos_saddle]
    · have he : z 0 = (2 * ((k-1 : ℤ) : ℝ) + 1) * Real.pi := by
        push_cast
        linarith
      rw [he, cos_saddle]
  dsimp [energy]
  rw [hc]
  nlinarith [sq_nonneg (z 1)]

lemma oval_strict_strip (k : ℤ) {e : ℝ} (he : e < 2) {z : Plane}
    (hz : z ∈ oval k e) : |z 0 - 2 * (k : ℝ) * Real.pi| < Real.pi := by
  exact lt_of_le_of_ne hz.2 (fun h => (not_le_of_gt he) (hz.1 ▸ energy_boundary k h))

lemma energy_level_noncritical {e : ℝ} (h0 : 0 < e) (h2 : e < 2)
    {z : Plane} (hz : energy z = e) : vectorField z ≠ 0 := by
  intro h
  have hy : z 1 = 0 := by simpa [vectorField] using congrFun h 0
  have hs : Real.sin (z 0) = 0 := by simpa [vectorField] using congrFun h 1
  rcases Real.sin_eq_zero_iff_cos_eq.mp hs with hc | hc <;>
    simp [energy, hy, hc] at hz <;> linarith

lemma energy_level_regular {e : ℝ} (h0 : 0 < e) (h2 : e < 2)
    {z : Plane} (hz : energy z = e) : Function.Surjective (fderiv ℝ energy z) := by
  intro r
  by_cases hy : z 1 = 0
  · have hs : Real.sin (z 0) ≠ 0 := by
      intro hs
      apply energy_level_noncritical h0 h2 hz
      ext i
      fin_cases i <;> simp [vectorField, hy, hs]
    refine ⟨![r / Real.sin (z 0), 0], ?_⟩
    simp only [energy_fderiv, Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, zero_add]
    field_simp
  · refine ⟨![0, r / z 1], ?_⟩
    simp only [energy_fderiv, Matrix.cons_val_one, Matrix.cons_val_zero, mul_zero, add_zero]
    field_simp

lemma oval_isClosed (k : ℤ) (e : ℝ) : IsClosed (oval k e) := by
  exact (isClosed_eq energy_contDiff.continuous continuous_const).inter
    (isClosed_le (((continuous_apply (0 : Fin 2)).sub continuous_const).abs) continuous_const)

lemma oval_isCompact (k : ℤ) (e : ℝ) : IsCompact (oval k e) := by
  apply (isCompact_closedBall (center k) (Real.pi + |e| + 2)).of_isClosed_subset
    (oval_isClosed k e)
  intro z hz
  rw [mem_closedBall, dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · change |z 0 - 2 * (k : ℝ) * Real.pi| ≤ Real.pi + |e| + 2
    linarith [hz.2, abs_nonneg e]
  · have hb : (z 1)^2 ≤ 2 * e := by
      have he := hz.1
      dsimp [energy] at he
      nlinarith [Real.cos_le_one (z 0)]
    change |z 1 - 0| ≤ Real.pi + |e| + 2
    rw [sub_zero]
    have hab : |z 1| ≤ |e| + 2 := by
      have hh := sq_abs (z 1)
      nlinarith [abs_nonneg (z 1), sq_nonneg (|z 1| - 1), le_abs_self e,
        sq_nonneg (|z 1| - (|e| + 2)), sq_nonneg (|e| + 1)]
    linarith [Real.pi_pos]

/-- A continuous trajectory cannot leave its well: any exit would pass an
energy-at-least-two boundary point. This treats either sign of time at once. -/
lemma oval_invariant (k : ℤ) {e : ℝ} (he : e < 2) :
    invariantValue pendulum (oval k e) := by
  refine ⟨subset_univ _, ?_⟩
  intro z hz t ht
  have hX := flow_ivp pendulum pendulum_regular (show z ∈ pendulum.domain from mem_univ _)
  have hen (r : ℝ) (hr : r ∈ (flowInterval pendulum z).carrier) :
      energy (flow pendulum r z) = e := by
    have hzero : flow pendulum 0 z = z := hX.2.2
    rw [energy_conserved _ _ hX.1 0 hX.2.1 r hr, hzero, hz.1]
  refine ⟨hen t ht, ?_⟩
  by_contra hn
  have hgt : Real.pi < |(flow pendulum t z) 0 - 2 * (k : ℝ) * Real.pi| := lt_of_not_ge hn
  have hcont : ContinuousOn (fun r => |(flow pendulum r z) 0 - 2 * (k : ℝ) * Real.pi|)
      (flowInterval pendulum z).carrier :=
    (((continuous_apply (0 : Fin 2)).comp_continuousOn hX.1.1.continuousOn).sub continuousOn_const).abs
  obtain ⟨r, hr, heq⟩ := (flowInterval pendulum z).ordConnected.isPreconnected.intermediate_value
    hX.2.1 ht hcont (show Real.pi ∈ Icc
      (|(flow pendulum 0 z) 0 - 2 * (k : ℝ) * Real.pi|)
      (|(flow pendulum t z) 0 - 2 * (k : ℝ) * Real.pi|) from
      ⟨by simpa only [hX.2.2] using hz.2, hgt.le⟩)
  exact (not_le_of_gt he) ((hen r hr) ▸ energy_boundary k heq)

lemma oval_complete (k : ℤ) {e : ℝ} (he : e < 2) {z : Plane}
    (hz : z ∈ oval k e) : IsComplete pendulum z ∧ ∀ t : ℝ, flow pendulum t z ∈ oval k e :=
  Ch11.Invariant.compact_complete pendulum pendulum_regular (oval k e)
    (oval_isCompact k e) (oval_invariant k he) z hz

/-- Identification with the canonical maximal trajectory includes its full
actual domain; no equality outside an unproved lifespan is used. -/
lemma global_solution_eq_flow (u : ℝ → Plane)
    (hu : ∀ t : ℝ, HasDerivAt u (vectorField (u t)) t) :
    IsComplete pendulum (u 0) ∧ ∀ t : ℝ, flow pendulum t (u 0) = u t := by
  let J : OpenTimeInterval := ⟨⟨univ, univ_nonempty, ordConnected_univ⟩, isOpen_univ⟩
  have hs : solutionOnValue pendulum.toODE J.toTimeInterval u := by
    refine ⟨(continuous_iff_continuousAt.mpr (fun t => (hu t).continuousAt)).continuousOn,
      fun _ _ => mem_univ _, ?_⟩
    intro t _
    simpa only [AutonomousODE.toODE_eval, pendulum_eval] using (hu t).hasDerivWithinAt
  have hc : classicalIVPOnValue pendulum.toODE J u 0 (u 0) :=
    ⟨(D13Unified.classical_iff_solutionOn _ _ _).mpr hs, mem_univ _, rfl⟩
  have h := (ODE.canonical_solution pendulum.toODE
    (pendulum.locallyLipschitzInState_of_contDiffOn pendulum_regular)
    0 (u 0) (mem_univ _)).2.2.2.2.2.1 J u hc
  exact ⟨Subset.antisymm (subset_univ _) h.1, fun t => h.2 (mem_univ t)⟩

lemma sin_four_arctan (r : ℝ) :
    Real.sin (4 * Real.arctan r) = 4 * r * (1-r^2) / (1+r^2)^2 := by
  have hd : 1+r^2 ≠ 0 := by positivity
  have hs : Real.sqrt (1+r^2) ≠ 0 := by positivity
  rw [show (4:ℝ)*Real.arctan r = 2*(2*Real.arctan r) by ring,
    Real.sin_two_mul, Real.cos_two_mul, Real.sin_two_mul,
    Real.sin_arctan, Real.cos_arctan]
  field_simp
  have hh : Real.sqrt (1+r^2)^2 = 1+r^2 := Real.sq_sqrt (by positivity)
  have hh4 : Real.sqrt (1+r^2)^4 = (1+r^2)^2 := by rw [show (4:ℕ)=2*2 from rfl, pow_mul, hh]
  rw [hh4, hh]
  ring

def sepX (t : ℝ) : ℝ := 4*Real.arctan (Real.exp t) - Real.pi
def sepY (t : ℝ) : ℝ := 4*Real.exp t/(1+(Real.exp t)^2)
lemma sepX_deriv (t : ℝ) : HasDerivAt sepX (sepY t) t := by
  convert ((Real.hasDerivAt_exp t).arctan.const_mul 4).sub_const Real.pi using 1 <;>
    (try rfl)
  dsimp only [sepY]
  ring
lemma sepY_deriv (t : ℝ) : HasDerivAt sepY (-Real.sin (sepX t)) t := by
  have hd : 1+(Real.exp t)^2 ≠ 0 := by positivity
  convert ((Real.hasDerivAt_exp t).const_mul 4).div
    (((Real.hasDerivAt_exp t).pow 2).const_add 1) hd using 1 <;> (try rfl)
  simp only [Pi.pow_apply, sepX, Real.sin_sub, Real.cos_pi, Real.sin_pi, mul_neg_one, mul_zero, sub_zero, neg_neg]
  rw [sin_four_arctan]
  field_simp
  ring
lemma sepY_lim : Tendsto sepY atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => 4/(Real.exp t + Real.exp (-t))) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (Real.tendsto_exp_atTop.atTop_add Real.tendsto_exp_neg_atTop_nhds_zero)
  convert he using 1
  ext t
  dsimp [sepY]
  rw [Real.exp_neg]
  field_simp
  ring
lemma sepX_lim : Tendsto sepX atTop (𝓝 Real.pi) := by
  have h := ((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp
    Real.tendsto_exp_atTop).const_mul 4 |>.sub_const Real.pi
  convert h using 1
  · rfl
  · ring

/-- The right-moving separatrix connects the two adjacent saddles on the
unwrapped plane. The shift is by a center, not a quotient of the plane. -/
def separatrix (k : ℤ) (t : ℝ) : Plane :=
  ![sepX t + 2 * (k : ℝ) * Real.pi, sepY t]

lemma separatrix_deriv (k : ℤ) (t : ℝ) :
    HasDerivAt (separatrix k) (vectorField (separatrix k t)) t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [separatrix, vectorField]
      using (sepX_deriv t).add_const (2 * (k : ℝ) * Real.pi)
  · have hs : Real.sin (sepX t + 2 * (k : ℝ) * Real.pi) = Real.sin (sepX t) := by
      convert Real.sin_add_int_mul_two_pi (sepX t) k using 1 <;> congr 1 <;> ring
    simpa [separatrix, vectorField, hs]
      using sepY_deriv t

lemma separatrix_zero (k : ℤ) : separatrix k 0 = ![2 * (k : ℝ) * Real.pi, 2] := by
  ext i
  fin_cases i <;> simp [separatrix, sepX, sepY] <;> ring

lemma separatrix_tendsto (k : ℤ) :
    Tendsto (separatrix k) atTop (𝓝 (saddle k)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  fin_cases i
  · have h := sepX_lim.add_const (2 * (k : ℝ) * Real.pi)
    convert h using 1 <;> dsimp [separatrix, saddle] <;> ring
  · exact sepY_lim

lemma separatrix_energy (k : ℤ) (t : ℝ) : energy (separatrix k t) = 2 := by
  obtain ⟨hc, hf⟩ := global_solution_eq_flow (separatrix k) (separatrix_deriv k)
  have hX := flow_ivp pendulum pendulum_regular
    (show separatrix k 0 ∈ pendulum.domain from mem_univ _)
  have he := energy_conserved _ _ hX.1 0 hX.2.1 t (by rw [hc]; trivial)
  rw [hf t, hf 0, separatrix_zero] at he
  norm_num [energy, cos_center] at he ⊢
  exact he

lemma separatrix_not_constant (k : ℤ) : ¬ IsConstant pendulum (separatrix k 0) := by
  intro h
  have hz := (Ch11.Orbits.equilibrium_characterization pendulum pendulum_regular
    (separatrix k 0) (mem_univ _)).mpr h
  change pendulum.eval (separatrix k 0) = 0 at hz
  rw [pendulum_eval, separatrix_zero] at hz
  have he := congrFun hz 0
  norm_num [vectorField] at he

/-- A convergent complete trajectory has exactly the singleton omega set.
The shared sequence characterization keeps all sequence times admissible. -/
lemma omega_eq_singleton_of_tendsto {z p : Plane} (hc : IsComplete pendulum z)
    (hp : Tendsto (fun t => flow pendulum t z) atTop (𝓝 p)) :
    omegaValue pendulum z = {p} := by
  ext q
  constructor
  · intro hq
    obtain ⟨s, _, hs, hq⟩ := (Ch11.OmegaTopology.sequence_characterization pendulum z q).mp hq
    exact mem_singleton_iff.mpr (tendsto_nhds_unique hq (hp.comp hs))
  · intro hq
    rw [mem_singleton_iff] at hq
    subst q
    apply (Ch11.OmegaTopology.sequence_characterization pendulum z p).mpr
    exact ⟨fun n => (n : ℝ), fun n => ⟨by rw [hc]; trivial, Nat.cast_nonneg n⟩,
      tendsto_natCast_atTop_atTop, hp.comp tendsto_natCast_atTop_atTop⟩

/-- A singleton containing an equilibrium cannot equal any nonconstant orbit. -/
lemma singleton_not_nonconstant_orbit (q : Plane) :
    ¬ ∃ p : Plane, ¬ IsConstant pendulum p ∧ HasLeastPeriod pendulum p ∧
      ({q} : Set Plane) = orbit pendulum p := by
  rintro ⟨p, hn, _, he⟩
  have hX := flow_ivp pendulum pendulum_regular (show p ∈ pendulum.domain from mem_univ _)
  have hp : p ∈ orbit pendulum p := ⟨0, hX.2.1, hX.2.2⟩
  have hpq : p = q := mem_singleton_iff.mp (he.symm ▸ hp)
  apply hn
  intro t ht
  have hmem : flow pendulum t p ∈ orbit pendulum p := ⟨t, ht, rfl⟩
  exact (mem_singleton_iff.mp (he.symm ▸ hmem)).trans hpq.symm

theorem saddle_limit : Specs.D13Unified.Ch13.PendulumOrbits.SaddleLimit := by
  intro k
  obtain ⟨hc, hf⟩ := global_solution_eq_flow (separatrix k) (separatrix_deriv k)
  have hp : Tendsto (fun t => flow pendulum t (separatrix k 0)) atTop (𝓝 (saddle k)) := by
    simpa only [hf] using separatrix_tendsto k
  have ho := omega_eq_singleton_of_tendsto hc hp
  refine ⟨separatrix k 0, separatrix_energy k 0, separatrix_not_constant k, hc, hp, ho, ?_⟩
  rw [ho]
  exact singleton_not_nonconstant_orbit _

lemma flow_deriv {p : Plane} (hc : IsComplete pendulum p) (t : ℝ) :
    HasDerivAt (fun t => flow pendulum t p) (vectorField (flow pendulum t p)) t := by
  have hX := flow_ivp pendulum pendulum_regular (show p ∈ pendulum.domain from mem_univ _)
  simpa only [AutonomousODE.toODE_eval, pendulum_eval] using
    hX.1.2.2 t (by rw [hc]; trivial)

lemma flow_x_deriv {p : Plane} (hc : IsComplete pendulum p) (t : ℝ) :
    HasDerivAt (fun t => (flow pendulum t p) 0) ((flow pendulum t p) 1) t := by
  simpa [vectorField, Function.comp_def] using! (hasFDerivAt_apply (𝕜 := ℝ) 0 (flow pendulum t p)).comp_hasDerivAt t
    (flow_deriv hc t)

def reflect : Plane →L[ℝ] Plane := ContinuousLinearMap.pi
  ![ContinuousLinearMap.proj (0 : Fin 2), -ContinuousLinearMap.proj (1 : Fin 2)]
@[simp] lemma reflect_zero (z : Plane) : reflect z 0 = z 0 := by simp [reflect]
@[simp] lemma reflect_one (z : Plane) : reflect z 1 = -z 1 := by simp [reflect]

lemma reflect_flow_of_turning {p : Plane} (hc : IsComplete pendulum p) (hp : p 1 = 0)
    (t : ℝ) : reflect (flow pendulum t p) = flow pendulum (-t) p := by
  let u := fun r => reflect (flow pendulum (-r) p)
  have hd (r : ℝ) : HasDerivAt u (vectorField (u r)) r := by
    have h := reflect.hasFDerivAt.comp_hasDerivAt r
      ((flow_deriv hc (-r)).scomp r ((hasDerivAt_id r).neg))
    have he : vectorField (u r) = reflect ((-1 : ℝ) • vectorField (flow pendulum (-r) p)) := by
      ext i
      fin_cases i <;> simp [u, vectorField, reflect]
    convert h using 1
    · rfl
  have hu0 : u 0 = p := by
    have hzero := (flow_ivp pendulum pendulum_regular (show p ∈ pendulum.domain from mem_univ _)).2.2
    ext i
    fin_cases i <;> simp [u, hzero, hp]
  have he := (global_solution_eq_flow u hd).2 (-t)
  rw [hu0] at he
  simpa only [u, neg_neg] using he.symm

lemma oval_projection (k : ℤ) {e : ℝ} {z : Plane} (hz : z ∈ oval k e) :
    |z 0 - 2 * (k : ℝ) * Real.pi| ≤ Real.arccos (1-e) := by
  have he := hz.1
  dsimp [energy] at he
  have hb : 1-e ≤ Real.cos (z 0) := by nlinarith [sq_nonneg (z 1)]
  have hcos : Real.cos |z 0 - 2 * (k : ℝ) * Real.pi| = Real.cos (z 0) := by
    rw [Real.cos_abs]
    convert Real.cos_sub_int_mul_two_pi (z 0) k using 1 <;> congr 1 <;> ring
  calc
    _ = Real.arccos (Real.cos |z 0 - 2 * (k : ℝ) * Real.pi|) :=
      (Real.arccos_cos (abs_nonneg _) hz.2).symm
    _ = Real.arccos (Real.cos (z 0)) := by rw [hcos]
    _ ≤ _ := Real.arccos_le_arccos hb

lemma oval_turning (k : ℤ) {e : ℝ} {z : Plane} (hz : z ∈ oval k e) (hy : z 1 = 0) :
    |z 0 - 2 * (k : ℝ) * Real.pi| = Real.arccos (1-e) := by
  have he := hz.1
  dsimp [energy] at he
  have hc : Real.cos (z 0) = 1-e := by rw [hy] at he; nlinarith
  have hcos : Real.cos |z 0 - 2 * (k : ℝ) * Real.pi| = 1-e := by
    rw [Real.cos_abs]
    have hh := Real.cos_sub_int_mul_two_pi (z 0) k
    convert hh.trans hc using 1 <;> congr 1 <;> ring
  rw [← Real.arccos_cos (abs_nonneg _) hz.2, hcos]

/-- A nonconstant periodic orbit in a low-energy well fills the entire oval.
Extrema of the horizontal coordinate are its two turning points; reversal at
a turning point supplies both signs of the vertical coordinate. -/
lemma periodic_orbit_eq_oval (k : ℤ) {e : ℝ} (h0 : 0 < e) (h2 : e < 2)
    {p : Plane} (hp : p ∈ oval k e) (hn : ¬ IsConstant pendulum p)
    (hper : HasLeastPeriod pendulum p) : orbit pendulum p = oval k e := by
  obtain ⟨hc, T, hT, hperiod, _⟩ := hper
  have hstay := (oval_complete k h2 hp).2
  let f : ℝ → ℝ := fun t => (flow pendulum t p) 0
  have hcont : Continuous f := continuous_iff_continuousAt.mpr fun t => (flow_x_deriv hc t).continuousAt
  have hfp : Function.Periodic f T := fun t => congrFun (hperiod t) 0
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hT.le) hcont.continuousOn
  obtain ⟨b, hb, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT.le) hcont.continuousOn
  have hbounds (t : ℝ) : f a ≤ f t ∧ f t ≤ f b := by
    obtain ⟨r,hr,he⟩ := hfp.exists_mem_Ico₀ hT t
    rw [he]
    exact ⟨hmin ⟨hr.1,hr.2.le⟩,hmax ⟨hr.1,hr.2.le⟩⟩
  have hya : (flow pendulum a p) 1 = 0 :=
    (show IsMinOn f univ a from fun t _ => (hbounds t).1).isLocalMin (univ_mem) |>.hasDerivAt_eq_zero
      (flow_x_deriv hc a)
  have hyb : (flow pendulum b p) 1 = 0 :=
    (show IsMaxOn f univ b from fun t _ => (hbounds t).2).isLocalMax (univ_mem) |>.hasDerivAt_eq_zero
      (flow_x_deriv hc b)
  have hlt : f a < f b := by
    by_contra hh
    have heq : ∀ t : ℝ, f t = f 0 := by
      intro t
      have h1 := hbounds t
      have h2 := hbounds 0
      linarith
    have hy (t : ℝ) : (flow pendulum t p) 1 = 0 := by
      have hd : HasDerivAt f 0 t := (hasDerivAt_const t (f 0)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall heq)
      exact (flow_x_deriv hc t).unique hd
    apply hn
    intro t _
    have hzero : flow pendulum 0 p = p :=
      (flow_ivp pendulum pendulum_regular (show p ∈ pendulum.domain from mem_univ _)).2.2
    ext i
    fin_cases i
    · exact (heq t).trans (congrFun hzero 0)
    · change (flow pendulum t p) 1 = p 1
      rw [hy, ← hzero, hy]
  have hamin := oval_turning k (hstay a) hya
  have hbmax := oval_turning k (hstay b) hyb
  have hapos : 0 < Real.arccos (1-e) := Real.arccos_pos.mpr (by linarith)
  have hends : f a = 2 * (k : ℝ) * Real.pi - Real.arccos (1-e) ∧
      f b = 2 * (k : ℝ) * Real.pi + Real.arccos (1-e) := by
    rcases (abs_eq hapos.le).mp hamin with ha | ha <;>
      rcases (abs_eq hapos.le).mp hbmax with hb | hb <;>
      dsimp [f] at * <;> constructor <;> linarith
  have hreflect (z : Plane) (hz : z ∈ orbit pendulum p) : reflect z ∈ orbit pendulum p := by
    let q := flow pendulum a p
    have hq : q ∈ oval k e := hstay a
    have hreb := Ch11.Orbits.orbit_rebase pendulum pendulum_regular
      (show p ∈ pendulum.domain from mem_univ _) (s := a) (by rw [hc]; trivial)
    rw [← hreb] at hz ⊢
    obtain ⟨t,ht,rfl⟩ := hz
    rw [reflect_flow_of_turning (oval_complete k h2 hq).1 hya]
    exact ⟨-t, by rw [(oval_complete k h2 hq).1]; trivial, rfl⟩
  apply Subset.antisymm
  · rintro _ ⟨t,ht,rfl⟩
    exact hstay t
  · intro z hz
    have hproj := oval_projection k hz
    have hx : f a ≤ z 0 ∧ z 0 ≤ f b := by
      rw [hends.1,hends.2]
      constructor <;> linarith [(abs_le.mp hproj).1,(abs_le.mp hproj).2]
    obtain ⟨t,ht,hxt⟩ := isPreconnected_univ.intermediate_value (mem_univ a) (mem_univ b)
      hcont.continuousOn hx
    let w := flow pendulum t p
    have hw : w ∈ oval k e := hstay t
    have hwΓ : w ∈ orbit pendulum p := ⟨t,by rw [hc]; trivial,rfl⟩
    have he : (z 1)^2 = (w 1)^2 := by
      have hzE := hz.1
      have hwE := hw.1
      dsimp [energy] at hzE hwE
      change w 0 = z 0 at hxt
      rw [hxt] at hwE
      nlinarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp he with he | he
    · have hzw : z = w := by
        ext i
        fin_cases i
        · exact hxt.symm
        · exact he
      exact hzw ▸ hwΓ
    · have hzw : z = reflect w := by
        ext i
        fin_cases i
        · change z 0 = reflect w 0
          rw [reflect_zero]
          exact hxt.symm
        · change z 1 = reflect w 1
          rw [reflect_one]
          exact he
      exact hzw ▸ hreflect w hwΓ


/-- Coordinate identification with the product plane used by the planar
Poincaré–Bendixson interface. It is a real continuous linear equivalence. -/
def planePair : Plane ≃L[ℝ] (ℝ × ℝ) := ContinuousLinearEquiv.finTwoArrow ℝ ℝ

def pairPendulum : AutonomousODE (ℝ × ℝ) where
  domain := univ
  isOpen_domain := isOpen_univ
  field := fun z => planePair (vectorField (planePair.symm z.val))
  continuous_field := planePair.continuous.comp (vectorField_contDiff.continuous.comp
    (planePair.symm.continuous.comp continuous_subtype_val))

lemma pairPendulum_eval (z : ℝ × ℝ) :
    pairPendulum.eval z = planePair (vectorField (planePair.symm z)) := by
  simp [AutonomousODE.eval, Specs.D13Unified.Ch01.AutonomousParameters.autonomousEvalValue,
    pairPendulum]

lemma pairPendulum_regular : ContDiffOn ℝ 1 pairPendulum.eval pairPendulum.domain := by
  rw [show pairPendulum.eval = (fun z => planePair (vectorField (planePair.symm z))) from
    funext pairPendulum_eval]
  exact (planePair.contDiff.comp (vectorField_contDiff.comp planePair.symm.contDiff)).contDiffOn

/-- Transport of a complete vector-coordinate trajectory to the actual product
coordinate flow; its canonical maximal domain is proved to be all real time. -/
lemma pair_flow_of_complete {x : Plane} (hc : IsComplete pendulum x) :
    IsComplete pairPendulum (planePair x) ∧ ∀ t : ℝ,
      flow pairPendulum t (planePair x) = planePair (flow pendulum t x) := by
  let u : ℝ → ℝ × ℝ := fun t => planePair (flow pendulum t x)
  have hd (t : ℝ) : HasDerivAt u (pairPendulum.eval (u t)) t := by
    simpa [pairPendulum_eval, u, Function.comp_def] using!
      planePair.hasFDerivAt.comp_hasDerivAt t (flow_deriv hc t)
  let J : OpenTimeInterval := ⟨⟨univ,univ_nonempty,ordConnected_univ⟩,isOpen_univ⟩
  have hs : solutionOnValue pairPendulum.toODE J.toTimeInterval u := by
    refine ⟨(continuous_iff_continuousAt.mpr (fun t => (hd t).continuousAt)).continuousOn,
      fun _ _ => mem_univ _, ?_⟩
    intro t _
    simpa only [AutonomousODE.toODE_eval] using (hd t).hasDerivWithinAt
  have hu0 : u 0 = planePair x := by
    have hzero : flow pendulum 0 x = x :=
      (flow_ivp pendulum pendulum_regular (show x ∈ pendulum.domain from mem_univ _)).2.2
    exact congrArg planePair hzero
  have hivp : classicalIVPOnValue pairPendulum.toODE J u 0 (planePair x) :=
    ⟨(D13Unified.classical_iff_solutionOn _ _ _).mpr hs,mem_univ _,hu0⟩
  have h := (ODE.canonical_solution pairPendulum.toODE
    (pairPendulum.locallyLipschitzInState_of_contDiffOn pairPendulum_regular)
    0 (planePair x) (mem_univ _)).2.2.2.2.2.1 J u hivp
  exact ⟨Subset.antisymm (subset_univ _) h.1,fun t => h.2 (mem_univ t)⟩

/-- The reverse transport is proved from the differential equation and canonical
uniqueness, rather than assumed from the names of the two coordinate models. -/
lemma vector_flow_of_pair {q : ℝ × ℝ} (hc : IsComplete pairPendulum q) :
    IsComplete pendulum (planePair.symm q) ∧ ∀ t : ℝ,
      flow pendulum t (planePair.symm q) = planePair.symm (flow pairPendulum t q) := by
  let u := fun t => planePair.symm (flow pairPendulum t q)
  have hX := flow_ivp pairPendulum pairPendulum_regular
    (show q ∈ pairPendulum.domain from mem_univ _)
  have hd (t : ℝ) : HasDerivAt u (vectorField (u t)) t := by
    have h := planePair.symm.hasFDerivAt.comp_hasDerivAt t
      (hX.1.2.2 t (by rw [hc]; trivial))
    simpa [AutonomousODE.toODE_eval,pairPendulum_eval,u,Function.comp_def] using! h
  have hu0 : u 0 = planePair.symm q := congrArg planePair.symm hX.2.2
  simpa only [hu0] using global_solution_eq_flow u hd

lemma exists_periodic_oval (k : ℤ) {e : ℝ} (h0 : 0 < e) (h2 : e < 2) :
    ∃ p ∈ oval k e, ¬ IsConstant pendulum p ∧ HasLeastPeriod pendulum p ∧
      orbit pendulum p = oval k e := by
  let x := ovalPoint k e
  have hx : x ∈ oval k e := ovalPoint_mem k h0.le
  have hcomplete := pair_flow_of_complete (oval_complete k h2 hx).1
  have hsub : positiveOrbit pairPendulum (planePair x) ⊆ planePair '' oval k e := by
    rintro _ ⟨t,ht,rfl⟩
    change flow pairPendulum t (planePair x) ∈ planePair '' oval k e
    rw [hcomplete.2]
    exact mem_image_of_mem _ ((oval_complete k h2 hx).2 t)
  have hcompactS : IsCompact (planePair '' oval k e) :=
    (oval_isCompact k e).image planePair.continuous
  have hcl : closure (positiveOrbit pairPendulum (planePair x)) ⊆ planePair '' oval k e :=
    closure_minimal hsub hcompactS.isClosed
  have hcompact := hcompactS.of_isClosed_subset isClosed_closure hcl
  have hΩ := Ch11.Omega.compact_omega pairPendulum pairPendulum_regular (planePair x)
    (mem_univ _) hcompact (subset_univ _)
  have hreg : ∀ q ∈ omegaValue pairPendulum (planePair x), pairPendulum.eval q ≠ 0 := by
    intro q hq hz
    have hqS := hcl (hΩ.2.2.2.2.1 hq)
    obtain ⟨p,hp,rfl⟩ := hqS
    rw [pairPendulum_eval,ContinuousLinearEquiv.symm_apply_apply] at hz
    have hh : vectorField p = 0 := planePair.injective (by simpa using hz)
    exact energy_level_noncritical h0 h2 hp.1 hh
  obtain ⟨q,hq,_,hperiod,_⟩ := PoincareBendixson.poincare_bendixson pairPendulum
    pairPendulum_regular (planePair x) (mem_univ _) hcompact (subset_univ _) hreg
  have hqS := hcl (hΩ.2.2.2.2.1 hq)
  obtain ⟨p,hp,hpq⟩ := hqS
  subst q
  obtain ⟨hc,hf⟩ := vector_flow_of_pair hperiod.1
  simp only [ContinuousLinearEquiv.symm_apply_apply] at hc hf
  have hn : ¬ IsConstant pendulum p := by
    intro h
    have hh := (Ch11.Orbits.equilibrium_characterization pendulum pendulum_regular p
      (mem_univ _)).mpr h
    change pendulum.eval p = 0 at hh
    exact energy_level_noncritical h0 h2 hp.1 (by simpa using hh)
  obtain ⟨_,T,hT,hper,_⟩ := hperiod
  have hzero := (flow_ivp pairPendulum pairPendulum_regular
    (show planePair p ∈ pairPendulum.domain from mem_univ _)).2.2
  have hreturn : flow pendulum T p = flow pendulum 0 p := by
    rw [hf T,hf 0]
    exact congrArg planePair.symm (by simpa using hper 0)
  have hpper : HasLeastPeriod pendulum p := Ch11.Orbits.self_intersection_least_period
    pendulum pendulum_regular p (mem_univ _) hn
    0 (by rw [hc]; trivial) T (by rw [hc]; trivial) hT.ne hreturn.symm
  exact ⟨p,hp,hn,hpper,periodic_orbit_eq_oval k h0 h2 hp hn hpper⟩

lemma oval_connectedComponent (k : ℤ) {e : ℝ} (h0 : 0 < e) (h2 : e < 2)
    (hconn : IsConnected (oval k e)) :
    oval k e = connectedComponentIn {z : Plane | energy z = e} (ovalPoint k e) := by
  apply Subset.antisymm
  · exact hconn.isPreconnected.subset_connectedComponentIn (ovalPoint_mem k h0.le)
      (fun z hz => hz.1)
  · intro z hz
    have hzE : energy z = e := connectedComponentIn_subset {z : Plane | energy z = e} (ovalPoint k e) hz
    refine ⟨hzE, ?_⟩
    by_contra hh
    have hgt : Real.pi < |z 0 - 2 * (k : ℝ) * Real.pi| := lt_of_not_ge hh
    have hc : Continuous (fun z : Plane => |z 0 - 2 * (k : ℝ) * Real.pi|) :=
      (((continuous_apply (0 : Fin 2)).sub continuous_const).abs)
    have hbase : ovalPoint k e ∈ connectedComponentIn {z : Plane | energy z = e} (ovalPoint k e) :=
      mem_connectedComponentIn (ovalPoint_mem k h0.le).1
    obtain ⟨w,hw,hwe⟩ := (isPreconnected_connectedComponentIn
      (x := ovalPoint k e) (F := {z : Plane | energy z = e})).intermediate_value
      hbase hz hc.continuousOn
      (show Real.pi ∈ Icc (|((ovalPoint k e) 0) - 2 * (k : ℝ) * Real.pi|)
        (|z 0 - 2 * (k : ℝ) * Real.pi|) from ⟨by simp [ovalPoint,Real.pi_pos.le],hgt.le⟩)
    have hwE : energy w = e := connectedComponentIn_subset {z : Plane | energy z = e} (ovalPoint k e) hw
    exact (not_le_of_gt h2) (hwE ▸ energy_boundary k hwe)

theorem energy_ovals : Specs.D13Unified.Ch13.PendulumOrbits.EnergyOvals := by
  intro k e h0 h2
  obtain ⟨p,hp,hn,hper,heq⟩ := exists_periodic_oval k h0 h2
  have hcont : Continuous (fun t => flow pendulum t p) :=
    continuous_iff_continuousAt.mpr fun t => (flow_deriv hper.1 t).continuousAt
  have hconn : IsConnected (oval k e) := by
    rw [←heq,orbit,hper.1]
    exact isConnected_univ.image _ hcont.continuousOn
  exact ⟨oval_isCompact k e,hconn,oval_connectedComponent k h0 h2 hconn,
    fun z hz => ⟨energy_level_regular h0 h2 hz.1,energy_level_noncritical h0 h2 hz.1⟩,
    oval_invariant k h2, p,hp,hn,hper,heq.symm⟩

lemma oval_point_periodic (k : ℤ) {e : ℝ} (h0 : 0 < e) (h2 : e < 2)
    {z : Plane} (hz : z ∈ oval k e) :
    ¬ IsConstant pendulum z ∧ HasLeastPeriod pendulum z := by
  obtain ⟨p,hp,_,hper,heq⟩ := exists_periodic_oval k h0 h2
  have hn : ¬ IsConstant pendulum z := by
    intro h
    have hh := (Ch11.Orbits.equilibrium_characterization pendulum pendulum_regular z
      (mem_univ _)).mpr h
    change pendulum.eval z = 0 at hh
    exact energy_level_noncritical h0 h2 hz.1 (by simpa using hh)
  obtain ⟨s,hs,hsz⟩ := heq.symm ▸ hz
  obtain ⟨hc,T,hT,hperiod,_⟩ := hper
  have htr := Ch11.Flow.flow_translation pendulum pendulum_regular p (mem_univ _) s hs
  have hcz := (oval_complete k h2 hz).1
  have hreturn : flow pendulum T z = flow pendulum 0 z := by
    rw [←hsz]
    rw [htr.2 T (by rw [hc]; trivial),htr.2 0 (by rw [hc]; trivial)]
    simpa only [add_comm,zero_add,add_zero] using hperiod s
  exact ⟨hn,Ch11.Orbits.self_intersection_least_period pendulum pendulum_regular z
    (mem_univ _) hn 0 (by rw [hcz]; trivial) T (by rw [hcz]; trivial) hT.ne hreturn.symm⟩

theorem centers : Specs.D13Unified.Ch13.PendulumOrbits.Centers := by
  intro k
  refine ⟨centers_stable k, ?_⟩
  obtain ⟨r,hr,hmin⟩ := strict_energy_minima k
  let U := ball (center k) (min r Real.pi) ∩ {z : Plane | energy z < 2}
  have hc : energy (center k) = 0 := by simp [energy,PendulumPortrait.center,cos_center]
  refine ⟨U,isOpen_ball.inter (isOpen_lt energy_contDiff.continuous continuous_const),
    ⟨mem_ball_self (lt_min hr Real.pi_pos), by simpa only [mem_ofPred_eq,hc] using (show (0:ℝ)<2 by norm_num)⟩,?_⟩
  intro z hz hne
  have hdist : dist z (center k) < min r Real.pi := hz.1
  have hE : 0 < energy z := by
    have hh := hmin z (hdist.trans_le (min_le_left _ _)) hne
    rwa [hc] at hh
  apply oval_point_periodic k hE hz.2
  refine ⟨rfl,?_⟩
  have hh := norm_le_pi_norm (z-center k) 0
  have hnorm : ‖z-center k‖ < Real.pi := by
    simpa only [dist_eq_norm] using hdist.trans_le (min_le_right _ _)
  change |z 0 - 2*(k:ℝ)*Real.pi| ≤ Real.pi
  exact (show |z 0 - 2*(k:ℝ)*Real.pi| ≤ ‖z-center k‖ from hh).trans hnorm.le

lemma energy_smul_lt {v : Plane} (hv : |v 0| ≤ Real.pi) (he : 0 < energy v)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : energy (s • v) < energy v := by
  have habx : |s * v 0| = s * |v 0| := by rw [abs_mul,abs_of_pos hs.1]
  have hle : |s*v 0| ≤ |v 0| := by rw [habx]; exact mul_le_of_le_one_left (abs_nonneg _) hs.2.le
  have hcos : Real.cos (v 0) ≤ Real.cos (s*v 0) := by
    rw [←Real.cos_abs (v 0),←Real.cos_abs (s*v 0)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hv hle
  by_cases hy : v 1 = 0
  · have hx : v 0 ≠ 0 := by
      intro hx
      simp [energy,hx,hy] at he
    have hlt : |s*v 0| < |v 0| := by
      rw [habx]
      exact mul_lt_of_lt_one_left (abs_pos.mpr hx) hs.2
    have hcoslt : Real.cos (v 0) < Real.cos (s*v 0) := by
      rw [←Real.cos_abs (v 0),←Real.cos_abs (s*v 0)]
      exact Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg _) hv hlt
    simpa [energy,hy] using sub_lt_sub_left hcoslt 1
  · have hsq : (s*v 1)^2 < (v 1)^2 := by
      apply sq_lt_sq.mpr
      rw [abs_mul,abs_of_pos hs.1]
      exact mul_lt_of_lt_one_left (abs_pos.mpr hy) hs.2
    dsimp [energy,Pi.smul_apply,smul_eq_mul]
    linarith

def wellInterior (k : ℤ) (e : ℝ) : Set Plane :=
  {z | energy z < e ∧ |z 0 - 2*(k:ℝ)*Real.pi| < Real.pi}

lemma wellInterior_open (k : ℤ) (e : ℝ) : IsOpen (wellInterior k e) :=
  (isOpen_lt energy_contDiff.continuous continuous_const).inter
    (isOpen_lt (((continuous_apply (0:Fin 2)).sub continuous_const).abs) continuous_const)

lemma wellInterior_bounded (k : ℤ) (e : ℝ) : Bornology.IsBounded (wellInterior k e) := by
  apply (isCompact_closedBall (center k) (Real.pi+|e|+2)).isBounded.subset
  intro z hz
  rw [mem_closedBall,dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · change |z 0-2*(k:ℝ)*Real.pi| ≤ Real.pi+|e|+2
    linarith [hz.2,abs_nonneg e]
  · have hb : (z 1)^2 ≤ 2*e := by
      have he := hz.1
      dsimp [energy] at he
      nlinarith [Real.cos_le_one (z 0)]
    change |z 1-0| ≤ Real.pi+|e|+2
    rw [sub_zero]
    have hab : |z 1| ≤ |e|+2 := by
      have hh := sq_abs (z 1)
      nlinarith [abs_nonneg (z 1),sq_nonneg (|z 1|-1),le_abs_self e,
        sq_nonneg (|z 1|-(|e|+2)),sq_nonneg (|e|+1)]
    linarith [Real.pi_pos]

lemma wellInterior_frontier (k : ℤ) {e : ℝ} (h0 : 0 < e) (h2 : e < 2) :
    frontier (wellInterior k e) = oval k e := by
  rw [(wellInterior_open k e).frontier_eq]
  apply Subset.antisymm
  · intro z hz
    have hE : energy z ≤ e :=
      (closure_minimal (fun w hw => hw.1.le)
        (isClosed_le energy_contDiff.continuous continuous_const)) hz.1
    have hstrip : |z 0-2*(k:ℝ)*Real.pi| ≤ Real.pi :=
      (closure_minimal (fun w hw => hw.2.le)
        (isClosed_le (((continuous_apply (0:Fin 2)).sub continuous_const).abs) continuous_const)) hz.1
    have hstrict : |z 0-2*(k:ℝ)*Real.pi| < Real.pi := by
      apply lt_of_le_of_ne hstrip
      intro heq
      linarith [energy_boundary k heq]
    exact ⟨le_antisymm hE (le_of_not_gt (fun hh => hz.2 ⟨hh,hstrict⟩)),hstrip⟩
  · intro z hz
    refine ⟨?_,fun h => (ne_of_lt h.1) hz.1⟩
    let g : ℝ → Plane := fun s => s • (z-center k) + center k
    have hg : Continuous g := (continuous_id.smul continuous_const).add continuous_const
    have hg1 : g 1 = z := by simp [g]
    have hcl : (1 : ℝ) ∈ closure (Ioo (0:ℝ) 1) := by
      rw [closure_Ioo (by norm_num : (0:ℝ)≠1)]
      norm_num
    have hmap : MapsTo g (Ioo (0:ℝ) 1) (wellInterior k e) := by
      intro s hs
      have hE : energy (z-center k) = e := by
        have hh := energy_add_center (z-center k) k
        simpa only [sub_add_cancel,hz.1] using hh.symm
      have hx : |(z-center k) 0| ≤ Real.pi := hz.2
      refine ⟨?_,?_⟩
      · dsimp [g]
        rw [energy_add_center]
        exact (energy_smul_lt hx (by rw [hE]; exact h0) hs).trans_eq hE
      · change |s * (z 0 - 2*(k:ℝ)*Real.pi) + 2*(k:ℝ)*Real.pi - 2*(k:ℝ)*Real.pi| < Real.pi
        rw [add_sub_cancel_right,abs_mul,abs_of_pos hs.1]
        exact (mul_le_of_le_one_left (abs_nonneg _) hs.2.le).trans_lt (oval_strict_strip k h2 hz)
    rw [←hg1]
    exact hg.continuousAt.continuousWithinAt.mem_closure hcl hmap

theorem surrounding_ovals : Specs.D13Unified.Ch13.PendulumOrbits.Surrounding := by
  intro k e h0 h2
  refine ⟨wellInterior k e,wellInterior_open k e,wellInterior_bounded k e,?_,
    wellInterior_frontier k h0 h2⟩
  constructor
  · simpa [energy,PendulumPortrait.center,cos_center] using h0
  · simpa [PendulumPortrait.center] using Real.pi_pos

end D13Unified.Ch13.PendulumOrbits
