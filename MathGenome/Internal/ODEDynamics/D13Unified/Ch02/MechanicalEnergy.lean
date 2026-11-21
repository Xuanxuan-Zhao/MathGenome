import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch02.MechanicalEnergy
import MathGenome.Internal.ODEDynamics.D13Unified.Ch02.Separation
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace D13Unified.MechanicalEnergy

lemma velocity (d : Data) {t : ℝ} (ht : t ∈ d.I.carrier) :
    HasDerivAt d.y (deriv d.y t) t :=
  ((d.trajectory_c2.differentiableOn (by norm_num)) t ht).differentiableAt
    (d.I.isOpen.mem_nhds ht) |>.hasDerivAt

lemma energy_derivative (d : Data) {t : ℝ} (ht : t ∈ d.I.carrier) :
    HasDerivAt (energy d) 0 t := by
  have hp := (d.potential_deriv _ (d.graph ht)).comp t (velocity d ht).hasDerivWithinAt
    d.graph
  have h := (((d.equation t ht).pow 2).div_const 2).add
    (hp.hasDerivAt (d.I.isOpen.mem_nhds ht))
  change HasDerivAt (energy d) _ t at h
  convert h using 1
  norm_num
  ring

theorem conservation : Specs.D13Unified.Ch02.MechanicalEnergy.conservationExpected := by
  intro d s t hs ht
  have hc : ContinuousOn (energy d) d.I.carrier :=
    fun u hu => (energy_derivative d hu).continuousAt.continuousWithinAt
  have hi := integral_eq_sub_on_interval d.I.ordConnected hc
    (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) d.I.carrier)
    (fun u hu => (energy_derivative d hu).hasDerivWithinAt) hs ht
  have hz : energy d t - energy d s = 0 := by simpa using hi.symm
  exact sub_eq_zero.mp hz

lemma velocity_squared (d : Data) (b : Branch d) {t : ℝ} (ht : t ∈ b.K.carrier) :
    (deriv d.y t)^2 = 2 * (energy d b.s - d.V (d.y t)) := by
  have he := conservation d b.s t (b.subset_time b.mem_s) (b.subset_time ht)
  dsimp [energy] at he ⊢
  linarith

lemma signed_velocity (d : Data) (b : Branch d) {t : ℝ} (ht : t ∈ b.K.carrier) :
    deriv d.y t = b.σ * Real.sqrt (2 * (energy d b.s - d.V (d.y t))) := by
  rw [← velocity_squared d b ht, Real.sqrt_sq_eq_abs]
  rcases b.sign_choice with hp | hn
  · have hv := b.velocity_sign t ht
    rw [hp, one_mul] at hv ⊢
    exact (abs_of_nonneg hv).symm
  · have hv := b.velocity_sign t ht
    rw [hn, neg_one_mul] at hv ⊢
    rw [abs_of_nonpos (by linarith : deriv d.y t ≤ 0)]
    ring

lemma velocity_ne_zero (d : Data) (b : Branch d) {t : ℝ} (ht : t ∈ b.K.carrier) :
    deriv d.y t ≠ 0 := by
  have hp := b.positive t ht
  have hs := velocity_squared d b ht
  intro hz
  rw [hz] at hs
  nlinarith

lemma isOpen_range (d : Data) (b : Branch d) : IsOpen (d.y '' b.K.carrier) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro u ⟨t, ht, rfl⟩
  have hstrict := ((d.trajectory_c2.contDiffAt
    (d.I.isOpen.mem_nhds (b.subset_time ht))).of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)).hasStrictDerivAt'
    (velocity d (b.subset_time ht)) one_ne_zero
  rw [← hstrict.map_nhds_eq (velocity_ne_zero d b ht)]
  exact Filter.image_mem_map (b.K.isOpen.mem_nhds ht)

/-- The state interval is the actual trajectory range; its openness follows
from nonvanishing velocity rather than an extra assumption on the potential. -/
def stateInterval (d : Data) (b : Branch d) : OpenTimeInterval where
  carrier := d.y '' b.K.carrier
  nonempty := b.K.nonempty.image d.y
  ordConnected := (b.K.ordConnected.isPreconnected.image d.y
    (d.trajectory_c2.continuousOn.mono b.subset_time)).ordConnected
  isOpen := isOpen_range d b

lemma continuous_radical (d : Data) (b : Branch d) :
    ContinuousOn (fun u => b.σ * Real.sqrt (2 * (energy d b.s - d.V u)))
      (stateInterval d b).carrier := by
  have hsub : (stateInterval d b).carrier ⊆ d.J.carrier := by
    rintro u ⟨t, ht, rfl⟩
    exact d.graph (b.subset_time ht)
  exact continuousOn_const.mul ((continuousOn_const.mul
    (continuousOn_const.sub (d.potential_c1.continuousOn.mono hsub))).sqrt)

/-- All separation data are constructed from the mechanical trajectory. -/
def separationData (d : Data) (b : Branch d) : Separation.Data where
  I := b.K
  J := stateInterval d b
  a := fun _ => 1
  g := fun u => b.σ * Real.sqrt (2 * (energy d b.s - d.V u))
  continuous_a := continuousOn_const
  continuous_g := continuous_radical d b
  nonzero_g := by
    rintro u ⟨t, ht, rfl⟩
    rw [← signed_velocity d b ht]
    exact velocity_ne_zero d b ht
  s := b.s
  ξ := d.y b.s
  mem_s := b.mem_s
  mem_ξ := ⟨b.s, b.mem_s, rfl⟩

lemma branch_isSolution (d : Data) (b : Branch d) :
    IsClassicalSolutionOn (separationData d b).ode b.K d.y := by
  refine ⟨(d.trajectory_c2.of_le (by norm_num)).mono b.subset_time, ?_, ?_⟩
  · intro t ht
    exact ⟨ht, t, ht, rfl⟩
  · intro t ht
    have he := Separation.eval_ode (separationData d b) ht ⟨t, ht, rfl⟩
    rw [he]
    dsimp [separationData]
    rw [one_mul, ← signed_velocity d b ht]
    exact velocity d (b.subset_time ht)

theorem recovery : Specs.D13Unified.Ch02.MechanicalEnergy.recoveryExpected := by
  intro d b
  refine ⟨fun t ht => signed_velocity d b ht, separationData d b,
    rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  let z : Solution (separationData d b).ode := ⟨b.K, d.y, branch_isSolution d b⟩
  have hs : (separationData d b).s ∈ z.interval.carrier := b.mem_s
  have hξ : z.representative (separationData d b).s = (separationData d b).ξ := rfl
  refine ⟨?_, Separation.solution_subset_branch _ z hs hξ,
    Separation.solution_eq_formula _ z hs hξ, ?_⟩
  · intro t ht
    have h := Separation.primitive_solution (separationData d b) z hs hξ ht
    simpa [Separation.timePrimitive, separationData] using h
  · obtain ⟨x, hx, hf, hxs, hxξ, hext, hmax⟩ := Separation.separation (separationData d b)
    have hz := hext z hs hξ
    exact ⟨x, hx, hf, hmax, hz.1, hz.2⟩

end D13Unified.MechanicalEnergy
