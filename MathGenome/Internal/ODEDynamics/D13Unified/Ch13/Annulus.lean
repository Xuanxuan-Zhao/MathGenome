import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch13.Annulus
import MathGenome.Internal.ODEDynamics.D13Unified.Ch11.Flow
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

noncomputable section
open Set Filter
open scoped Topology ContDiff
namespace D13Unified.Ch13.Annulus
open Specs.D13Unified.Ch13.Annulus
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Ch06.StateDerivative

@[simp] lemma oscillator_eval (z : ℂ) : oscillator.eval z = vectorField z := by
  simp [AutonomousODE.eval, autonomousEvalValue, oscillator]

lemma smooth_vectorField : ContDiff ℝ 1 vectorField := by
  unfold vectorField
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_norm_sq ℝ))).mul
    contDiff_id).add (contDiff_const.mul contDiff_id)

lemma oscillator_c1 : ContDiffOn ℝ 1 oscillator.eval oscillator.domain := by
  have he : oscillator.eval = vectorField := funext oscillator_eval
  rw [he]
  exact smooth_vectorField.contDiffOn

theorem cartesian_field : CartesianField := by
  intro z
  have hn : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.sq_norm z)
  change _ ∧ _
  simp only [vectorField, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  rw [hn]
  constructor <;> ring

lemma polar_norm (r θ : ℝ) : ‖polar r θ‖ = |r| := by
  simp [polar, Complex.norm_exp_ofReal_mul_I]

lemma rotation_deriv (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp ((u : ℂ) * Complex.I))
      (Complex.I * Complex.exp ((t : ℂ) * Complex.I)) t := by
  convert ((Complex.hasDerivAt_exp ((t : ℂ) * Complex.I)).comp t
    ((hasDerivAt_id t).ofReal_comp.mul_const Complex.I)) using 1 <;> simp [Function.comp_def, mul_comm]

theorem polar_to_cartesian : PolarToCartesian := by
  intro r θ t hr hdr hdθ
  have he := (Complex.hasDerivAt_exp ((θ t : ℂ) * Complex.I)).comp t
    (hdθ.ofReal_comp.mul_const Complex.I)
  have hd := hdr.ofReal_comp.mul he
  convert hd using 1
  · rfl
  dsimp [polar, vectorField, Function.comp_def]
  rw [norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I, mul_one, Real.norm_eq_abs, abs_of_pos hr]
  push_cast
  ring

/-- Denominator of the explicit solution. Its positive set is an open interval
containing zero, even for radii greater than one (which can blow up backwards). -/
def denominator (z : ℂ) (t : ℝ) : ℝ := ‖z‖^2 + (1-‖z‖^2)*Real.exp (-2*t)
def trajectory (z : ℂ) (t : ℝ) : ℂ :=
  ((1 / Real.sqrt (denominator z t) : ℝ) : ℂ) *
    Complex.exp ((t : ℂ)*Complex.I) * z

@[simp] lemma denominator_zero (z : ℂ) : denominator z 0 = 1 := by
  simp [denominator]

lemma continuous_denominator (z : ℂ) : Continuous (denominator z) := by
  unfold denominator
  fun_prop

lemma positive_denominator_forward {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    0 < denominator z t := by
  have hq : 0 < ‖z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
  have he0 := Real.exp_pos (-2*t)
  have he1 : Real.exp (-2*t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  by_cases hq1 : ‖z‖^2 ≤ 1
  · dsimp [denominator]; positivity
  · dsimp [denominator]; nlinarith

lemma denominator_ordConnected (z : ℂ) : OrdConnected {t | 0 < denominator z t} := by
  constructor
  intro a ha b hb t ht
  have hea : Real.exp (-2*t) ≤ Real.exp (-2*a) := Real.exp_le_exp.mpr (by linarith [ht.1])
  have heb : Real.exp (-2*b) ≤ Real.exp (-2*t) := Real.exp_le_exp.mpr (by linarith [ht.2])
  change 0 < denominator z a at ha
  change 0 < denominator z b at hb
  change 0 < denominator z t
  dsimp [denominator] at *
  by_cases hq : ‖z‖^2 ≤ 1
  · nlinarith
  · nlinarith

def explicitInterval (z : ℂ) : OpenTimeInterval where
  carrier := {t | 0 < denominator z t}
  nonempty := ⟨0, by simp⟩
  ordConnected := denominator_ordConnected z
  isOpen := isOpen_lt continuous_const (continuous_denominator z)

@[simp] lemma trajectory_zero (z : ℂ) : trajectory z 0 = z := by
  simp [trajectory]


theorem cartesian_derivative : CartesianDerivative := by
  intro z t
  have hc := cartesian_field (z t)
  constructor
  · intro h
    exact ⟨hc.1 ▸ Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h,
      hc.2 ▸ Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h⟩
  · rintro ⟨hre, him⟩
    have hd := hre.ofReal_comp.add (him.ofReal_comp.mul_const Complex.I)
    convert hd using 1
    · funext u
      exact (Complex.re_add_im (z u)).symm
    · rw [← hc.1, ← hc.2]
      exact (Complex.re_add_im (vectorField (z t))).symm

lemma denominator_deriv (z : ℂ) (t : ℝ) :
    HasDerivAt (denominator z) (-2*(1-‖z‖^2)*Real.exp (-2*t)) t := by
  convert (((hasDerivAt_id t).const_mul (-2)).exp.const_mul (1-‖z‖^2)).const_add (‖z‖^2)
    using 1
  · rfl
  · simp only [id_eq]; ring

lemma amplitude_deriv (z : ℂ) {t : ℝ} (ht : 0 < denominator z t) :
    HasDerivAt (fun u => 1 / Real.sqrt (denominator z u))
      ((1 / Real.sqrt (denominator z t)) *
        (1-‖z‖^2*(1 / Real.sqrt (denominator z t))^2)) t := by
  have hs := Real.sqrt_pos.mpr ht
  have hsq := Real.sq_sqrt ht.le
  have hd := ((denominator_deriv z t).sqrt ht.ne').inv hs.ne'
  convert hd using 1
  · simp only [one_div]; rfl
  · field_simp [hs.ne']
    rw [hsq]
    dsimp [denominator]
    ring

lemma trajectory_norm (z : ℂ) {t : ℝ} (ht : 0 < denominator z t) :
    ‖trajectory z t‖ = ‖z‖ / Real.sqrt (denominator z t) := by
  simp [trajectory,
    abs_of_pos (Real.sqrt_pos.mpr ht), div_eq_mul_inv, mul_comm]

lemma trajectory_norm_sq (z : ℂ) {t : ℝ} (ht : 0 < denominator z t) :
    ‖trajectory z t‖^2 = ‖z‖^2 / denominator z t := by
  rw [trajectory_norm z ht, div_pow, Real.sq_sqrt ht.le]

lemma trajectory_deriv (z : ℂ) {t : ℝ} (ht : 0 < denominator z t) :
    HasDerivAt (trajectory z) (vectorField (trajectory z t)) t := by
  have hd := ((amplitude_deriv z ht).ofReal_comp.mul (rotation_deriv t)).mul_const z
  convert hd using 1
  · rfl
  dsimp [vectorField, Function.comp_def]
  rw [trajectory_norm_sq z ht]
  have he : (denominator z t : ℂ) = (Real.sqrt (denominator z t) : ℂ)^2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt ht.le]
  dsimp [trajectory]
  push_cast
  rw [he]
  ring

lemma trajectory_solution (z : ℂ) :
    classicalIVPOnValue oscillator.toODE (explicitInterval z) (trajectory z) 0 z := by
  have hd (t : ℝ) (ht : t ∈ (explicitInterval z).carrier) := trajectory_deriv z ht
  refine ⟨⟨?_, fun t ht => mem_univ _, ?_⟩, by simp [explicitInterval], trajectory_zero z⟩
  · have hdiff : DifferentiableOn ℝ (trajectory z) (explicitInterval z).carrier :=
      fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
    rw [show (1 : ℕ∞ω) = 0+1 from rfl,
      contDiffOn_succ_iff_deriv_of_isOpen (explicitInterval z).isOpen]
    refine ⟨hdiff, by simp, ?_⟩
    rw [contDiffOn_zero]
    have he : EqOn (deriv (trajectory z)) (fun t => vectorField (trajectory z t))
        (explicitInterval z).carrier := fun t ht => (hd t ht).deriv
    exact (continuous_vectorField.comp_continuousOn hdiff.continuousOn).congr he
  · intro t ht
    simpa only [AutonomousODE.toODE_eval, oscillator_eval] using hd t ht

/-- Comparison with the shared canonical maximal solution also proves that
all times in the explicit formula's interval are allowed canonical times. -/
lemma flow_eq_trajectory (z : ℂ) :
    (explicitInterval z).carrier ⊆ (flowInterval oscillator z).carrier ∧
    EqOn (fun t => flow oscillator t z) (trajectory z) (explicitInterval z).carrier := by
  have hc := ODE.canonical_solution oscillator.toODE
    (oscillator.locallyLipschitzInState_of_contDiffOn oscillator_c1) 0 z (mem_univ _)
  exact hc.2.2.2.2.2.1 _ _ (trajectory_solution z)

lemma forward_complete {z : ℂ} (hz : z ≠ 0) :
    Ici (0 : ℝ) ⊆ (flowInterval oscillator z).carrier :=
  fun _ ht => (flow_eq_trajectory z).1 (positive_denominator_forward hz ht)

lemma flow_forward_formula {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : 0 ≤ t) :
    flow oscillator t z = trajectory z t :=
  (flow_eq_trajectory z).2 (positive_denominator_forward hz ht)


lemma vectorField_ne_zero {z : ℂ} (hz : z ≠ 0) : vectorField z ≠ 0 := by
  rw [vectorField, ← add_mul]
  apply mul_ne_zero _ hz
  intro he
  have hi := congrArg Complex.im he
  simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, Complex.zero_im, zero_add] at hi
  norm_num at hi

theorem no_equilibrium : NoEquilibrium := by
  intro z hz
  apply vectorField_ne_zero
  intro he
  have := hz.1
  rw [he, norm_zero] at this
  norm_num at this

lemma trajectory_mem_annulus {z : ℂ} (hz : z ∈ annulus) {t : ℝ} (ht : 0 ≤ t) :
    trajectory z t ∈ annulus := by
  have hn : z ≠ 0 := by
    intro he
    have := hz.1
    simp only [he, norm_zero] at this
    norm_num at this
  have hD := positive_denominator_forward hn ht
  have he0 := (Real.exp_pos (-2*t)).le
  have he1 : Real.exp (-2*t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hq0 := sq_nonneg ‖z‖
  have hqlo : (1/4:ℝ) ≤ ‖z‖^2 := by nlinarith [hz.1]
  have hqhi : ‖z‖^2 ≤ (4:ℝ) := by nlinarith [hz.2, norm_nonneg z]
  have hlo : denominator z t ≤ 4 * ‖z‖^2 := by
    dsimp [denominator]
    by_cases hq : ‖z‖^2 ≤ 1
    · nlinarith [mul_nonneg (sub_nonneg.mpr he1) (sub_nonneg.mpr hq)]
    · nlinarith [mul_nonneg he0 (show 0 ≤ ‖z‖^2-1 by linarith)]
  have hhi : ‖z‖^2 ≤ 4 * denominator z t := by
    dsimp [denominator]
    by_cases hq : ‖z‖^2 ≤ 1
    · nlinarith [mul_nonneg he0 (sub_nonneg.mpr hq)]
    · nlinarith [mul_nonneg (sub_nonneg.mpr he1) (show 0 ≤ ‖z‖^2-1 by linarith)]
  have hsq := trajectory_norm_sq z hD
  have hsmall : (1/4:ℝ) ≤ ‖trajectory z t‖^2 := by
    rw [hsq, le_div_iff₀ hD]
    nlinarith [hlo]
  have hbig : ‖trajectory z t‖^2 ≤ (4:ℝ) := by
    rw [hsq, div_le_iff₀ hD]
    exact hhi
  change (1/2:ℝ) ≤ ‖trajectory z t‖ ∧ ‖trajectory z t‖ ≤ 2
  constructor <;> nlinarith [norm_nonneg (trajectory z t)]

theorem positive_invariance : PositiveInvariance := by
  refine ⟨subset_univ _, ?_⟩
  intro z hz t _ ht
  have hn : z ≠ 0 := by
    intro he
    have := hz.1
    simp only [he, norm_zero] at this
    norm_num at this
  rw [flow_forward_formula hn ht]
  exact trajectory_mem_annulus hz ht

lemma denominator_tendsto (z : ℂ) :
    Tendsto (denominator z) atTop (𝓝 (‖z‖^2)) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-2*t)) atTop (𝓝 0) := by
    simpa only [neg_mul, Function.comp_def, id_eq] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (show (0:ℝ)<2 by norm_num))
  have h := (tendsto_const_nhds (x := ‖z‖^2)).add
    ((tendsto_const_nhds (x := 1-‖z‖^2)).mul he)
  change Tendsto (fun t => ‖z‖^2+(1-‖z‖^2)*Real.exp (-2*t)) atTop _
  simpa only [mul_zero, add_zero] using h

lemma forward_radius_tendsto {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun t => ‖flow oscillator t z‖) atTop (𝓝 1) := by
  have hn := norm_ne_zero_iff.mpr hz
  have h := (tendsto_const_nhds (x := ‖z‖)).div (denominator_tendsto z).sqrt
    (show Real.sqrt (‖z‖^2) ≠ 0 by simpa [Real.sqrt_sq_eq_abs, abs_norm] using hn)
  have hr : Tendsto (fun t => ‖z‖ / Real.sqrt (denominator z t)) atTop (𝓝 1) := by
    convert h using 1; simp only [Real.sqrt_sq_eq_abs, abs_norm, div_self hn]
  apply hr.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [flow_forward_formula hz ht, trajectory_norm z (positive_denominator_forward hz ht)]

lemma distance_to_circle_le (z : ℂ) : Metric.infDist z unitCircle ≤ |‖z‖-1| := by
  let w := Complex.exp ((z.arg : ℂ)*Complex.I)
  have hw : w ∈ unitCircle := Complex.norm_exp_ofReal_mul_I z.arg
  have he : z-w = ((‖z‖-1:ℝ):ℂ)*w := by
    dsimp [w]
    push_cast
    linear_combination -(Complex.norm_mul_exp_arg_mul_I z)
  calc
    Metric.infDist z unitCircle ≤ dist z w := Metric.infDist_le_dist_of_mem hw
    _ = |‖z‖-1| := by
      rw [dist_eq_norm, he, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      dsimp [w]
      rw [Complex.norm_exp_ofReal_mul_I, mul_one]

theorem forward_attraction : ForwardAttraction := by
  intro z hz
  refine ⟨forward_complete hz, ?_, ?_⟩
  · intro t ht
    rw [flow_forward_formula hz ht]
    apply norm_pos_iff.mp
    rw [trajectory_norm z (positive_denominator_forward hz ht)]
    exact div_pos (norm_pos_iff.mpr hz)
      (Real.sqrt_pos.mpr (positive_denominator_forward hz ht))
  · have h : Tendsto (fun t => |‖flow oscillator t z‖-1|) atTop (𝓝 0) := by
      simpa using ((forward_radius_tendsto hz).sub_const 1).abs
    exact squeeze_zero (fun t => Metric.infDist_nonneg)
      (fun t => distance_to_circle_le _) h

@[simp] lemma circleCurve_eq (t : ℝ) : circleCurve t = Complex.exp ((t : ℂ)*Complex.I) := by
  simp [circleCurve, polar]

lemma circle_deriv (t : ℝ) : HasDerivAt circleCurve (vectorField (circleCurve t)) t := by
  change HasDerivAt (fun u : ℝ => (1:ℂ)*Complex.exp ((u:ℂ)*Complex.I)) _ t
  simpa [circleCurve_eq, vectorField, Complex.norm_exp_ofReal_mul_I] using rotation_deriv t

lemma circle_periodic : Function.Periodic circleCurve (2*Real.pi) := by
  intro t
  simp only [circleCurve_eq, Complex.ofReal_add, add_mul, Complex.exp_add]
  rw [show (((2*Real.pi:ℝ):ℂ)*Complex.I) = 2*Real.pi*Complex.I by push_cast; ring,
    Complex.exp_two_pi_mul_I, mul_one]

lemma circle_least_period {T : ℝ} (hT : 0 < T) (hper : Function.Periodic circleCurve T) :
    2*Real.pi ≤ T := by
  have he : Complex.exp ((T:ℂ)*Complex.I) = 1 := by
    simpa using hper 0
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp he
  have hk' : T = (k:ℝ)*(2*Real.pi) := by
    have hi := congrArg Complex.im hk
    simpa using hi
  have hkpos : (0:ℝ) < (k:ℝ) := by
    rw [hk'] at hT
    exact (mul_pos_iff_of_pos_right Real.two_pi_pos).mp hT
  have hk1 : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast (show (1:ℤ) ≤ k by exact_mod_cast hkpos)
  rw [hk']
  nlinarith [Real.pi_pos]

theorem circle_in_annulus : CircleInAnnulus := by
  intro z hz
  change (1/2:ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 2
  rw [show ‖z‖ = 1 from hz]
  norm_num

lemma canonical_circle : (flowInterval oscillator (1:ℂ)).carrier = univ ∧
    ∀ t : ℝ, flow oscillator t 1 = circleCurve t := by
  have hD (t : ℝ) : denominator (1:ℂ) t = 1 := by simp [denominator]
  have hI : (explicitInterval (1:ℂ)).carrier = univ := by
    ext t
    simp [explicitInterval, hD]
  have hsub := (flow_eq_trajectory (1:ℂ)).1
  rw [hI] at hsub
  refine ⟨Subset.antisymm (subset_univ _) hsub, ?_⟩
  intro t
  have ht : t ∈ (explicitInterval (1:ℂ)).carrier := by rw [hI]; exact mem_univ _
  exact ((flow_eq_trajectory (1:ℂ)).2 ht).trans (by
    simp [trajectory, hD, circleCurve_eq])

theorem periodic_circle : PeriodicCircle := by
  refine ⟨canonical_circle, circle_deriv, ?_, ?_, Real.two_pi_pos, circle_periodic,
    fun T hT hper => circle_least_period hT hper⟩
  · ext z
    simp only [mem_range, mem_ofPred_eq, unitCircle, circleCurve_eq]
    exact (Complex.norm_eq_one_iff z).symm
  · refine ⟨0, Real.pi, ?_⟩
    norm_num [circleCurve_eq, Complex.exp_pi_mul_I]


/-- A real radius on the actual positive-denominator interval. -/
def explicitRadius (z : ℂ) (t : ℝ) : ℝ := ‖z‖*(1/Real.sqrt (denominator z t))

lemma explicitRadius_pos {z : ℂ} (hz : z ≠ 0) {t : ℝ} (ht : 0 < denominator z t) :
    0 < explicitRadius z t := by
  dsimp [explicitRadius]
  exact mul_pos (norm_pos_iff.mpr hz) (one_div_pos.mpr (Real.sqrt_pos.mpr ht))

lemma explicitRadius_deriv (z : ℂ) {t : ℝ} (ht : 0 < denominator z t) :
    HasDerivAt (explicitRadius z)
      (explicitRadius z t*(1-explicitRadius z t^2)) t := by
  convert (amplitude_deriv z ht).const_mul ‖z‖ using 1
  · rfl
  · dsimp [explicitRadius]; ring

lemma trajectory_polar (z : ℂ) (t : ℝ) :
    trajectory z t = polar (explicitRadius z t) (t+z.arg) := by
  calc
    trajectory z t = ((1/Real.sqrt (denominator z t):ℝ):ℂ) *
        Complex.exp ((t:ℂ)*Complex.I) *
        ((‖z‖:ℂ)*Complex.exp ((z.arg:ℂ)*Complex.I)) := by
      rw [Complex.norm_mul_exp_arg_mul_I]; rfl
    _ = polar (explicitRadius z t) (t+z.arg) := by
      simp only [polar, explicitRadius, Complex.ofReal_mul, Complex.ofReal_add,
        add_mul, Complex.exp_add]
      ring

/-- The radius derivative and a differentiable angular lift are attached to the
actual given solution by uniqueness, after translating its base time. -/
theorem local_polar : LocalPolar := by
  intro I z hz s hs hzs
  let K := (explicitInterval (z s)).elapsed (-s)
  have hsK : s ∈ K.carrier := by
    simp [K, OpenTimeInterval.elapsed, TimeInterval.elapsed, explicitInterval]
  let J : OpenTimeInterval :=
    { carrier := I.carrier ∩ K.carrier
      nonempty := ⟨s, hs, hsK⟩
      ordConnected := I.ordConnected.inter K.ordConnected
      isOpen := I.isOpen.inter K.isOpen }
  have hzODE := (D13Unified.classicalAutonomousSolutionOn_iff oscillator I z).mp hz
  have hzshift : classicalIVPOnValue oscillator.toODE (I.elapsed s)
      (fun u => z (s+u)) 0 (z s) := by
    refine ⟨Ch11.Flow.shift_solution oscillator I z hzODE s, ?_, by simp⟩
    simpa [OpenTimeInterval.elapsed, TimeInterval.elapsed] using hs
  have hc := ODE.canonical_solution oscillator.toODE
    (oscillator.locallyLipschitzInState_of_contDiffOn oscillator_c1) 0 (z s) (mem_univ _)
  have hcomp := hc.2.2.2.2.2.1 _ _ hzshift
  refine ⟨J, (fun t => explicitRadius (z s) (t-s)), (fun t => t-s+(z s).arg),
    ⟨hs,hsK⟩, inter_subset_left, ?_⟩
  intro t ht
  have htI : t-s ∈ (I.elapsed s).carrier := by
    simpa [OpenTimeInterval.elapsed, TimeInterval.elapsed] using ht.1
  have htD : 0 < denominator (z s) (t-s) := by
    simpa [K, OpenTimeInterval.elapsed, TimeInterval.elapsed, explicitInterval,
      sub_eq_add_neg, add_comm] using ht.2
  have hrep : z t = trajectory (z s) (t-s) := by
    have h1 := hcomp.2 htI
    have h2 := (flow_eq_trajectory (z s)).2 htD
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1.symm.trans h2
  refine ⟨explicitRadius_pos hzs htD, ?_, ?_, ?_, ?_⟩
  · rw [hrep, trajectory_norm (z s) htD]
    dsimp [explicitRadius]; ring
  · rw [hrep, trajectory_polar]
  · convert (explicitRadius_deriv (z s) htD).scomp t ((hasDerivAt_id t).sub_const s)
      using 1 <;> simp only [Function.comp_def, id_eq, one_smul]
  · simpa only [id_eq] using ((hasDerivAt_id t).sub_const s).add_const (z s).arg

end D13Unified.Ch13.Annulus
