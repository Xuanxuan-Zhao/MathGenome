import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch12.ZeroExample
import MathGenome.Internal.ODEDynamics.D13Unified.Ch12.StabilityDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap
import MathGenome.Internal.ODEDynamics.D13Unified.Ch03.DerivativeCriterion
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

noncomputable section
open Set Filter
open scoped Topology
namespace D13Unified.Ch12.ZeroExample
open Specs.D13Unified.Ch12.ZeroExample
open Specs.D13Unified.Ch01.AutonomousParameters
open Specs.D13Unified.Ch01.SolutionConcepts
open Specs.D13Unified.Ch04.MaximalSolutionMap
open Specs.D13Unified.Ch12.StabilityDefinitions
open Ch06.StateDerivative

@[simp] lemma cubic_eval (a x : ℝ) : autonomousEvalValue (cubicODE a) x = a*x^3 := by
  simp [autonomousEvalValue, cubicODE]

@[simp] lemma cubic_eval_fun (a : ℝ) :
    autonomousEvalValue (cubicODE a) = fun x => a*x^3 := funext (cubic_eval a)

lemma cubic_smooth (a : ℝ) : ContDiffOn ℝ 1 (autonomousEvalValue (cubicODE a)) univ := by
  rw [cubic_eval_fun]
  exact (contDiff_const.mul (contDiff_id.pow 3)).contDiffOn

/-- All three source fields are smooth, vanish at zero, and have derivative zero there. -/
theorem field_properties : FieldProperties := by
  intro a
  refine ⟨cubic_smooth a, by simp, ?_⟩
  rw [cubic_eval_fun]
  convert ((hasDerivAt_id (0 : ℝ)).pow 3).const_mul a using 1 <;> norm_num

/-- An open interval containing zero, with positive radicand throughout. -/
def radicandInterval (a x : ℝ) : OpenTimeInterval where
  carrier := {t | 0 < 1-2*a*t*x^2}
  nonempty := ⟨0, by simp⟩
  ordConnected := by
    constructor
    intro u hu v hv t ht
    dsimp at hu hv ⊢
    by_cases hk : 0 ≤ 2*a*x^2
    · have h := mul_le_mul_of_nonneg_left ht.2 hk
      nlinarith
    · have h := mul_le_mul_of_nonpos_left ht.1 (le_of_not_ge hk)
      nlinarith
  isOpen := isOpen_lt continuous_const (continuous_const.sub
    (continuous_const.mul continuous_id |>.mul continuous_const))

lemma cubicCurve_deriv (a x t : ℝ) (ht : 0 < 1-2*a*t*x^2) :
    HasDerivAt (cubicCurve a x) (a*(cubicCurve a x t)^3) t := by
  have hs : Real.sqrt (1-2*a*t*x^2) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 ht)
  have hd : HasDerivAt (fun t : ℝ => 1-2*a*t*x^2) (-2*a*x^2) t := by
    apply ((hasDerivAt_const t (1 : ℝ)).sub
      (((hasDerivAt_id t).const_mul (2*a)).mul_const (x^2))).congr_deriv
    ring
  have h := (hasDerivAt_const t x).div (hd.sqrt (ne_of_gt ht)) hs
  apply h.congr_deriv
  dsimp [cubicCurve]
  field_simp; ring

lemma cubicCurve_ivp (a x : ℝ) :
    classicalIVPOnValue (autonomousToODEValue (cubicODE a))
      (radicandInterval a x) (cubicCurve a x) 0 x := by
  refine ⟨⟨?_, fun _ _ => mem_univ _, ?_⟩, by simp [radicandInterval], ?_⟩
  · apply ContDiffOn.div contDiffOn_const
      ((contDiffOn_const.sub ((contDiffOn_const.mul contDiffOn_id).mul
        contDiffOn_const)).sqrt (fun t ht => ne_of_gt ht))
    exact fun t ht => ne_of_gt (Real.sqrt_pos.2 ht)
  · intro t ht
    simpa [autonomousToODEValue, ODE.eval, cubicODE] using cubicCurve_deriv a x t ht
  · simp [cubicCurve]

lemma cubic_canonical_cover (a x : ℝ) :
    (radicandInterval a x).carrier ⊆ (flowInterval (cubicODE a) x).carrier ∧
    EqOn (fun t => flow (cubicODE a) t x) (cubicCurve a x)
      (radicandInterval a x).carrier := by
  have h := ODE.canonical_solution (autonomousToODEValue (cubicODE a))
    ((cubicODE a).locallyLipschitzInState_of_contDiffOn (cubic_smooth a)) 0 x
    (show (0,x) ∈ (autonomousToODEValue (cubicODE a)).domain from mem_univ _)
  exact h.2.2.2.2.2.1 _ _ (cubicCurve_ivp a x)

/-- Global forward existence and the explicit solution, including x₀ = 0. -/
theorem negative_formula : NegativeFormula := by
  intro x t ht
  have hr : t ∈ (radicandInterval (-1) x).carrier := by
    dsimp [radicandInterval]
    nlinarith [mul_nonneg ht (sq_nonneg x)]
  refine ⟨⟨mem_univ _, (cubic_canonical_cover (-1) x).1 hr⟩, ?_⟩
  simpa [cubicCurve] using (cubic_canonical_cover (-1) x).2 hr

lemma negative_norm_bound (x t : ℝ) (ht : 0 ≤ t) :
    ‖flow (cubicODE (-1)) t x‖ ≤ ‖x‖ := by
  rw [(negative_formula x t ht).2, norm_div,
    Real.norm_eq_abs (Real.sqrt _), abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_self (norm_nonneg _)
  apply Real.one_le_sqrt.mpr
  nlinarith [mul_nonneg ht (sq_nonneg x)]

lemma negative_tendsto (x : ℝ) :
    Tendsto (fun t => flow (cubicODE (-1)) t x) atTop (𝓝 0) := by
  have he : (fun t => flow (cubicODE (-1)) t x) =ᶠ[atTop]
      (fun t => x / Real.sqrt (1+2*t*x^2)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact (negative_formula x t ht).2
  apply Tendsto.congr' he.symm
  by_cases hx : x = 0
  · simp [hx]
  · have hsq : 0 < 2*x^2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hx)
    have hr : Tendsto (fun t : ℝ => 1+2*t*x^2) atTop atTop := by
      apply tendsto_atTop_mono (f := fun t : ℝ => (2*x^2)*t)
        (fun t => ?_) (tendsto_id.const_mul_atTop hsq)
      nlinarith
    exact tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp hr)

/-- The norm never increases, and every initial state tends to zero. -/
theorem negative_stability : NegativeStability := by
  intro hF
  constructor
  · intro ε hε
    refine ⟨ε, hε, fun x _ hx => ⟨?_, ?_⟩⟩
    · exact fun t ht => (negative_formula x t ht).1
    · exact fun t ht => (negative_norm_bound x t ht).trans_lt hx
  · exact ⟨1, zero_lt_one, fun x _ _ =>
      ⟨fun t ht => (negative_formula x t ht).1, negative_tendsto x⟩⟩

/-- Every trajectory of the zero field is constant on the whole real line. -/
theorem zero_formula : ZeroFormula := by
  intro x t
  have hr : t ∈ (radicandInterval 0 x).carrier := by simp [radicandInterval]
  exact ⟨⟨mem_univ _, (cubic_canonical_cover 0 x).1 hr⟩,
    (cubic_canonical_cover 0 x).2 hr |>.trans (by simp [cubicCurve])⟩

/-- A nonzero constant trajectory in every ball excludes attraction. -/
theorem zero_stability : ZeroStability := by
  intro hF
  constructor
  · intro ε hε
    refine ⟨ε, hε, fun x _ hx => ⟨fun t _ => (zero_formula x t).1, ?_⟩⟩
    intro t _
    simpa only [(zero_formula x t).2] using hx
  · rintro ⟨δ, hδ, h⟩
    have hx : ‖δ/2‖ < δ := by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; linarith
    have hz := h (δ/2) hx
    simp only [(zero_formula (δ/2) _).2] at hz
    have he : δ/2 = 0 := tendsto_nhds_unique tendsto_const_nhds hz
    linarith

lemma positive_radicand (x t : ℝ) (hx : 0 < x) :
    t ∈ (radicandInterval 1 x).carrier ↔ t < escapeTime x := by
  have hsq : 0 < 2*x^2 := by positivity
  dsimp [radicandInterval, escapeTime]
  rw [lt_div_iff₀ hsq]
  constructor <;> intro h <;> nlinarith

lemma positiveCurve_blowup (x : ℝ) (hx : 0 < x) :
    Tendsto (cubicCurve 1 x) (𝓝[<] (escapeTime x)) atTop := by
  have hsquare : x^2 ≠ 0 := pow_ne_zero 2 hx.ne'
  have he : 1-2*(1 : ℝ)*escapeTime x*x^2 = 0 := by
    dsimp [escapeTime]
    field_simp; ring
  have hc : Tendsto (fun t : ℝ => Real.sqrt (1-2*1*t*x^2))
      (𝓝[<] (escapeTime x)) (𝓝 0) := by
    have h : Continuous (fun t : ℝ => Real.sqrt (1-2*1*t*x^2)) :=
      Real.continuous_sqrt.comp (continuous_const.sub
        ((continuous_const.mul continuous_id).mul continuous_const))
    simpa only [he, Real.sqrt_zero] using
      (h.continuousAt (x := escapeTime x)).tendsto.mono_left nhdsWithin_le_nhds
  have hpos : ∀ᶠ t in 𝓝[<] (escapeTime x),
      Real.sqrt (1-2*1*t*x^2) ∈ Ioi (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact Real.sqrt_pos.mpr ((positive_radicand x t hx).mpr ht)
  have hi := (tendsto_nhdsWithin_iff.mpr ⟨hc,hpos⟩).inv_tendsto_nhdsGT_zero
  change Tendsto (fun t : ℝ => x * (Real.sqrt (1-2*1*t*x^2))⁻¹)
    (𝓝[<] (escapeTime x)) atTop
  exact hi.const_mul_atTop hx

lemma positive_flow_blowup (x : ℝ) (hx : 0 < x) :
    Tendsto (fun t => flow (cubicODE 1) t x) (𝓝[<] (escapeTime x)) atTop := by
  apply (positiveCurve_blowup x hx).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact ((cubic_canonical_cover 1 x).2 ((positive_radicand x t hx).mpr ht)).symm

lemma positive_interval (x : ℝ) (hx : 0 < x) :
    (flowInterval (cubicODE 1) x).carrier = Iio (escapeTime x) := by
  obtain ⟨hsol, h0, _, _, _, _, _⟩ := ODE.canonical_solution
    (autonomousToODEValue (cubicODE 1))
    ((cubicODE 1).locallyLipschitzInState_of_contDiffOn (cubic_smooth 1)) 0 x
    (show (0,x) ∈ (autonomousToODEValue (cubicODE 1)).domain from mem_univ _)
  have hnot : escapeTime x ∉ (flowInterval (cubicODE 1) x).carrier := by
    intro hT
    have hc : ContinuousAt (fun t => flow (cubicODE 1) t x) (escapeTime x) :=
      hsol.1.continuousOn.continuousAt ((flowInterval (cubicODE 1) x).isOpen.mem_nhds hT)
    exact not_tendsto_atTop_of_tendsto_nhds
      (hc.tendsto.mono_left nhdsWithin_le_nhds) (positive_flow_blowup x hx)
  apply Subset.antisymm
  · intro t ht
    by_contra hn
    apply hnot
    exact (flowInterval (cubicODE 1) x).ordConnected.out h0 ht
      ⟨by dsimp [escapeTime]; positivity, le_of_not_gt hn⟩
  · intro t ht
    exact (cubic_canonical_cover 1 x).1 ((positive_radicand x t hx).mpr ht)

/-- Blow-up obstructs continuation at exactly the stated finite maximal time. -/
theorem positive_escape : PositiveEscape := by
  intro x hx
  have hI := positive_interval x hx
  have hcan := ODE.canonical_solution (autonomousToODEValue (cubicODE 1))
    ((cubicODE 1).locallyLipschitzInState_of_contDiffOn (cubic_smooth 1)) 0 x
    (show (0,x) ∈ (autonomousToODEValue (cubicODE 1)).domain from mem_univ _)
  have he := hcan.2.2.2.2.1
  have hrep (t : ℝ) : t ∈ (flowInterval (cubicODE 1) x).carrier ↔
      lowerEndpointValue (autonomousToODEValue (cubicODE 1)) 0 x < (t : EReal) ∧
      (t : EReal) < upperEndpointValue (autonomousToODEValue (cubicODE 1)) 0 x := by
    change t ∈ (maximalDataValue (autonomousToODEValue (cubicODE 1)) 0 x).interval.carrier ↔ _
    rw [he.2.2]
    rfl
  have hT : (0 : EReal) < (escapeTime x : EReal) := by
    rw [← EReal.coe_zero, EReal.coe_lt_coe_iff]
    dsimp [escapeTime]
    positivity
  have hu : upperEndpointValue (autonomousToODEValue (cubicODE 1)) 0 x =
      (escapeTime x : EReal) := by
    apply le_antisymm
    · by_contra hn
      have hlt := lt_of_not_ge hn
      have hm : escapeTime x ∈ (flowInterval (cubicODE 1) x).carrier :=
        (hrep _).mpr ⟨he.1.trans hT, hlt⟩
      rw [hI] at hm
      exact lt_irrefl (escapeTime x) hm
    · by_contra hn
      obtain ⟨r, hr, hrT⟩ := EReal.exists_between_coe_real (lt_of_not_ge hn)
      have hm : r ∈ (flowInterval (cubicODE 1) x).carrier := by
        rw [hI]
        exact EReal.coe_lt_coe_iff.mp hrT
      exact (not_lt_of_gt hr) ((hrep r).mp hm).2
  exact ⟨hI, hu,
    fun t ht => (cubic_canonical_cover 1 x).2 ((positive_radicand x t hx).mpr ht),
    positive_flow_blowup x hx⟩

/-- Arbitrarily small positive data have finite forward lifespan, excluding stability. -/
theorem positive_instability : PositiveInstability := by
  intro hF hs
  obtain ⟨δ, hδ, hδsol⟩ := hs 1 zero_lt_one
  have hx : ‖δ/2‖ < δ := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have hcomplete := (hδsol (δ/2) (mem_univ _) hx).1
  have htime : 0 ≤ escapeTime (δ/2) := by dsimp [escapeTime]; positivity
  have hm := (hcomplete (escapeTime (δ/2)) htime).2
  rw [positive_interval (δ/2) (by positivity)] at hm
  exact lt_irrefl (escapeTime (δ/2)) hm

end D13Unified.Ch12.ZeroExample
