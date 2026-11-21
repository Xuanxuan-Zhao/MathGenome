import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch20.NonlinearGraphExample
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Ext

noncomputable section
open Set Filter Topology
namespace D13Unified.Ch20.NonlinearGraphExample
open Specs.D13Unified.Ch20.NonlinearGraphExample

def field : fieldType := fieldValue
def orbit : orbitType := orbitValue

lemma exp_two (t : ℝ) : Real.exp (2*t) = (Real.exp t)^2 := by
  rw [two_mul, Real.exp_add, pow_two]

lemma orbit_coefficient (p : ℝ × ℝ) (t : ℝ) :
    (orbitValue p t).1 - (orbitValue p t).2^2/3 =
      Real.exp (-t) * (p.1 - p.2^2/3) := by
  simp only [orbitValue, exp_two]
  ring

lemma orbit_y_integral (p : ℝ × ℝ) (t : ℝ) :
    (orbitValue p t).2 * Real.exp (-t) = p.2 := by
  simp only [orbitValue]
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

lemma orbit_x_integral (p : ℝ × ℝ) (t : ℝ) :
    ((orbitValue p t).1 - (orbitValue p t).2^2/3) * Real.exp t = p.1 - p.2^2/3 := by
  rw [orbit_coefficient]
  calc
    _ = (p.1 - p.2^2/3) * (Real.exp (-t) * Real.exp t) := by ring
    _ = _ := by rw [← Real.exp_add]; simp

theorem exact_solution : exactSolutionExpected := by
  intro p
  refine ⟨?_, ?_, ?_⟩
  · ext <;> simp [orbitValue]
  · unfold orbitValue
    fun_prop
  · intro t
    have hx := (((hasDerivAt_neg t).exp.mul_const (p.1 - p.2^2/3)).add
      (((hasDerivAt_id t).const_mul 2).exp.const_mul (p.2^2/3)))
    have hy := (Real.hasDerivAt_exp t).const_mul p.2
    convert hx.prodMk hy using 1
    · rfl
    · apply Prod.ext
      · simp [fieldValue, orbitValue, exp_two]; ring
      · rfl

lemma ode_eval (t : ℝ) (p : ℝ × ℝ) : odeValue.eval t p = fieldValue p := by
  simp [D13Unified.ODE.eval, odeValue]

/-- The two integrating factors identify every solution, without assuming
its uniqueness or using an extension of the vector field. -/
theorem all_solutions : allSolutionsExpected := by
  intro I z p h0 hp hz
  have hd (t : ℝ) (ht : t ∈ I.carrier) :
      HasDerivAt z (fieldValue (z t)) t := by
    simpa only [ode_eval] using hz.2.2 t ht
  have hdy (t : ℝ) (ht : t ∈ I.carrier) :
      HasDerivAt (fun r => (z r).2) (z t).2 t := by
    have hh := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hd t ht)
    exact hh
  have hdx (t : ℝ) (ht : t ∈ I.carrier) :
      HasDerivAt (fun r => (z r).1) (-(z t).1 + (z t).2^2) t :=
    (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have dy (t : ℝ) (ht : t ∈ I.carrier) :
      HasDerivAt (fun r => (z r).2 * Real.exp (-r)) 0 t := by
    convert ((hdy t ht).mul (hasDerivAt_neg t).exp) using 1
    simp
  have dx (t : ℝ) (ht : t ∈ I.carrier) :
      HasDerivAt (fun r => ((z r).1 - (z r).2^2/3) * Real.exp r) 0 t := by
    convert (((hdx t ht).sub (((hdy t ht).pow 2).div_const 3)).mul
      (Real.hasDerivAt_exp t)) using 1
    simp; ring
  have cy (t : ℝ) (ht : t ∈ I.carrier) : (z t).2 * Real.exp (-t) = p.2 := by
    have := I.isOpen.is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
      (fun t ht => (dy t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (dy t ht).deriv) ht h0
    simpa [hp] using this
  have cx (t : ℝ) (ht : t ∈ I.carrier) :
      ((z t).1 - (z t).2^2/3) * Real.exp t = p.1 - p.2^2/3 := by
    have := I.isOpen.is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
      (fun t ht => (dx t ht).differentiableAt.differentiableWithinAt)
      (fun t ht => (dx t ht).deriv) ht h0
    simpa [hp] using this
  intro t ht
  have hy : (z t).2 = (orbitValue p t).2 := by
    apply mul_right_cancel₀ (Real.exp_ne_zero (-t))
    rw [cy t ht, orbit_y_integral]
  have hc : (z t).1 - (z t).2^2/3 =
      (orbitValue p t).1 - (orbitValue p t).2^2/3 := by
    apply mul_right_cancel₀ (Real.exp_ne_zero t)
    rw [cx t ht, orbit_x_integral]
  exact Prod.ext (by rw [hy] at hc; linarith) hy

theorem global_ivp : globalIVPExpected := by
  intro p
  refine ⟨⟨(exact_solution p).2.1.contDiffOn, ?_, ?_⟩, mem_univ _, (exact_solution p).1⟩
  · intro t _; exact mem_univ _
  · intro t _; simpa only [ode_eval] using (exact_solution p).2.2 t

theorem stable_set : stableSetExpected := by
  ext p
  change Tendsto (orbitValue p) atTop (𝓝 0) ↔ p.2 = 0
  constructor
  · intro h
    change Tendsto (orbitValue p) atTop (𝓝 ((0:ℝ), (0:ℝ))) at h
    have hy : Tendsto (fun t => (orbitValue p t).2 * Real.exp (-t)) atTop (𝓝 (0:ℝ)) := by
      simpa using (continuous_snd.tendsto (0,0) |>.comp h).mul Real.tendsto_exp_neg_atTop_nhds_zero
    have he : (fun t => (orbitValue p t).2 * Real.exp (-t)) = fun _ => p.2 :=
      funext (orbit_y_integral p)
    rw [he] at hy
    exact tendsto_nhds_unique tendsto_const_nhds hy
  · intro hp
    have hx : Tendsto (fun t => Real.exp (-t) * p.1) atTop (𝓝 (0:ℝ)) := by
      simpa using Real.tendsto_exp_neg_atTop_nhds_zero.mul_const p.1
    convert hx.prodMk_nhds (tendsto_const_nhds (x := (0:ℝ))) using 1
    funext t; simp [orbitValue, hp]

theorem unstable_set : unstableSetExpected := by
  ext p
  change Tendsto (orbitValue p) atBot (𝓝 0) ↔ p.1 = p.2^2/3
  constructor
  · intro h
    change Tendsto (orbitValue p) atBot (𝓝 ((0:ℝ), (0:ℝ))) at h
    have hc : Tendsto (fun t =>
        ((orbitValue p t).1 - (orbitValue p t).2^2/3) * Real.exp t) atBot (𝓝 (0:ℝ)) := by
      have hx := (continuous_fst.tendsto (0,0)).comp h
      have hy := (continuous_snd.tendsto (0,0)).comp h
      simpa using (hx.sub ((hy.pow 2).div_const 3)).mul Real.tendsto_exp_atBot
    have he : (fun t => ((orbitValue p t).1 - (orbitValue p t).2^2/3) * Real.exp t) =
        fun _ => p.1 - p.2^2/3 := funext (orbit_x_integral p)
    rw [he] at hc
    have := tendsto_nhds_unique tendsto_const_nhds hc
    linarith
  · intro hp
    have hx : Tendsto (fun t => (p.2^2/3) * (Real.exp t)^2) atBot (𝓝 (0:ℝ)) := by
      simpa using (Real.tendsto_exp_atBot.pow 2).const_mul (p.2^2/3)
    have hy : Tendsto (fun t => p.2 * Real.exp t) atBot (𝓝 (0:ℝ)) := by
      simpa using Real.tendsto_exp_atBot.const_mul p.2
    convert hx.prodMk_nhds hy using 1
    funext t; simp [orbitValue, hp, exp_two]

theorem invariance : invarianceExpected := by
  refine ⟨?_, ?_, ?_⟩
  · intro p t hp; simp [orbitValue, hp]
  · intro p t hp
    have := orbit_coefficient p t
    rw [hp, sub_self, mul_zero] at this
    linarith
  · intro y t
    apply Prod.ext
    · simp [orbitValue, unstableParam, exp_two]; ring
    · rfl

theorem geometry : geometryExpected := by
  have hd (y : ℝ) : HasDerivAt unstableParam (2*y/3, 1) y := by
    convert (((hasDerivAt_id y).pow 2).div_const 3).prodMk (hasDerivAt_id y) using 1
    · rfl
    · ext <;> simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold unstableParam; fun_prop
  · simp [unstableParam]
  · simpa using hd 0
  · intro y
    refine ⟨hd y, ?_⟩
    apply Prod.ext
    · simp [fieldValue, unstableParam]; ring
    · simp [fieldValue, unstableParam]
  · intro he
    have hm : ((1/3:ℝ), (1:ℝ)) ∈ {p : ℝ × ℝ | p.1 = p.2^2/3} := by norm_num
    rw [he] at hm
    norm_num at hm

theorem linearization : linearizationExpected := by
  have hf := (ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := (0 : ℝ × ℝ))
  have hg := (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := (0 : ℝ × ℝ))
  have hd := (hf.neg.add (hg.pow 2)).prodMk hg
  intro v
  rw [show fderiv ℝ fieldValue 0 = _ from hd.fderiv]
  simp

end D13Unified.Ch20.NonlinearGraphExample
