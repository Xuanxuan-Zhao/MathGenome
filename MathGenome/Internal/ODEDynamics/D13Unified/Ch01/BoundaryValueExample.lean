import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch01.BoundaryValueExample
import MathGenome.Internal.ODEDynamics.D13Unified.Ch02.HarmonicOscillator

noncomputable section
open Set

namespace D13Unified.BoundaryValueExample
open HarmonicOscillator

private lemma family_eq_formula (A B : ℝ) :
    (fun t => A * Real.cos t + B * Real.sin t) = formula 1 0 A B := by
  funext t
  simp [formula]

theorem global_family :
    Specs.D13Unified.Ch01.BoundaryValueExample.globalFamilyExpected := by
  intro A B
  have h := (positive 1 (by norm_num) 0 A B).1
  simpa only [← family_eq_formula, one_pow, one_mul] using h

/-- Moving the initial time into the coefficients does not change the solution. -/
private lemma unshift_formula (s a b t : ℝ) :
    formula 1 s a b t =
      (a * Real.cos s - b * Real.sin s) * Real.cos t +
      (a * Real.sin s + b * Real.cos s) * Real.sin t := by
  simp only [formula, one_mul, div_one, Real.cos_sub, Real.sin_sub]
  ring

private lemma unshift_velocity (s a b t : ℝ) :
    deriv (formula 1 s a b) t =
      -(a * Real.cos s - b * Real.sin s) * Real.sin t +
      (a * Real.sin s + b * Real.cos s) * Real.cos t := by
  rw [formula_deriv 1 s a b (by norm_num)]
  simp only [one_mul, mul_one, Real.cos_sub, Real.sin_sub]
  ring

private lemma oscillator_of_eqOn (I : OpenTimeInterval) (y z : ℝ → ℝ)
    (hz : IsOscillatorOn 1 I z) (h : EqOn y z I.carrier) :
    IsOscillatorOn 1 I y := by
  refine ⟨hz.1.congr h, ?_⟩
  intro t ht
  have hd := (hz.2 t ht).congr_of_eventuallyEq
    ((h.deriv I.isOpen).eventuallyEq_of_mem (I.isOpen.mem_nhds ht))
  simpa only [h ht] using hd

theorem classification :
    Specs.D13Unified.Ch01.BoundaryValueExample.classificationExpected := by
  intro I y
  constructor
  · intro hy
    obtain ⟨s, hs⟩ := I.nonempty
    have he := (positive 1 (by norm_num) s (y s) (deriv y s)).2.2.2.1
      I y hs hy rfl rfl
    refine ⟨y s * Real.cos s - deriv y s * Real.sin s,
      y s * Real.sin s + deriv y s * Real.cos s, ?_⟩
    intro t ht
    exact (he ht).trans (unshift_formula s (y s) (deriv y s) t)
  · rintro ⟨A, B, h⟩
    apply oscillator_of_eqOn I y _ _ h
    exact ⟨(global_family A B).1.contDiffOn, fun t _ => by
      simpa only [one_pow, one_mul] using (global_family A B).2 t⟩

theorem homogeneous_boundary_iff :
    Specs.D13Unified.Ch01.BoundaryValueExample.homogeneousBoundaryExpected := by
  intro I y h0 hpi
  constructor
  · rintro ⟨hy, hy0, _⟩
    obtain ⟨A, B, h⟩ := (classification I y).mp hy
    have hA : A = 0 := by simpa [hy0] using (h h0).symm
    refine ⟨B, ?_⟩
    simpa only [hA, zero_mul, zero_add] using h
  · rintro ⟨B, h⟩
    refine ⟨(classification I y).mpr ⟨0, B, by simpa using h⟩, ?_, ?_⟩
    · simpa using h h0
    · simpa using h hpi

theorem incompatible_boundary :
    Specs.D13Unified.Ch01.BoundaryValueExample.incompatibleBoundaryExpected := by
  intro I y h0 hpi ⟨hy, hy0, hypi⟩
  obtain ⟨A, B, h⟩ := (classification I y).mp hy
  have hA : A = 0 := by simpa [hy0] using (h h0).symm
  have hp : y Real.pi = 0 := by simpa [hA] using h hpi
  exact zero_ne_one (hp.symm.trans hypi)

/-- The global position-velocity family is a shared solution on every interval. -/
private lemma interval_family (I : TimeInterval) (A B : ℝ) :
    IsSolutionOn (equation 1).toODE I
      (fun t => ![A * Real.cos t + B * Real.sin t,
        -A * Real.sin t + B * Real.cos t]) := by
  have hp (t : ℝ) : HasDerivAt (fun u => A * Real.cos u + B * Real.sin u)
      (-A * Real.sin t + B * Real.cos t) t := by
    convert ((Real.hasDerivAt_cos t).const_mul A).add
      ((Real.hasDerivAt_sin t).const_mul B) using 1
    ring
  have hv (t : ℝ) : HasDerivAt (fun u => -A * Real.sin u + B * Real.cos u)
      (-(A * Real.cos t + B * Real.sin t)) t := by
    convert ((Real.hasDerivAt_sin t).const_mul (-A)).add
      ((Real.hasDerivAt_cos t).const_mul B) using 1
    ring
  refine ⟨?_, fun _ _ => mem_univ _, ?_⟩
  · apply Continuous.continuousOn
    apply continuous_pi
    intro j
    fin_cases j
    · exact (continuous_const.mul Real.continuous_cos).add
        (continuous_const.mul Real.continuous_sin)
    · exact (continuous_const.mul Real.continuous_sin).add
        (continuous_const.mul Real.continuous_cos)
  · intro t ht
    rw [companion_eval]
    apply hasDerivWithinAt_pi.mpr
    intro j
    fin_cases j
    · simpa using (hp t).hasDerivWithinAt (s := I.carrier)
    · simpa using (hv t).hasDerivWithinAt (s := I.carrier)

theorem interval_classification :
    Specs.D13Unified.Ch01.BoundaryValueExample.intervalClassificationExpected := by
  intro I Y
  constructor
  · intro hY
    obtain ⟨s, hs⟩ := I.nonempty
    have hinit : Y s = ![Y s 0, Y s 1] := by
      funext j
      fin_cases j <;> rfl
    have he := interval_uniqueness.1 1 (by norm_num) s (Y s 0) (Y s 1) I Y hs hY hinit
    refine ⟨Y s 0 * Real.cos s - Y s 1 * Real.sin s,
      Y s 0 * Real.sin s + Y s 1 * Real.cos s, ?_⟩
    intro t ht
    rw [he t ht, unshift_formula, unshift_velocity]
  · rintro ⟨A, B, h⟩
    exact (solutionOn_congr (equation 1).toODE I Y _ h).mpr (interval_family I A B)

theorem interval_homogeneous_boundary_iff :
    Specs.D13Unified.Ch01.BoundaryValueExample.intervalHomogeneousBoundaryExpected := by
  intro I Y h0 hpi
  constructor
  · rintro ⟨hY, hY0, _⟩
    obtain ⟨A, B, h⟩ := (interval_classification I Y).mp hY
    have hA : A = 0 := by simpa [hY0] using (congrFun (h h0) 0).symm
    refine ⟨B, ?_⟩
    simpa only [hA, zero_mul, zero_add, neg_zero, add_zero] using h
  · rintro ⟨B, h⟩
    refine ⟨(interval_classification I Y).mpr ⟨0, B, by simpa using h⟩, ?_, ?_⟩
    · simpa using congrFun (h h0) 0
    · simpa using congrFun (h hpi) 0

theorem interval_incompatible_boundary :
    Specs.D13Unified.Ch01.BoundaryValueExample.intervalIncompatibleBoundaryExpected := by
  intro I Y h0 hpi ⟨hY, hY0, hYpi⟩
  obtain ⟨A, B, h⟩ := (interval_classification I Y).mp hY
  have hA : A = 0 := by simpa [hY0] using (congrFun (h h0) 0).symm
  have hp : Y Real.pi 0 = 0 := by simpa [hA] using congrFun (h hpi) 0
  exact zero_ne_one (hp.symm.trans hYpi)

end D13Unified.BoundaryValueExample
