import MathGenome.Internal.ODEDynamics.D13Unified.Ch05.PerturbationResidual
import MathGenome.Internal.ODEDynamics.D13Unified.Ch04.MaximalSolutionMap
import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch05.InitialValueBound
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

noncomputable section
open Set

namespace D13Unified.Ch05.InitialValueBound
open Specs.D13Unified.Ch05.InitialValueBound

/-- The full-domain scalar field x′ = Lx used to test the sharpness. -/
def linearODE : linearODEType := linearODEValue

/-- Its explicit solution with value ξ at time s. -/
def linearCurve : linearCurveType := linearCurveValue

/-- Restrict to the compact segment joining s to t and set the residual to zero. -/
theorem initial_value_bound : initialValueBoundExpected := by
  intro E _ _ _ F I x y s ξ η L hx hy hL hLip t ht
  have hsub : Icc (min s t) (max s t) ⊆ I.carrier :=
    I.ordConnected.uIcc_subset hx.2.1 ht
  have hxc : IsCompactSolutionOn F (min s t) (max s t) x :=
    ⟨min_le_max, hx.1.1.mono hsub, fun r hr => hx.1.2.1 r (hsub hr),
      fun r hr => (hx.1.2.2 r (hsub hr)).mono hsub⟩
  have hyc := hy.1.1.mono hsub
  have hv : ContinuousOn (fun r => F.eval r (y r)) (Icc (min s t) (max s t)) :=
    F.continuousOn_eval.comp (continuousOn_id.prodMk hyc)
      (fun r hr => hy.1.2.1 r (hsub hr))
  have h := PerturbationResidual.residual F (min s t) (max s t) s L 0 x y
    (fun r => F.eval r (y r)) hxc ⟨min_le_left _ _, le_max_left _ _⟩ hL le_rfl
    hyc hv (fun r hr => (hy.1.2.2 r (hsub hr)).mono hsub)
    (fun r hr => hy.1.2.1 r (hsub hr)) (fun r hr => hLip r (hsub hr))
    (by intro r hr; simp) t ⟨min_le_right _ _, le_max_right _ _⟩
  simpa only [zero_mul, add_zero, hx.2.2, hy.2.2] using h

/-- The canonical solution map satisfies the bound on every common interval. -/
theorem solutionValue_bound : solutionValueBoundExpected := by
  intro E _ _ _ F hF I s ξ η L hξ hη hs hIξ hIη hL hLip
  have hx := ODE.solutionValue_ivp F hF s ξ hξ
  have hy := ODE.solutionValue_ivp F hF s η hη
  have hx' := (classical_iff_solutionOn F _ _).mp hx.1
  have hy' := (classical_iff_solutionOn F _ _).mp hy.1
  apply initial_value_bound F I (fun t => F.solutionValue t s ξ)
    (fun t => F.solutionValue t s η) s ξ η L _ _ hL hLip
  · exact ⟨⟨hx'.1.mono hIξ, fun r hr => hx'.2.1 r (hIξ hr),
      fun r hr => (hx'.2.2 r (hIξ hr)).mono hIξ⟩, hs, hx.2.2⟩
  · exact ⟨⟨hy'.1.mono hIη, fun r hr => hy'.2.1 r (hIη hr),
      fun r hr => (hy'.2.2 r (hIη hr)).mono hIη⟩, hs, hy.2.2⟩

@[simp] lemma linearODE_eval (L t x : ℝ) : (linearODE L).eval t x = L * x := by
  simp [linearODE, linearODEValue, ODE.eval]

/-- Direct differentiation retains the equation and the original initial data. -/
theorem linear_solution : linearSolutionExpected := by
  intro L I s ξ hs
  have hd (t : ℝ) : HasDerivAt (linearCurve L s ξ)
      (L * linearCurve L s ξ t) t := by
    have h := (((hasDerivAt_id t).sub_const s).const_mul L).exp.const_mul ξ
    change HasDerivAt (fun r : ℝ => ξ * Real.exp (L * (r - s))) _ t
    convert h using 1 <;>
      simp only [linearCurve, linearCurveValue, id_eq, mul_one] <;> ring
  refine ⟨⟨fun t ht => (hd t).continuousAt.continuousWithinAt,
    fun t ht => mem_univ _, ?_⟩, hs, ?_⟩
  · intro t ht
    change HasDerivWithinAt (linearCurve L s ξ)
      ((linearODE L).eval t (linearCurve L s ξ t)) I.carrier t
    rw [linearODE_eval]
    exact (hd t).hasDerivWithinAt
  · simp [linearCurveValue]

/-- In one real dimension the Lipschitz estimate itself is an equality. -/
theorem linear_lipschitz : linearLipschitzExpected := by
  intro L hL t x y
  change ‖(linearODE L).eval t x - (linearODE L).eval t y‖ = _
  rw [linearODE_eval, linearODE_eval, ← mul_sub, norm_mul, Real.norm_eq_abs,
    abs_of_nonneg hL]

private lemma linear_locally_lipschitz (L : ℝ) :
    Specs.D13Unified.Ch03.LocalLipschitz.locallyLipschitzInStateValue (linearODE L) := by
  intro s ξ hs
  refine ⟨1, 1, |L|, zero_lt_one, zero_lt_one, abs_nonneg _, subset_univ _, ?_⟩
  intro t ht x hx y hy
  rw [linearODE_eval, linearODE_eval, ← mul_sub, norm_mul, Real.norm_eq_abs]

/-- The global curve forces the maximal interval to be all of real time. -/
theorem linear_solutionValue : linearSolutionValueExpected := by
  intro L s ξ
  let J : OpenTimeInterval := OpenTimeInterval.whole
  have hj := linear_solution L J.toTimeInterval s ξ (mem_univ _)
  have hjc : IsClassicalIVPOn (linearODE L) J (linearCurve L s ξ) s ξ :=
    ⟨(classical_iff_solutionOn _ _ _).mpr hj.1, hj.2⟩
  have hcanon := ODE.canonical_solution (linearODE L) (linear_locally_lipschitz L)
    s ξ (mem_univ _)
  have hrestrict := hcanon.2.2.2.2.2.1 J (linearCurve L s ξ) hjc
  have hall : (Specs.D13Unified.Ch04.MaximalSolutionMap.maximalIntervalValue
      (linearODE L) s ξ).carrier = univ :=
    Subset.antisymm (subset_univ _) hrestrict.1
  refine ⟨hall, fun t => ?_⟩
  have hval := ODE.solutionValue_on_domain (linearODE L) (linear_locally_lipschitz L)
    t s ξ ⟨mem_univ _, hall ▸ mem_univ t⟩
  exact hval.1.trans (hrestrict.2 (mem_univ t))

/-- The scalar example attains the estimate at every future time. -/
theorem sharpness : sharpnessExpected := by
  intro L hL s ξ η t hst
  rw [(linear_solutionValue L s ξ).2 t, (linear_solutionValue L s η).2 t]
  dsimp [linearCurveValue]
  rw [← sub_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  rw [abs_of_nonneg (sub_nonneg.mpr hst)]
  exact mul_comm _ _

/-- Any finite replacement constant is exceeded for fixed distinct initial data. -/
theorem no_uniform_constant : noUniformConstantExpected := by
  intro L hL s ξ η hne C
  let v : ℝ := (max C 0 + 1) / L
  have hv : 0 ≤ v := div_nonneg (by positivity) hL.le
  have hCv : C < Real.exp (L * v) := by
    have hLv : L * v = max C 0 + 1 := by dsimp [v]; field_simp
    rw [hLv]
    have h := Real.add_one_le_exp (max C 0 + 1)
    linarith [le_max_left C 0]
  refine ⟨s + v, le_add_of_nonneg_right hv, ?_⟩
  rw [sharpness L hL.le s ξ η (s + v) (le_add_of_nonneg_right hv),
    add_sub_cancel_left, abs_of_nonneg hv]
  exact mul_lt_mul_of_pos_right hCv (norm_pos_iff.mpr (sub_ne_zero.mpr hne))

end D13Unified.Ch05.InitialValueBound
