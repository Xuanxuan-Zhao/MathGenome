import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch10.GreenOperator
import MathGenome.Internal.ODEDynamics.D13Unified.Ch10.GreenWeakInverse
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Ordered

noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set Filter
open scoped ENNReal ComplexConjugate BoundedContinuousFunction

namespace D13Unified.Ch10.GreenOperator
open GreenKernel
open RegularProblem hiding Problem interval
open GreenWeakInverse

/-- Equality of Hilbert outputs implies equality of the continuous integral
representatives on the entire closed interval, not only almost everywhere. -/
lemma representative_eqOn_of_operator_eq (P : Problem) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x ∈ interval P, 1 ≤ Q P c x)
    (f g : Hilbert P) (h : operator P c f = operator P c g) :
    EqOn (representative P c f) (representative P c g) (interval P) := by
  have hf := (inverse_weak P c hc hQ (f : ℝ → ℂ) (Lp.memLp f)).1
  have hg := (inverse_weak P c hc hQ (g : ℝ → ℂ) (Lp.memLp g)).1
  apply Measure.eqOn_Icc_of_ae_eq volume P.a_lt_b.ne _ hf.1.continuousOn hg.1.continuousOn
  exact (class_representative P c hc hQ f).2.symm.trans
    ((show (operator P c f : ℝ → ℂ) =ᵐ[baseMeasure P] operator P c g from
      h ▸ EventuallyEq.rfl).trans (class_representative P c hc hQ g).2)

/-- The weak differential equation recovers every L² forcing from its Green
output. No positivity assertion is used in this injectivity argument. -/
theorem injective : Specs.D13Unified.Ch10.GreenOperator.Injective := by
  intro P c hc hQ f g hfg
  have he := representative_eqOn_of_operator_eq P c hc hQ f g hfg
  have hd : EqOn (derivative P (representative P c f))
      (derivative P (representative P c g)) (interval P) := by
    intro x hx
    exact derivWithin_congr he (he hx)
  have hz : EqOn
      (fun t => (P.p t : ℂ) * derivative P (representative P c f) t)
      (fun t => (P.p t : ℂ) * derivative P (representative P c g) t)
      (interval P) := fun x hx => congrArg (fun z => (P.p x : ℂ) * z) (hd hx)
  have hf := weak_equation P c (f : ℝ → ℂ) (representative P c f)
    (inverse_weak P c hc hQ (f : ℝ → ℂ) (Lp.memLp f)).1
  have hg := weak_equation P c (g : ℝ → ℂ) (representative P c g)
    (inverse_weak P c hc hQ (g : ℝ → ℂ) (Lp.memLp g)).1
  apply (hilbert_equality P f g).mpr
  filter_upwards [hf, hg, ae_restrict_mem measurableSet_Icc] with x hfx hgx hx
  have hdz := derivWithin_congr hz (hz hx)
  change derivWithin _ (interval P) x = derivWithin _ (interval P) x at hdz
  have hw : (P.w x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (P.w_positive x hx).ne'
  apply mul_left_cancel₀ hw
  rw [← hfx, ← hgx]
  change -derivWithin _ (interval P) x + (Q P c x : ℂ) * representative P c f x =
    -derivWithin _ (interval P) x + (Q P c x : ℂ) * representative P c g x
  rw [he hx, hdz]

/-- Addition of the integrals, with the AE representatives of L² addition
handled explicitly. -/
lemma representative_add (P : Problem) (c : ℝ) (f g : Hilbert P) :
    EqOn (representative P c (f + g))
      (fun x => representative P c f x + representative P c g x) (interval P) := by
  intro x hx
  have hf := kernel_integrable P c (f : ℝ → ℂ) (Lp.memLp f) x hx
  have hg := kernel_integrable P c (g : ℝ → ℂ) (Lp.memLp g) x hx
  change (∫ t in P.a..P.b, (kernel P c x t : ℂ) * (f + g) t * (P.w t : ℂ)) = _
  calc
    _ = ∫ t in P.a..P.b, (kernel P c x t : ℂ) * (f t + g t) * (P.w t : ℂ) := by
      rw [intervalIntegral.integral_of_le P.a_lt_b.le,
        intervalIntegral.integral_of_le P.a_lt_b.le]
      apply integral_congr_ae
      have ha := (weighted_ae P _).mp (Lp.coeFn_add f g)
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self ha] with t ht
      rw [ht]; rfl
    _ = _ := by
      simp_rw [mul_add, add_mul]
      exact intervalIntegral.integral_add hf hg

lemma representative_smul (P : Problem) (c : ℝ) (z : ℂ) (f : Hilbert P) :
    EqOn (representative P c (z • f))
      (fun x => z * representative P c f x) (interval P) := by
  intro x hx
  change (∫ t in P.a..P.b, (kernel P c x t : ℂ) * (z • f) t * (P.w t : ℂ)) = _
  calc
    _ = ∫ t in P.a..P.b, (kernel P c x t : ℂ) * (z * f t) * (P.w t : ℂ) := by
      rw [intervalIntegral.integral_of_le P.a_lt_b.le,
        intervalIntegral.integral_of_le P.a_lt_b.le]
      apply integral_congr_ae
      have ha := (weighted_ae P _).mp (Lp.coeFn_smul z f)
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self ha] with t ht
      rw [ht]; rfl
    _ = _ := by
      simp_rw [show ∀ t, (kernel P c x t : ℂ) * (z * f t) * (P.w t : ℂ) =
        z * ((kernel P c x t : ℂ) * f t * (P.w t : ℂ)) by intro t; ring]
      exact intervalIntegral.integral_const_mul z _

theorem linearity : Specs.D13Unified.Ch10.GreenOperator.Linearity := by
  intro P c hc hQ
  constructor
  · intro f g
    apply (hilbert_equality P _ _).mpr
    have hr := representative_add P c f g
    have ha := (weighted_ae P _).mp (Lp.coeFn_add (operator P c f) (operator P c g))
    filter_upwards [(class_representative P c hc hQ (f + g)).2,
      (class_representative P c hc hQ f).2,
      (class_representative P c hc hQ g).2, ha,
      ae_restrict_mem measurableSet_Icc] with x hsum hf hg ha hx
    change (operator P c (f + g) : ℝ → ℂ) x =
      (operator P c f + operator P c g : Hilbert P) x
    calc
      _ = representative P c (f + g) x := hsum
      _ = representative P c f x + representative P c g x := hr hx
      _ = (operator P c f : ℝ → ℂ) x + (operator P c g : ℝ → ℂ) x :=
        congrArg₂ (· + ·) hf.symm hg.symm
      _ = _ := ha.symm
  · intro z f
    apply (hilbert_equality P _ _).mpr
    have hr := representative_smul P c z f
    have ha := (weighted_ae P _).mp (Lp.coeFn_smul z (operator P c f))
    filter_upwards [(class_representative P c hc hQ (z • f)).2,
      (class_representative P c hc hQ f).2, ha,
      ae_restrict_mem measurableSet_Icc] with x hsum hf ha hx
    change (operator P c (z • f) : ℝ → ℂ) x = (z • operator P c f : Hilbert P) x
    calc
      _ = representative P c (z • f) x := hsum
      _ = z * representative P c f x := hr hx
      _ = z * (operator P c f : ℝ → ℂ) x := congrArg (z * ·) hf.symm
      _ = _ := ha.symm

end D13Unified.Ch10.GreenOperator

namespace D13Unified.Ch10.GreenOperator
open GreenKernel
open RegularProblem hiding Problem interval
open GreenWeakInverse

/-- Complex-valued FTC with an explicitly supplied integrable AE derivative.
This uses absolute continuity, so no differentiability of an L² input is needed. -/
lemma integral_eq_sub_of_ac_ae {y g : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hy : AbsolutelyContinuousOnInterval y a b)
    (hg : IntervalIntegrable g volume a b)
    (hd : ∀ᵐ x ∂volume, x ∈ Icc a b → HasDerivAt y (g x) x) :
    (∫ x in a..b, g x) = y b - y a := by
  let z : ℝ → ℂ := fun x => ∫ t in a..x, g t
  have hz := complex_primitive_ac hg left_mem_uIcc
  have he : ∀ᵐ x ∂volume, x ∈ uIcc a b → HasDerivAt (y - z) 0 x := by
    filter_upwards [hd, hg.ae_hasDerivAt_integral] with x hdy hdz hx
    have hxI : x ∈ Icc a b := (uIcc_of_le hab) ▸ hx
    simpa only [sub_self] using (hdy hxI).sub (hdz hx a left_mem_uIcc)
  obtain ⟨C, hC⟩ := (hy.sub hz).const_of_ae_hasDerivAt_zero he
  have ha := hC a left_mem_uIcc
  have hb := hC b right_mem_uIcc
  change y a - z a = C at ha
  change y b - z b = C at hb
  have hza : z a = 0 := by simp [z]
  change z b = _
  rw [hza, sub_zero] at ha
  rw [← ha] at hb
  linear_combination -hb

/-- A Dirichlet weak solution satisfies the real energy formula. -/
lemma weak_energy (P : Problem) (c : ℝ) (f y : ℝ → ℂ)
    (hf : MemLp f 2 (weightedMeasure P)) (hy : IsWeakDirichletSolution P c f y) :
    (∫ x in P.a..P.b, y x * conj (f x) * (P.w x : ℂ)) =
      ((∫ x in P.a..P.b,
        P.p x * ‖derivative P y x‖ ^ 2 + Q P c x * ‖y x‖ ^ 2 : ℝ) : ℂ) := by
  let d := derivative P y
  let z : ℝ → ℂ := fun x => (P.p x : ℂ) * d x
  let e : ℝ → ℝ := fun x => P.p x * ‖d x‖ ^ 2 + Q P c x * ‖y x‖ ^ 2
  let F : ℝ → ℂ := fun x => y x * conj (f x) * (P.w x : ℂ)
  have ud := uniqueDiffOn_Icc P.a_lt_b
  have hyd : ∀ x ∈ interval P, HasDerivWithinAt y (d x) (interval P) x :=
    fun x hx => (hy.1.differentiableOn (by norm_num) x hx).hasDerivWithinAt
  have hdc : ContinuousOn d (interval P) :=
    hy.1.continuousOn_derivWithin ud (by norm_num)
  have hyc := hy.1.continuousOn
  have hec : ContinuousOn e (interval P) :=
    (P.p_regular.continuousOn.mul (hdc.norm.pow 2)).add
      ((continuousOn_Q P c).mul (hyc.norm.pow 2))
  have hEI : IntervalIntegrable (fun x => (e x : ℂ)) volume P.a P.b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le P.a_lt_b.le]
    exact Complex.continuous_ofReal.comp_continuousOn hec
  have hFI : IntervalIntegrable F volume P.a P.b := by
    have hFc := IntegrableOn.continuousOn_mul hyc
      (show Integrable (fun x => conj (f x * (P.w x : ℂ))) (baseMeasure P) from
        Complex.conjCLE.toContinuousLinearMap.integrable_comp (weighted_l1 P f hf).2) isCompact_Icc
    have hFF : IntegrableOn F (interval P) := by
      apply hFc.congr
      exact Eventually.of_forall fun x => by simp [F, map_mul, mul_assoc]
    exact ⟨hFF.mono_set Ioc_subset_Icc_self,
      by simp [Ioc_eq_empty (not_lt.mpr P.a_lt_b.le)]⟩
  have hyac : AbsolutelyContinuousOnInterval y P.a P.b := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    rw [uIcc_of_le P.a_lt_b.le]
    exact hy.1
  have hzac : AbsolutelyContinuousOnInterval (fun x => conj (z x)) P.a P.b :=
    Complex.isometry_conj.lipschitzWith.comp_absolutelyContinuousOnInterval hy.2.1
  have hprod : AbsolutelyContinuousOnInterval (fun x => y x * conj (z x)) P.a P.b :=
    hyac.smul hzac
  have hAE : ∀ᵐ x ∂volume, x ∈ interval P →
      HasDerivAt (fun t => y t * conj (z t)) ((e x : ℂ) - F x) x := by
    have hzder := (ae_restrict_iff' measurableSet_Icc).mp hy.2.2.2.2
    filter_upwards [hzder, ae_interior P.a P.b] with x hz hi hx
    have hyder := (hyd x hx).hasDerivAt (Icc_mem_nhds (hi hx).1 (hi hx).2)
    have hzd : HasDerivAt z ((Q P c x : ℂ) * y x - (P.w x : ℂ) * f x) x := hz hx
    have hh : HasDerivAt (fun t => y t * conj (z t))
        (d x * conj (z x) + y x * conj ((Q P c x : ℂ) * y x - (P.w x : ℂ) * f x)) x :=
      hyder.mul hzd.star
    convert hh using 1
    dsimp [e, F, z]
    simp only [map_sub, map_mul, Complex.conj_ofReal]
    rw [show d x * ((P.p x : ℂ) * conj (d x)) +
        y x * ((Q P c x : ℂ) * conj (y x) - (P.w x : ℂ) * conj (f x)) =
        (P.p x : ℂ) * (d x * conj (d x)) +
        (Q P c x : ℂ) * (y x * conj (y x)) - y x * conj (f x) * (P.w x : ℂ) by ring]
    simp only [Complex.mul_conj', Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
  have hFTC := integral_eq_sub_of_ac_ae P.a_lt_b.le hprod (hEI.sub hFI) hAE
  have hboundary : y P.b * conj (z P.b) - y P.a * conj (z P.a) = 0 := by
    rw [hy.2.2.1, hy.2.2.2.1]; ring
  rw [hboundary, intervalIntegral.integral_sub hEI hFI] at hFTC
  have heq := sub_eq_zero.mp hFTC
  change (∫ x in P.a..P.b, F x) = _
  rw [← heq, intervalIntegral.integral_ofReal]

theorem energy_identity : Specs.D13Unified.Ch10.GreenOperator.EnergyIdentity := by
  intro P c hc hQ f
  have hy := (inverse_weak P c hc hQ (f : ℝ → ℂ) (Lp.memLp f)).1
  have he := weak_energy P c (f : ℝ → ℂ) (representative P c f) (Lp.memLp f) hy
  calc
    _ = ∫ x in P.a..P.b, representative P c f x * conj (f x) * (P.w x : ℂ) := by
      change paperInner P (operator P c f) f = _
      rw [inner_intervalIntegral P]
      rw [intervalIntegral.integral_of_le P.a_lt_b.le,
        intervalIntegral.integral_of_le P.a_lt_b.le]
      apply integral_congr_ae
      have ha := (class_representative P c hc hQ f).2
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self ha] with x hx
      exact congrArg (fun z : ℂ => z * conj (f x) * (P.w x : ℂ)) hx
    _ = _ := he

end D13Unified.Ch10.GreenOperator

namespace D13Unified.Ch10.GreenOperator
open GreenKernel
open RegularProblem hiding Problem interval
open GreenWeakInverse

/-- The integral operator with its proved complex linear structure. -/
def linearOperator (P : Problem) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x ∈ interval P, 1 ≤ Q P c x) : Hilbert P →ₗ[ℂ] Hilbert P where
  toFun := operator P c
  map_add' := (linearity P c hc hQ).1
  map_smul' := (linearity P c hc hQ).2

lemma linearOperator_symmetric (P : Problem) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x ∈ interval P, 1 ≤ Q P c x) :
    (linearOperator P c hc hQ).IsSymmetric := by
  apply (LinearMap.isSymmetric_iff_inner_map_self_real _).mpr
  intro f
  have he := energy_identity P c hc hQ f
  change inner ℂ f (operator P c f) = _ at he
  have hh := congrArg (conj : ℂ → ℂ) he
  simp only [inner_conj_symm, Complex.conj_ofReal] at hh
  change conj (inner ℂ (operator P c f) f) = inner ℂ (operator P c f) f
  rw [hh, Complex.conj_ofReal]

theorem selfAdjoint : Specs.D13Unified.Ch10.GreenOperator.SelfAdjoint := by
  intro P c hc hQ f g
  exact (linearOperator_symmetric P c hc hQ g f).symm

/-- Hellinger–Toeplitz applies because the symmetric complex linear map is
defined on all of the complete weighted L² space. -/
theorem boundedLinear : Specs.D13Unified.Ch10.GreenOperator.BoundedLinear := by
  intro P c hc hQ
  exact ⟨⟨linearOperator P c hc hQ, (linearOperator_symmetric P c hc hQ).continuous⟩,
    fun _ => rfl⟩

theorem strictlyPositive : Specs.D13Unified.Ch10.GreenOperator.StrictlyPositive := by
  intro P c hc hQ f hf
  let y := representative P c f
  let d := derivative P y
  let e : ℝ → ℝ := fun x => P.p x * ‖d x‖ ^ 2 + Q P c x * ‖y x‖ ^ 2
  have hy := (inverse_weak P c hc hQ (f : ℝ → ℂ) (Lp.memLp f)).1
  have hyc : ContinuousOn y (interval P) := hy.1.continuousOn
  have hdc : ContinuousOn d (interval P) :=
    hy.1.continuousOn_derivWithin (uniqueDiffOn_Icc P.a_lt_b) (by norm_num)
  have hec : ContinuousOn e (interval P) :=
    (P.p_regular.continuousOn.mul (hdc.norm.pow 2)).add
      ((continuousOn_Q P c).mul (hyc.norm.pow 2))
  have hnonneg : ∀ x ∈ interval P, 0 ≤ e x := by
    intro x hx
    exact add_nonneg (mul_nonneg (P.p_positive x hx).le (sq_nonneg _))
      (mul_nonneg (le_trans zero_le_one (hQ x hx)) (sq_nonneg _))
  have hK : operator P c f ≠ 0 := by
    intro hh
    apply hf
    apply injective P c hc hQ
    exact hh.trans (linearOperator P c hc hQ).map_zero.symm
  have hm := (class_representative P c hc hQ f).1
  have hop : operator P c f = toHilbert P y hm := by
    unfold operator Specs.D13Unified.Ch10.GreenWeakInverse.operatorValue
    rw [dite_eq_left hm]
  obtain ⟨x, hx, hyx⟩ := (continuous_nonzero P y hyc hm).mp (hop ▸ hK)
  have hpos : 0 < e x := by
    apply add_pos_of_nonneg_of_pos
    · exact mul_nonneg (P.p_positive x hx).le (sq_nonneg _)
    · exact mul_pos (lt_of_lt_of_le zero_lt_one (hQ x hx))
        (sq_pos_of_pos (norm_pos_iff.mpr hyx))
  have hI : 0 < ∫ x in P.a..P.b, e x :=
    intervalIntegral.integral_pos P.a_lt_b hec
      (fun x hx => hnonneg x (Ioc_subset_Icc_self hx)) ⟨x, hx, hpos⟩
  have he := energy_identity P c hc hQ f
  change paperInner P (operator P c f) f = ((∫ x in P.a..P.b, e x : ℝ) : ℂ) at he
  change 0 < (paperInner P (operator P c f) f).re ∧
    (paperInner P (operator P c f) f).im = 0
  rw [he]
  exact ⟨hI, rfl⟩

end D13Unified.Ch10.GreenOperator

namespace D13Unified.Ch10.GreenOperator
open GreenKernel
open RegularProblem hiding Problem interval
open GreenWeakInverse

local instance weightedFinite (P : Problem) : IsFiniteMeasure (weightedMeasure P) :=
  weightedMeasure_finite P

abbrev ClosedInterval (P : Problem) := Icc P.a P.b

/-- Clamping to [a,b] is used only to represent a continuous interval
function on the ambient real line before passing to the L² quotient. -/
def intervalProjection (P : Problem) : C(ℝ, ClosedInterval P) :=
  ⟨projIcc P.a P.b P.a_lt_b.le, continuous_projIcc⟩

def uniformToHilbert (P : Problem) (v : ClosedInterval P →ᵇ ℂ) : Hilbert P :=
  BoundedContinuousFunction.toLp 2 (weightedMeasure P) ℂ (v.compContinuous (intervalProjection P))

lemma uniformToHilbert_continuous (P : Problem) : Continuous (uniformToHilbert P) :=
  (BoundedContinuousFunction.toLp 2 (weightedMeasure P) ℂ).continuous.comp
    (BoundedContinuousFunction.continuous_compContinuous (intervalProjection P))

lemma uniformToHilbert_ae (P : Problem) (v : ClosedInterval P →ᵇ ℂ) :
    (uniformToHilbert P v : ℝ → ℂ) =ᵐ[baseMeasure P]
      fun x => v (projIcc P.a P.b P.a_lt_b.le x) :=
  (weighted_ae P _).mp (BoundedContinuousFunction.coeFn_toLp 2 (weightedMeasure P) ℂ _)

/-- The actual continuous kernel on the compact square. -/
def continuousKernel (P : Problem) (c : ℝ) :
    C(ClosedInterval P × ClosedInterval P, ℂ) :=
  ⟨fun z => (kernel P c z.1 z.2 : ℂ),
    Complex.continuous_ofReal.comp
      ((kernel_continuity P c).comp_continuous
        (continuous_subtype_val.comp continuous_fst |>.prodMk
          (continuous_subtype_val.comp continuous_snd))
        (fun z => ⟨z.1.property, z.2.property⟩))⟩

def kernelSection (P : Problem) (c : ℝ) (x : ClosedInterval P) : ClosedInterval P →ᵇ ℂ :=
  ContinuousMap.equivBoundedOfCompact _ _ ((continuousKernel P c).curry x)

lemma kernelSection_continuous (P : Problem) (c : ℝ) : Continuous (kernelSection P c) :=
  (ContinuousMap.linearIsometryBoundedOfCompact (ClosedInterval P) ℂ ℂ).continuous.comp
    (continuousKernel P c).curry.continuous

/-- Kernel slices in the same weighted Hilbert space as the forcing. -/
def hilbertKernel (P : Problem) (c : ℝ) (x : ClosedInterval P) : Hilbert P :=
  uniformToHilbert P (kernelSection P c x)

lemma hilbertKernel_continuous (P : Problem) (c : ℝ) : Continuous (hilbertKernel P c) :=
  (uniformToHilbert_continuous P).comp (kernelSection_continuous P c)

lemma hilbertKernel_ae (P : Problem) (c : ℝ) (x : ClosedInterval P) :
    (hilbertKernel P c x : ℝ → ℂ) =ᵐ[baseMeasure P] fun t => (kernel P c x t : ℂ) := by
  filter_upwards [uniformToHilbert_ae P (kernelSection P c x),
    ae_restrict_mem measurableSet_Icc] with t ht hti
  change (uniformToHilbert P (kernelSection P c x) : ℝ → ℂ) t = _
  rw [ht]
  change (kernel P c x (projIcc P.a P.b P.a_lt_b.le t) : ℂ) = _
  rw [projIcc_of_mem P.a_lt_b.le hti]

/-- Evaluation of the integral is the Hilbert pairing with its kernel slice.
This is the Cauchy–Schwarz bridge for the unit-ball equicontinuity estimate. -/
lemma representative_inner (P : Problem) (c : ℝ) (f : Hilbert P) (x : ClosedInterval P) :
    representative P c f x = paperInner P f (hilbertKernel P c x) := by
  rw [inner_intervalIntegral P]
  change (∫ t in P.a..P.b, (kernel P c x t : ℂ) * f t * (P.w t : ℂ)) = _
  rw [intervalIntegral.integral_of_le P.a_lt_b.le,
    intervalIntegral.integral_of_le P.a_lt_b.le]
  apply integral_congr_ae
  have ha := hilbertKernel_ae P c x
  filter_upwards [ae_restrict_of_ae_restrict_of_subset Ioc_subset_Icc_self ha] with t ht
  rw [ht, Complex.conj_ofReal]
  ring

/-- Cauchy–Schwarz gives the actual kernel-slice estimate, uniformly for
all inputs in the Hilbert unit ball. -/
lemma representative_difference_bound (P : Problem) (c : ℝ) (f : Hilbert P)
    (x y : ClosedInterval P) :
    ‖representative P c f x - representative P c f y‖ ≤
      ‖hilbertKernel P c x - hilbertKernel P c y‖ * ‖f‖ := by
  rw [representative_inner P c f x, representative_inner P c f y]
  change ‖inner ℂ (hilbertKernel P c x) f - inner ℂ (hilbertKernel P c y) f‖ ≤ _
  rw [← inner_sub_left]
  exact norm_inner_le_norm _ _

/-- The Green outputs as bounded continuous functions on the actual interval. -/
def uniformOperator (P : Problem) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x ∈ interval P, 1 ≤ Q P c x) (f : Hilbert P) :
    ClosedInterval P →ᵇ ℂ :=
  ContinuousMap.equivBoundedOfCompact _ _
    (⟨fun x : ClosedInterval P => representative P c f x,
      continuousOn_iff_continuous_domRestrict.mp
        (inverse_weak P c hc hQ (f : ℝ → ℂ) (Lp.memLp f)).1.1.continuousOn⟩ :
      C(ClosedInterval P, ℂ))

lemma uniformOperator_factorization (P : Problem) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x ∈ interval P, 1 ≤ Q P c x) (f : Hilbert P) :
    uniformToHilbert P (uniformOperator P c hc hQ f) = operator P c f := by
  apply (hilbert_equality P _ _).mpr
  filter_upwards [uniformToHilbert_ae P (uniformOperator P c hc hQ f),
    (class_representative P c hc hQ f).2, ae_restrict_mem measurableSet_Icc]
      with x hx hy hxi
  rw [hx, hy]
  change representative P c f (projIcc P.a P.b P.a_lt_b.le x) = representative P c f x
  rw [projIcc_of_mem P.a_lt_b.le hxi]

end D13Unified.Ch10.GreenOperator

namespace D13Unified.Ch10.GreenOperator
open GreenKernel
open RegularProblem hiding Problem interval
open GreenWeakInverse

/-- Arzelà–Ascoli on the actual Hilbert unit ball: continuity of the
kernel slices supplies equicontinuity, and Cauchy–Schwarz supplies the
common bound. This is compactness for the uniform norm on [a,b]. -/
lemma uniformOperator_compact (P : Problem) (c : ℝ)
    (hc : 0 < c) (hQ : ∀ x ∈ interval P, 1 ≤ Q P c x) :
    IsCompact (closure (uniformOperator P c hc hQ '' Metric.closedBall 0 1)) := by
  let A := uniformOperator P c hc hQ '' Metric.closedBall 0 1
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn
    (hilbertKernel_continuous P c).continuousOn
  have hbound : ∀ (v : ClosedInterval P →ᵇ ℂ) (x : ClosedInterval P), v ∈ A →
      v x ∈ Metric.closedBall (0 : ℂ) M := by
    rintro v x ⟨f, hf, rfl⟩
    have hfn : ‖f‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hf
    rw [Metric.mem_closedBall, dist_zero_right]
    change ‖representative P c f x‖ ≤ M
    rw [representative_inner P c f x]
    exact (norm_inner_le_norm (hilbertKernel P c x) f).trans
      ((mul_le_of_le_one_right (norm_nonneg _) hfn).trans (hM x (mem_univ x)))
  have hequi : Equicontinuous ((↑) : A → ClosedInterval P → ℂ) := by
    intro x
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hd⟩ := Metric.continuousAt_iff.mp
      (hilbertKernel_continuous P c).continuousAt ε hε
    refine ⟨δ, hδ, fun y hy v => ?_⟩
    obtain ⟨f, hf, hfv⟩ := v.property
    have hfn : ‖f‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hf
    change dist (v.val x) (v.val y) < ε
    rw [← hfv]
    rw [dist_eq_norm]
    change ‖representative P c f x - representative P c f y‖ < ε
    apply lt_of_le_of_lt (representative_difference_bound P c f x y)
    apply lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hfn)
    simpa only [dist_eq_norm, norm_sub_rev] using hd hy
  exact BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : ℂ) M) (isCompact_closedBall _ _) A hbound hequi

/-- Uniform convergence embeds continuously into weighted L². The compact
set supplied by Arzelà–Ascoli therefore contains the Hilbert image of the
unit ball, proving compactness of the original quotient operator. -/
theorem compact : Specs.D13Unified.Ch10.GreenOperator.Compact := by
  intro P c hc hQ
  apply (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).mpr
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ zero_lt_one,
    uniformToHilbert P '' closure (uniformOperator P c hc hQ '' Metric.closedBall 0 1),
    (uniformOperator_compact P c hc hQ).image (uniformToHilbert_continuous P), ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  exact ⟨uniformOperator P c hc hQ f, subset_closure ⟨f, hf, rfl⟩,
    uniformOperator_factorization P c hc hQ f⟩

end D13Unified.Ch10.GreenOperator
