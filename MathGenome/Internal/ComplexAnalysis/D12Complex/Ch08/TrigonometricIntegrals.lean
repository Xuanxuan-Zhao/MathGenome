import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch08.TrigonometricIntegrals
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.ResidueCycle
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch08.ResidueComputation
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch03.PathOperations
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Poisson

noncomputable section
open Set Metric Filter
open scoped Topology BigOperators

namespace D12Complex.TrigonometricIntegrals

namespace Definitions

abbrev substitute : Specs.D12Complex.Ch08.TrigonometricIntegrals.substitute_type :=
  _root_.D12Complex.TrigonometricIntegrals.substitute

abbrev rationalize : Specs.D12Complex.Ch08.TrigonometricIntegrals.rationalize_type :=
  _root_.D12Complex.TrigonometricIntegrals.rationalize

abbrev value : Specs.D12Complex.Ch08.TrigonometricIntegrals.value_type :=
  _root_.D12Complex.TrigonometricIntegrals.value

abbrev angularValue : Specs.D12Complex.Ch08.TrigonometricIntegrals.angularValue_type :=
  _root_.D12Complex.TrigonometricIntegrals.angularValue

abbrev NoCirclePoles : Specs.D12Complex.Ch08.TrigonometricIntegrals.NoCirclePoles_type :=
  _root_.D12Complex.TrigonometricIntegrals.NoCirclePoles

abbrev transform : Specs.D12Complex.Ch08.TrigonometricIntegrals.transform_type :=
  _root_.D12Complex.TrigonometricIntegrals.transform

abbrev singularities : Specs.D12Complex.Ch08.TrigonometricIntegrals.singularities_type :=
  _root_.D12Complex.TrigonometricIntegrals.singularities

end Definitions

lemma circleMap_ne_zero (t : ℝ) : circleMap 0 1 t ≠ 0 := by
  simp [circleMap, Complex.exp_ne_zero]

lemma regular_of_dvd {r : RatFunc ℂ} {p : Polynomial ℂ} {z : ℂ}
    (hd : r.denom ∣ p) (hp : p.eval z ≠ 0) : r.denom.eval z ≠ 0 := by
  intro hz
  apply hp
  simpa only [Polynomial.eval₂_id] using
    Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero (RingHom.id ℂ) z hd
      (by simpa only [Polynomial.eval₂_id] using hz)

lemma regular_add {r s : RatFunc ℂ} {z : ℂ}
    (hr : r.denom.eval z ≠ 0) (hs : s.denom.eval z ≠ 0) :
    (r+s).denom.eval z ≠ 0 :=
  regular_of_dvd (RatFunc.denom_add_dvd r s) (by simpa using mul_ne_zero hr hs)

lemma regular_mul {r s : RatFunc ℂ} {z : ℂ}
    (hr : r.denom.eval z ≠ 0) (hs : s.denom.eval z ≠ 0) :
    (r*s).denom.eval z ≠ 0 :=
  regular_of_dvd (RatFunc.denom_mul_dvd r s) (by simpa using mul_ne_zero hr hs)

lemma regular_inv {r : RatFunc ℂ} {z : ℂ} (hr : value r z ≠ 0) :
    r⁻¹.denom.eval z ≠ 0 := by
  have hr0 : r ≠ 0 := by intro he; simp [he, value] at hr
  apply regular_of_dvd (RatFunc.denom_inv_dvd hr0)
  intro hn
  apply hr
  simp [value, RatFunc.eval, hn]

lemma value_inv {r : RatFunc ℂ} {z : ℂ}
    (hr : r.denom.eval z ≠ 0) (hv : value r z ≠ 0) :
    value r⁻¹ z = (value r z)⁻¹ := by
  have hr0 : r ≠ 0 := by intro he; simp [he, value] at hv
  have hi := regular_inv hv
  have he := RatFunc.eval_mul (RingHom.id ℂ) z (by simpa using hr) (by simpa using hi)
  rw [mul_inv_cancel₀ hr0, RatFunc.eval_one] at he
  change 1 = value r z * value r⁻¹ z at he
  apply (mul_left_cancel₀ hv)
  rw [← he, mul_inv_cancel₀ hv]
lemma value_add {r s : RatFunc ℂ} {z : ℂ}
    (hr : r.denom.eval z ≠ 0) (hs : s.denom.eval z ≠ 0) :
    value (r+s) z = value r z + value s z := by
  simpa only [value, Polynomial.eval₂_id] using RatFunc.eval_add (RingHom.id ℂ) z hr hs

lemma value_mul {r s : RatFunc ℂ} {z : ℂ}
    (hr : r.denom.eval z ≠ 0) (hs : s.denom.eval z ≠ 0) :
    value (r*s) z = value r z * value s z := by
  simpa only [value, Polynomial.eval₂_id] using RatFunc.eval_mul (RingHom.id ℂ) z hr hs

lemma regular_div {r s : RatFunc ℂ} {z : ℂ}
    (hr : r.denom.eval z ≠ 0) (hs : value s z ≠ 0) :
    (r/s).denom.eval z ≠ 0 := by
  rw [div_eq_mul_inv]
  exact regular_mul hr (regular_inv hs)

lemma value_div {r s : RatFunc ℂ} {z : ℂ}
    (hr : r.denom.eval z ≠ 0) (hs : s.denom.eval z ≠ 0) (hv : value s z ≠ 0) :
    value (r/s) z = value r z / value s z := by
  rw [div_eq_mul_inv, value_mul hr (regular_inv hv), value_inv hs hv, div_eq_mul_inv]

lemma eval₂_regular {σ : Type*} (p : MvPolynomial σ ℂ) (x : σ → RatFunc ℂ) (z : ℂ)
    (hx : ∀ i, (x i).denom.eval z ≠ 0) :
    (MvPolynomial.eval₂Hom RatFunc.C x p).denom.eval z ≠ 0 ∧
    value (MvPolynomial.eval₂Hom RatFunc.C x p) z =
      MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun i => value (x i) z) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [value]
  | add p q hp hq =>
    simp only [map_add]
    exact ⟨regular_add hp.1 hq.1, by rw [value_add hp.1 hq.1, hp.2, hq.2]⟩
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval₂Hom_X']
    exact ⟨regular_mul hp.1 (hx i), by rw [value_mul hp.1 (hx i), hp.2]⟩

lemma regular_neg {r : RatFunc ℂ} {z : ℂ} (hr : r.denom.eval z ≠ 0) :
    (-r).denom.eval z ≠ 0 := by
  have h := regular_mul (r := RatFunc.C (-1)) (z := z)
    (by rw [RatFunc.denom_C, Polynomial.eval_one]; exact one_ne_zero) hr
  rwa [map_neg, map_one, neg_one_mul] at h

lemma value_neg {r : RatFunc ℂ} {z : ℂ} (hr : r.denom.eval z ≠ 0) :
    value (-r) z = -value r z := by
  have h := value_mul (r := RatFunc.C (-1)) (z := z)
    (by rw [RatFunc.denom_C, Polynomial.eval_one]; exact one_ne_zero) hr
  rw [show RatFunc.C (-1) * r = -r by rw [map_neg, map_one, neg_one_mul],
    show value (RatFunc.C (-1)) z = -1 by simp only [value, RatFunc.eval_C, RingHom.id_apply],
    neg_one_mul] at h
  exact h

lemma substituted_coordinates (z : ℂ) (hz : z ≠ 0) (i : Fin 2) :
    (if i = 0 then (RatFunc.X + RatFunc.X⁻¹) / 2
      else (RatFunc.X - RatFunc.X⁻¹) / (2 * RatFunc.C Complex.I) : RatFunc ℂ).denom.eval z ≠ 0 ∧
    value (if i = 0 then (RatFunc.X + RatFunc.X⁻¹) / 2
      else (RatFunc.X - RatFunc.X⁻¹) / (2 * RatFunc.C Complex.I)) z =
      if i = 0 then (z+z⁻¹)/2 else (z-z⁻¹)/(2*Complex.I) := by
  have hX : (RatFunc.X : RatFunc ℂ).denom.eval z ≠ 0 := by simp
  have hXv : value RatFunc.X z = z := by simp [value]
  have hXi : (RatFunc.X⁻¹ : RatFunc ℂ).denom.eval z ≠ 0 :=
    regular_inv (by simpa only [hXv] using hz)
  have hXiv : value RatFunc.X⁻¹ z = z⁻¹ := by rw [value_inv hX (by simpa only [hXv] using hz), hXv]
  have h2 : (2 : RatFunc ℂ) = RatFunc.C 2 := (map_ofNat RatFunc.C 2).symm
  have hI2 : (2 * RatFunc.C Complex.I : RatFunc ℂ) = RatFunc.C (2*Complex.I) := by rw [map_mul, ← h2]
  by_cases hi : i = 0
  · simp only [hi, ite_true]
    rw [h2]
    refine ⟨regular_div (regular_add hX hXi) (by simp only [value, RatFunc.eval_C, RingHom.id_apply]; norm_num [Complex.I_ne_zero]), ?_⟩
    rw [value_div (regular_add hX hXi) (by rw [RatFunc.denom_C, Polynomial.eval_one]; exact one_ne_zero) (by simp only [value, RatFunc.eval_C, RingHom.id_apply]; norm_num [Complex.I_ne_zero]), value_add hX hXi,
      hXv, hXiv]
    simp only [value, RatFunc.eval_C, RingHom.id_apply]
  · simp only [hi, ite_false]
    rw [hI2, sub_eq_add_neg]
    refine ⟨regular_div (regular_add hX (regular_neg hXi)) (by simp only [value, RatFunc.eval_C, RingHom.id_apply]; norm_num [Complex.I_ne_zero]), ?_⟩
    rw [value_div (regular_add hX (regular_neg hXi)) (by rw [RatFunc.denom_C, Polynomial.eval_one]; exact one_ne_zero) (by simp only [value, RatFunc.eval_C, RingHom.id_apply]; norm_num [Complex.I_ne_zero]),
      value_add hX (regular_neg hXi), value_neg hXi, hXv, hXiv]
    simp only [value, RatFunc.eval_C, RingHom.id_apply, sub_eq_add_neg]

lemma circle_coordinates (t : ℝ) :
    ((circleMap 0 1 t + (circleMap 0 1 t)⁻¹)/2 = (Real.cos t : ℂ)) ∧
    ((circleMap 0 1 t - (circleMap 0 1 t)⁻¹)/(2*Complex.I) = (Real.sin t : ℂ)) := by
  have hi : (circleMap 0 1 t)⁻¹ = Complex.exp ((-t : ℝ)*Complex.I) := by
    simp [circleMap, Complex.exp_neg]
  have hexp : Complex.exp ((-t : ℝ)*Complex.I) =
      (Real.cos t : ℂ) - (Real.sin t : ℂ)*Complex.I := by
    rw [Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, sub_eq_add_neg, neg_mul]
  have hm : circleMap 0 1 t = (Real.cos t : ℂ) + (Real.sin t : ℂ)*Complex.I := by
    simp only [circleMap, zero_add, Complex.ofReal_one, one_mul, Complex.exp_ofReal_mul_I]
  rw [hi, hexp, hm]
  constructor <;> field_simp <;> ring

lemma substitute_value (p : MvPolynomial (Fin 2) ℂ) (t : ℝ) :
    (substitute p).denom.eval (circleMap 0 1 t) ≠ 0 ∧
    value (substitute p) (circleMap 0 1 t) =
      MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun i : Fin 2 => if i = 0 then (Real.cos t : ℂ) else (Real.sin t : ℂ)) p := by
  have hz : circleMap 0 1 t ≠ 0 := by simp [circleMap, Complex.exp_ne_zero]
  have hc := substituted_coordinates (circleMap 0 1 t) hz
  have hp := eval₂_regular p _ (circleMap 0 1 t) (fun i => (hc i).1)
  refine ⟨hp.1, hp.2.trans ?_⟩
  apply congrArg (fun f : Fin 2 → ℂ => MvPolynomial.eval₂Hom (RingHom.id ℂ) f p)
  funext i
  rw [(hc i).2]
  split_ifs <;> simp only [circle_coordinates t |>.1, circle_coordinates t |>.2]

lemma rationalize_value (p q : MvPolynomial (Fin 2) ℂ) (t : ℝ)
    (hq : MvPolynomial.eval₂Hom (RingHom.id ℂ)
      (fun i : Fin 2 => if i = 0 then (Real.cos t : ℂ) else (Real.sin t : ℂ)) q ≠ 0) :
    angularValue (rationalize p q) t =
      MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun i : Fin 2 => if i = 0 then (Real.cos t : ℂ) else (Real.sin t : ℂ)) p /
      MvPolynomial.eval₂Hom (RingHom.id ℂ)
        (fun i : Fin 2 => if i = 0 then (Real.cos t : ℂ) else (Real.sin t : ℂ)) q := by
  change value (substitute p / substitute q) (circleMap 0 1 t) = _
  rw [value_div (substitute_value p t).1 (substitute_value q t).1
    (by simpa only [(substitute_value q t).2] using hq),
    (substitute_value p t).2, (substitute_value q t).2]


/-- The real substitution identity needs no integrability premise: the two
parameter integrands agree at every point. -/
theorem circle_substitution :
    Specs.D12Complex.Ch08.TrigonometricIntegrals.circle_substitution_type := by
  intro r
  unfold circleIntegral
  apply intervalIntegral.integral_congr
  intro t _
  dsimp [angularValue, transform]
  rw [deriv_circleMap]
  have hz := circleMap_ne_zero t
  field_simp [hz, Complex.I_ne_zero]

lemma denominator_ne_zero_on_circle {r : RatFunc ℂ} (hr : NoCirclePoles r)
    {z : ℂ} (hz : ‖z‖ = 1) : r.denom.eval z ≠ 0 := by
  have hm : z ∈ sphere (0 : ℂ) 1 := by simpa [mem_sphere, dist_eq_norm] using hz
  rw [← show circleMap 0 1 '' Ioc 0 (2 * Real.pi) = sphere (0 : ℂ) 1 by
    simp] at hm
  obtain ⟨t, _, rfl⟩ := hm
  exact hr t

lemma value_differentiableAt (r : RatFunc ℂ) {z : ℂ}
    (hz : r.denom.eval z ≠ 0) : DifferentiableAt ℂ (value r) z := by
  unfold value RatFunc.eval
  simp only [Polynomial.eval₂_id]
  exact r.num.differentiableAt.div r.denom.differentiableAt hz

theorem transform_no_unit_circle_pole :
    Specs.D12Complex.Ch08.TrigonometricIntegrals.transform_no_unit_circle_pole_type := by
  intro r hr z hz
  apply (value_differentiableAt r (denominator_ne_zero_on_circle hr hz)).div
    (differentiableAt_const _ |>.mul differentiableAt_id)
  apply mul_ne_zero Complex.I_ne_zero
  change z ≠ 0
  intro he
  simp [he] at hz

lemma mem_singularities (r : RatFunc ℂ) (z : ℂ) :
    z ∈ singularities r ↔ z = 0 ∨ r.denom.eval z = 0 := by
  classical
  simp [singularities, Polynomial.mem_roots (RatFunc.denom_ne_zero r), Polynomial.IsRoot]

lemma transform_holomorphic (r : RatFunc ℂ) :
    HolomorphicOn ((singularities r : Set ℂ)ᶜ) (transform r) := by
  refine ⟨(singularities r).finite_toSet.isClosed.isOpen_compl, ?_⟩
  intro z hz
  have h : z ≠ 0 ∧ r.denom.eval z ≠ 0 := by
    simpa only [mem_compl_iff, Finset.mem_coe, mem_singularities, not_or] using hz
  exact (value_differentiableAt r h.2).div
    (differentiableAt_const _ |>.mul differentiableAt_id)
    (mul_ne_zero Complex.I_ne_zero h.1)

/-- The actual positive unit-circle cycle in the shared contour representation. -/
def unitCycle : IntegralCycle :=
  ⟨Finsupp.single (DiskCauchyFormula.circlePath 0 1) 1, by
    intro γ hγ
    have he : γ = DiskCauchyFormula.circlePath 0 1 := by
      simpa using hγ
    subst γ
    exact DiskCauchyFormula.circlePath_closed 0 1⟩

lemma unitCycle_trace : unitCycle.trace = sphere (0 : ℂ) 1 := by
  classical
  ext z
  simp only [unitCycle, IntegralCycle.trace, IntegralCycle.chain, IntegralChain.trace,
    Finsupp.support_single _ (by norm_num : (1 : ℤ) ≠ 0), Finset.mem_singleton,
    exists_eq_left]
  rw [DiskCauchyFormula.circlePath_trace 0 1 (by norm_num)]
  rfl

lemma unitCycle_integral (f : ℂ → ℂ) :
    unitCycle.integral f = (DiskCauchyFormula.circlePath 0 1).integral f := by
  simp [unitCycle, IntegralCycle.integral, IntegralCycle.chain, IntegralChain.integral]

lemma unitCycle_index (a : ℂ) : unitCycle.index a = if ‖a‖ < 1 then 1 else 0 := by
  classical
  by_cases hat : a ∈ unitCycle.trace
  · have hn : ‖a‖ = 1 := by simpa [unitCycle_trace, mem_sphere, dist_eq_norm] using hat
    change a ∈ unitCycle.chain.trace at hat
    simp [IntegralCycle.index, IntegralChain.index, hat, hn]
  · rw [unitCycle.index_eq_integral a hat, unitCycle_integral]
    by_cases ha : ‖a‖ < 1
    · rw [ite_eq_left ha]
      have hi := DiskCauchyFormula.circle_integral_sub_inv 0 a 1 (by norm_num)
        (by simpa using ha)
      simp only [one_div]
      rw [hi]
      exact inv_mul_cancel₀ (by
        exact mul_ne_zero (mul_ne_zero two_ne_zero
          (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
    · rw [ite_eq_right ha]
      have hn : ‖a‖ ≠ 1 := by
        intro he
        apply hat
        simpa [unitCycle_trace, mem_sphere, dist_eq_norm] using he
      have hext : 1 < ‖a‖ := lt_of_le_of_ne (le_of_not_gt ha) hn.symm
      have hc : ContinuousOn (fun z : ℂ => 1 / (z-a)) (sphere 0 1) := by
        apply continuousOn_const.div (continuousOn_id.sub continuousOn_const)
        intro z hz
        apply sub_ne_zero.mpr
        intro h
        change z = a at h
        subst z
        exact (ne_of_gt hext) (by simpa [mem_sphere, dist_eq_norm] using hz)
      rw [DiskCauchyFormula.integral_eq_circleIntegral 0 1 _ (by norm_num) hc]
      simp only [one_div]
      rw [Laurent.circleIntegral_sub_inv_of_exterior 0 a 1 (by norm_num)
        (by simpa using hext), mul_zero]

/-- The ordinary parameter integral exists under precisely the no-pole condition. -/
theorem angularValue_intervalIntegrable (r : RatFunc ℂ) (hr : NoCirclePoles r) :
    IntervalIntegrable (angularValue r) MeasureTheory.volume 0 (2*Real.pi) := by
  have hc : Continuous (angularValue r) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (value_differentiableAt r (hr t)).continuousAt.comp
      (continuous_circleMap 0 1).continuousAt
  exact hc.intervalIntegrable _ _

/-- The finite sum can omit every regular point: all its residues vanish. -/
theorem residue_transform_zero_off_singularities (r : RatFunc ℂ) (a : ℂ)
    (ha : a ∉ singularities r) : Residue.residue (transform r) a = 0 := by
  let U := (singularities r : Set ℂ)ᶜ
  have hf := transform_holomorphic r
  have hg : HolomorphicOn U (fun z => (z-a) * transform r z) :=
    ⟨hf.1, fun z hz => (differentiableAt_id.sub_const a).mul (hf.2 z hz)⟩
  have he := ResidueComputation.residue_pole_formula (transform r)
    (fun z => (z-a) * transform r z) a 1 U (by norm_num) ha hg
    (Filter.Eventually.of_forall (fun z => by simp))
  simpa using he

/-- An explicit rational representative of the transformed differential,
including all possible powers at zero. Polynomial reduction is unnecessary
for residues, which use punctured germs. -/
theorem transform_rational (r : RatFunc ℂ) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      transform r = fun z => P.eval z / Q.eval z := by
  refine ⟨r.num, (Polynomial.C Complex.I * Polynomial.X) * r.denom, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (by simp)
      Polynomial.X_ne_zero) (RatFunc.denom_ne_zero r)
  · funext z
    simp only [transform, value, RatFunc.eval, Polynomial.eval₂_id,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X, div_div]
    congr 1
    ring

theorem trigonometric_residue_formula :
    Specs.D12Complex.Ch08.TrigonometricIntegrals.trigonometric_residue_formula_type := by
  classical
  intro r hr
  have havoid : Disjoint unitCycle.trace (singularities r : Set ℂ) := by
    apply Set.disjoint_left.mpr
    intro z hz hs
    have hn : ‖z‖ = 1 := by simpa [unitCycle_trace, mem_sphere, dist_eq_norm] using hz
    rcases (mem_singularities r z).mp hs with he | he
    · simp [he] at hn
    · exact denominator_ne_zero_on_circle hr hn he
  have hf : HolomorphicOn (univ \ (singularities r : Set ℂ)) (transform r) := by
    simpa only [compl_eq_univ_sdiff] using transform_holomorphic r
  obtain ⟨s, hs, hi⟩ := ResidueCycle.residue_theorem univ (singularities r) (transform r)
    unitCycle isOpen_univ (subset_univ _)
    ((singularities r).finite_toSet.isClosed.preimage continuous_subtype_val)
    (singularities r).finite_toSet.isDiscrete hf (subset_univ _) havoid
    (fun w hw => (hw (mem_univ w)).elim)
  have heq : s = (singularities r).filter (fun a => ‖a‖ < 1) := by
    ext a
    rw [hs, Finset.mem_filter]
    simp only [unitCycle_index]
    split_ifs <;> simp_all
  rw [heq] at hi
  have hc : ContinuousOn (transform r) (sphere 0 1) := by
    intro z hz
    exact (transform_no_unit_circle_pole r hr z
      (by simpa [mem_sphere, dist_eq_norm] using hz)).continuousAt.continuousWithinAt
  rw [circle_substitution, ← DiskCauchyFormula.integral_eq_circleIntegral 0 1 _
    (by norm_num) hc, ← unitCycle_integral, hi]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [unitCycle_index, ite_eq_left (Finset.mem_filter.mp ha).2, one_mul]

theorem rational_expression_formula :
    Specs.D12Complex.Ch08.TrigonometricIntegrals.rational_expression_formula_type := by
  intro p q _ hr
  exact trigonometric_residue_formula (rationalize p q) hr

lemma poissonKernel_unit_real (q t : ℝ) :
    poissonKernel 0 (q : ℂ) (circleMap 0 1 t) =
      (1-q^2)/(1+q^2-2*q*Real.cos t) := by
  simp only [poissonKernel, sub_zero]
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq]
  simp [circleMap, Complex.exp_ofReal_mul_I, Complex.normSq_apply, -Complex.ofReal_cos, -Complex.ofReal_sin]
  congr 1 <;> nlinarith [Real.sin_sq_add_cos_sq t]

lemma poisson_integral (q : ℝ) (hq : |q| < 1) :
    (∫ t in (0:ℝ)..2*Real.pi, (1-q^2)/(1+q^2-2*q*Real.cos t)) = 2*Real.pi := by
  have hw : (q : ℂ) ∈ ball 0 1 := by simpa [mem_ball, Complex.norm_real] using hq
  have hp := (diffContOnCl_const : DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (ball 0 1)).circleAverage_poissonKernel_smul hw
  simp only [Real.circleAverage_def, Pi.smul_apply', Complex.real_smul, mul_one] at hp
  change (2*Real.pi)⁻¹ • (∫ t in (0:ℝ)..2*Real.pi,
    (poissonKernel 0 (q : ℂ) (circleMap 0 1 t) : ℂ)) = 1 at hp
  simp_rw [poissonKernel_unit_real] at hp
  rw [intervalIntegral.integral_ofReal] at hp
  rw [Complex.real_smul] at hp
  have he : (2*Real.pi)⁻¹ *
      (∫ t in (0:ℝ)..2*Real.pi, (1-q^2)/(1+q^2-2*q*Real.cos t)) = 1 := by
    exact_mod_cast hp
  have hm := congrArg (fun x : ℝ => (2*Real.pi)*x) he
  simpa only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt Real.two_pi_pos), one_mul, mul_one] using hm

theorem integral_inv_affine_cos :
    Specs.D12Complex.Ch08.TrigonometricIntegrals.integral_inv_affine_cos_type := by
  intro a b hab
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg b) hab
  have hsq : b^2 < a^2 := by
    simpa only [sq_abs] using (sq_lt_sq₀ (abs_nonneg b) ha.le).mpr hab
  let d := Real.sqrt (a^2-b^2)
  have hd : 0 < d := Real.sqrt_pos.mpr (by linarith)
  have hd2 : d^2 = a^2-b^2 := Real.sq_sqrt (by linarith)
  have had : 0 < a+d := by positivity
  let q := -b/(a+d)
  have hq : |q| < 1 := by
    dsimp [q]
    rw [abs_div, abs_neg, abs_of_pos had]
    apply (div_lt_one had).mpr
    linarith
  have hq2 : q^2 < 1 := by
    simpa only [sq_abs, one_pow] using (sq_lt_sq₀ (abs_nonneg q) (by norm_num : (0:ℝ) ≤ 1)).mpr hq
  have hrel1 : (1-q^2)*a = d*(1+q^2) := by
    dsimp [q]
    field_simp
    linear_combination -(a+d)*hd2
  have hrel2 : (1-q^2)*b = -2*d*q := by
    dsimp [q]
    field_simp
    linear_combination -b*hd2
  have hid (t : ℝ) : (1-q^2)/(1+q^2-2*q*Real.cos t) =
      d*(a+b*Real.cos t)⁻¹ := by
    have hpos : 0 < a+b*Real.cos t := by
      have hbound : |b*Real.cos t| ≤ |b| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg b) (Real.abs_cos_le_one t)
      linarith [neg_abs_le (b*Real.cos t)]
    have hidentity : (1-q^2)*(a+b*Real.cos t) =
        d*(1+q^2-2*q*Real.cos t) := by
      linear_combination hrel1 + Real.cos t * hrel2
    have hden : 1+q^2-2*q*Real.cos t ≠ 0 := by
      intro he
      rw [he, mul_zero] at hidentity
      exact (mul_ne_zero (ne_of_gt (by linarith : 0 < 1-q^2)) (ne_of_gt hpos)) hidentity
    rw [← one_div, mul_one_div]
    apply (div_eq_div_iff hden (ne_of_gt hpos)).mpr
    exact hidentity
  have hi := poisson_integral q hq
  simp_rw [hid] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  apply (eq_div_iff (ne_of_gt hd)).mpr
  nlinarith [hi]

end D12Complex.TrigonometricIntegrals
