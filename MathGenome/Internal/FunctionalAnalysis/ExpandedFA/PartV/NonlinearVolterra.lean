import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartV.NonlinearVolterra
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.VolterraFactorial
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartV.FractionalIntegrals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The nonlinear integral map is continuous in time and preserves the state
ball. Iterating its pointwise Lipschitz estimate gives `C^n*(t-a)^n/n!`.
A sufficiently high iterate is therefore contracting on the complete closed
function ball, even when `C*(b-a) ≥ 1`. Its fixed point is fixed by the
original map; the factorial estimate gives convergence from every curve.

For the weakly singular kernel, dominated convergence first proves time
continuity and the exact `B*h^α/α` bound proves invariance. If
`D(c) = ∫₀ʰ r^(α-1) exp(-c*r) dr`, then `D(c) → 0` as `c → ∞`.
Choose a nonnegative integer `c` with `q = L*D(c) < 1`. The pointwise
iterate estimate is `dist(T^n u(t),T^n v(t)) ≤ exp(c*t)*q^n*dist(u,v)`.
Thus a high iterate is contracting also in the ordinary supremum metric.
This proves existence, uniqueness, and uniform convergence without any
smallness restriction on the original interval or Lipschitz constant. -/

noncomputable section
namespace ExpandedFA.PartV
open Set MeasureTheory Filter Function
open scoped Topology

namespace NonlinearVolterra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {a b : ℝ} (hab : a ≤ b) {x₀ : E} {R : ℝ}
  (f : C(VolterraInterval a b, E))
  (G : C(volterraTriangle a b × Metric.closedBall x₀ R, E))

omit [NormedSpace ℝ E] in
lemma continuous_state (u : Ball a b x₀ R) :
    Continuous (state u) := u.val.continuous.subtype_mk _

omit [NormedSpace ℝ E] in
lemma continuous_integrand (u : Ball a b x₀ R) :
    Continuous (fun p : VolterraInterval a b × ℝ => integrand hab G u p.1 p.2) := by
  exact G.continuous.comp (continuous_volterraRetraction.prodMk
    ((continuous_state u).comp (continuous_projIcc.comp continuous_snd)))

omit [NormedSpace ℝ E] in
lemma intervalIntegrable_integrand (u : Ball a b x₀ R) (t : VolterraInterval a b) :
    IntervalIntegrable (integrand hab G u t) volume a (t : ℝ) :=
  ((continuous_integrand hab G u).comp
    (continuous_const.prodMk continuous_id : Continuous (fun s : ℝ => (t, s)))).intervalIntegrable _ _

lemma continuous_rhs (u : Ball a b x₀ R) : Continuous (rhs hab f G u) := by
  exact f.continuous.add
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (continuous_integrand hab G u) continuous_subtype_val)

omit [NormedSpace ℝ E] in
lemma integrand_restriction (u : Ball a b x₀ R) (t : VolterraInterval a b)
    (s : ℝ) (hs : s ∈ Icc a (t : ℝ)) :
    integrand hab G u t s =
      G (⟨((t : ℝ), s), hs.1, hs.2, t.property.2⟩,
        state u ⟨s, hs.1, hs.2.trans t.property.2⟩) := by
  unfold integrand
  have hr : volterraRetraction t s = ⟨((t : ℝ), s), hs.1, hs.2, t.property.2⟩ := by
    apply Subtype.ext
    simp [volterraRetraction, min_eq_right hs.2, max_eq_right hs.1]
  rw [hr, Set.projIcc_of_mem hab ⟨hs.1, hs.2.trans t.property.2⟩]

variable {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
  (hbound : ∀ p z, ‖G (p, z)‖ ≤ B)
  (hlip : ∀ p (z w : Metric.closedBall x₀ R),
    ‖G (p, z) - G (p, w)‖ ≤ C * ‖(z : E) - (w : E)‖)

include hbound in
lemma integral_bound (u : Ball a b x₀ R) (t : VolterraInterval a b) :
    ‖∫ s in a..(t : ℝ), integrand hab G u t s‖ ≤ ((t : ℝ) - a) * B := by
  have hb : ∀ s ∈ Set.uIoc a (t : ℝ), ‖integrand hab G u t s‖ ≤ B :=
    fun s _ => hbound _ _
  simpa only [abs_of_nonneg (sub_nonneg.mpr t.property.1), mul_comm B] using
    intervalIntegral.norm_integral_le_of_norm_le_const hb

variable (hinv : ‖f - ContinuousMap.const _ x₀‖ + (b - a) * B ≤ R)

/-- The continuous integral map preserves the closed supremum-norm ball. -/
def next (u : Ball a b x₀ R) : Ball a b x₀ R :=
  ⟨⟨rhs hab f G u, continuous_rhs hab f G u⟩, by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hR : 0 ≤ R := (add_nonneg (norm_nonneg _) (mul_nonneg (sub_nonneg.mpr hab) hB)).trans hinv
    apply (ContinuousMap.norm_le _ hR).mpr
    intro t
    change ‖(f t + ∫ s in a..(t : ℝ), integrand hab G u t s) - x₀‖ ≤ R
    rw [add_sub_right_comm]
    calc
      _ ≤ ‖f t - x₀‖ + ‖∫ s in a..(t : ℝ), integrand hab G u t s‖ := norm_add_le _ _
      _ ≤ ‖f - ContinuousMap.const _ x₀‖ + ((t : ℝ) - a) * B :=
        add_le_add ((f - ContinuousMap.const _ x₀).norm_coe_le_norm t)
          (integral_bound hab G hbound u t)
      _ ≤ ‖f - ContinuousMap.const _ x₀‖ + (b - a) * B := by
        gcongr; exact t.property.2
      _ ≤ R := hinv⟩

@[simp] lemma next_apply (u : Ball a b x₀ R) (t : VolterraInterval a b) :
    (next hab f G hB hbound hinv u).val t = rhs hab f G u t := rfl

lemma isFixedPt_next_iff (u : Ball a b x₀ R) :
    IsFixedPt (next hab f G hB hbound hinv) u ↔ IsSolution hab f G u := by
  constructor
  · intro hu t
    exact (congrArg (fun v : Ball a b x₀ R => v.val t) hu).symm
  · intro hu
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    exact (hu t).symm

include hC hlip in
/-- The nonlinear analogue of the simplex bound: two iterates have factorial
rather than geometric separation. No `C*(b-a)<1` assumption is involved. -/
lemma iterate_pointwise (u v : Ball a b x₀ R) (n : ℕ) (t : VolterraInterval a b) :
    dist ((((next hab f G hB hbound hinv)^[n]) u).val t)
         ((((next hab f G hB hbound hinv)^[n]) v).val t) ≤
      C ^ n * ((t : ℝ) - a) ^ n / (n.factorial : ℝ) * dist u v := by
  let T := next hab f G hB hbound hinv
  change dist (((T^[n]) u).val t) (((T^[n]) v).val t) ≤ _
  induction n generalizing t with
  | zero =>
    simpa only [iterate_zero_apply, pow_zero, Nat.factorial_zero, Nat.cast_one,
      div_one, one_mul, Subtype.dist_eq] using
        (ContinuousMap.dist_apply_le_dist (f := u.val) (g := v.val) t)
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm]
    change ‖(f t + ∫ s in a..(t : ℝ), integrand hab G ((T^[n]) u) t s) -
      (f t + ∫ s in a..(t : ℝ), integrand hab G ((T^[n]) v) t s)‖ ≤ _
    rw [add_sub_add_left_eq_sub, ← intervalIntegral.integral_sub
      (intervalIntegrable_integrand hab G ((T^[n]) u) t)
      (intervalIntegrable_integrand hab G ((T^[n]) v) t)]
    calc
      _ ≤ ∫ s in a..(t : ℝ),
          C * (C ^ n * (s - a) ^ n / (n.factorial : ℝ) * dist u v) := by
        apply intervalIntegral.norm_integral_le_of_norm_le t.property.1
        · apply Filter.Eventually.of_forall
          intro s hs
          rw [integrand_restriction hab G _ t s ⟨hs.1.le, hs.2⟩,
            integrand_restriction hab G _ t s ⟨hs.1.le, hs.2⟩]
          exact (hlip _ _ _).trans (mul_le_mul_of_nonneg_left
            (by simpa only [state, ← dist_eq_norm] using
              ih ⟨s, hs.1.le, hs.2.trans t.property.2⟩) hC)
        · exact (by fun_prop : Continuous (fun s : ℝ =>
            C * (C ^ n * (s - a) ^ n / (n.factorial : ℝ) * dist u v))).intervalIntegrable _ _
      _ = C ^ (n + 1) * ((t : ℝ) - a) ^ (n + 1) /
          ((n + 1).factorial : ℝ) * dist u v := by
        rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
          intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_sub_pow]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
          pow_succ, div_eq_mul_inv, mul_inv_rev]
        ring

include hC hlip in
lemma iterate_bound (u v : Ball a b x₀ R) (n : ℕ) :
    dist (((next hab f G hB hbound hinv)^[n]) u)
         (((next hab f G hB hbound hinv)^[n]) v) ≤
      (C * (b - a)) ^ n / (n.factorial : ℝ) * dist u v := by
  change dist ((((next hab f G hB hbound hinv)^[n]) u).val)
    ((((next hab f G hB hbound hinv)^[n]) v).val) ≤ _
  apply (ContinuousMap.dist_le (by positivity)).mpr
  intro t
  apply (iterate_pointwise hab f G hB hC hbound hlip hinv u v n t).trans
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hC _)
  exact pow_le_pow_left₀ (sub_nonneg.mpr t.property.1)
    (sub_le_sub_right t.property.2 a) n


include hC hlip in
lemma lipschitz_next :
    LipschitzWith ⟨(b - a) * C, mul_nonneg (sub_nonneg.mpr hab) hC⟩
      (next hab f G hB hbound hinv) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  change dist (next hab f G hB hbound hinv u) (next hab f G hB hbound hinv v) ≤
    ((b - a) * C) * dist u v
  simpa only [iterate_one, pow_one, Nat.factorial_one, Nat.cast_one, div_one,
    NNReal.coe_mk, mul_comm C] using
    iterate_bound hab f G hB hC hbound hlip hinv u v 1

variable [CompleteSpace E]

include hC hlip in
lemma solvesAndIterates_next (hR : 0 ≤ R) :
    SolvesAndIterates hab f G (next hab f G hB hbound hinv) := by
  let T := next hab f G hB hbound hinv
  let : Nonempty (Ball a b x₀ R) :=
    ⟨⟨ContinuousMap.const _ x₀, by simpa only [Metric.mem_closedBall, dist_self] using hR⟩⟩
  let : CompleteSpace (Ball a b x₀ R) := Metric.isClosed_closedBall.completeSpace_coe
  have hlim := FloorSemiring.tendsto_pow_div_factorial_atTop (C * (b - a))
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists
  let K : NNReal := ⟨(C * (b - a)) ^ n / (n.factorial : ℝ), by positivity⟩
  have hcontract : ContractingWith K (T^[n]) :=
    ⟨hn, LipschitzWith.of_dist_le_mul
      (fun u v => iterate_bound hab f G hB hC hbound hlip hinv u v n)⟩
  let u := hcontract.fixedPoint (T^[n])
  have hu : IsFixedPt T u := hcontract.isFixedPt_fixedPoint_iterate
  have hconv : ∀ v : Ball a b x₀ R,
      Tendsto (fun m => ((T^[m]) v).val) atTop (𝓝 u.val) := by
    intro v
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hz := hlim.mul_const (dist v u)
    simp only [zero_mul] at hz
    apply squeeze_zero (fun _ => dist_nonneg) _ hz
    intro m
    have hb := iterate_bound hab f G hB hC hbound hlip hinv v u m
    have hfix : (T^[m]) u = u := hu.iterate m
    rw [hfix] at hb
    exact hb
  refine ⟨fun _ _ => rfl, u,
    (isFixedPt_next_iff hab f G hB hbound hinv u).mp hu, ?_, hconv, ?_⟩
  · intro v hv
    have hv' := (isFixedPt_next_iff hab f G hB hbound hinv v).mpr hv
    exact hcontract.fixedPoint_unique (hv'.iterate n)
  · intro v
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp (hconv v)) ε hε] with m hm t
    rw [dist_comm]
    exact (ContinuousMap.dist_apply_le_dist t).trans_lt hm

end NonlinearVolterra

namespace NonlinearVolterra.WeaklySingular
open FractionalIntegrals
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {h : ℝ} (hh : 0 ≤ h) {x₀ : E} {R α B : ℝ} (hα : 0 < α)
  (f : C(VolterraInterval 0 h, E))
  (G : C(volterraTriangle 0 h × Metric.closedBall x₀ R, E))
  (hB : 0 ≤ B) (hbound : ∀ p z, ‖G (p,z)‖ ≤ B)

include hα hbound in
lemma integrable_integrand (u : Ball 0 h x₀ R) (t : VolterraInterval 0 h) :
    IntegrableOn (fun s => ((t : ℝ)-s) ^ (α-1) • integrand hh G u t s)
      (Ioc 0 (t : ℝ)) := by
  exact (reflected_power_integrable hα).smul_bdd B
    (((continuous_integrand hh G u).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall (fun s => hbound _ _))

include hα hbound in
lemma integral_bound (u : Ball 0 h x₀ R) (t : VolterraInterval 0 h) :
    ‖∫ s in Ioc 0 (t : ℝ), ((t : ℝ)-s) ^ (α-1) • integrand hh G u t s‖ ≤
      (t : ℝ) ^ α / α * B := by
  rw [← reflected_power_integral hα t.property.1, ← integral_mul_const]
  apply norm_integral_le_of_norm_le ((reflected_power_integrable hα).mul_const B)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)]
  exact mul_le_mul_of_nonneg_left (hbound _ _) (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)

include hα hB hbound in
/-- Moving the singularity to a fixed endpoint makes dominated convergence
applicable even when the state ball is noncompact. -/
lemma continuous_rhs (u : Ball 0 h x₀ R) : Continuous (rhs hh α f G u) := by
  let H : VolterraInterval 0 h → ℝ → E :=
    fun t r => integrand hh G u t ((t : ℝ)-r)
  have hH : Continuous (fun p : VolterraInterval 0 h × ℝ => H p.1 p.2) :=
    (continuous_integrand hh G u).comp
      (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_fst).sub continuous_snd))
  let F : VolterraInterval 0 h → ℝ → E := fun t r =>
    r ^ (α-1) • (if r ≤ (t : ℝ) then H t r else 0)
  have hm (t : VolterraInterval 0 h) : AEStronglyMeasurable (F t)
      (volume.restrict (Ioc 0 h)) := by
    exact (power_integrable (T := h) hα).aestronglyMeasurable.smul
      (StronglyMeasurable.ite (measurableSet_le measurable_id measurable_const)
        (hH.comp (continuous_const.prodMk continuous_id)).stronglyMeasurable
        stronglyMeasurable_const).aestronglyMeasurable
  have hb (t : VolterraInterval 0 h) : ∀ᵐ r ∂volume.restrict (Ioc 0 h),
      ‖F t r‖ ≤ r ^ (α-1) * B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    dsimp [F]
    rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg hr.1.le _)]
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hr.1.le _)
    split_ifs
    · exact hbound _ _
    · simpa using hB
  have hc : Continuous (fun t => ∫ r in Ioc 0 h, F t r) := by
    apply continuous_iff_continuousAt.mpr
    intro t₀
    apply continuousAt_of_dominated (Filter.Eventually.of_forall hm)
      (Filter.Eventually.of_forall hb) ((power_integrable hα).mul_const B)
    have hne : ∀ᵐ r ∂volume.restrict (Ioc 0 h), r ≠ (t₀ : ℝ) :=
      ae_restrict_of_ae (volume.ae_ne (t₀ : ℝ))
    filter_upwards [hne] with r hr
    have hec : ContinuousAt (fun t => r ^ (α-1) • H t r) t₀ :=
      continuousAt_const.smul ((hH.comp (continuous_id.prodMk continuous_const)).continuousAt)
    rcases lt_or_gt_of_ne hr with hrt | htr
    · apply hec.congr
      filter_upwards [continuous_subtype_val.continuousAt.eventually (eventually_gt_nhds hrt)]
        with t ht
      simp [F, ht.le]
    · apply (continuousAt_const (y := (0 : E))).congr
      filter_upwards [continuous_subtype_val.continuousAt.eventually (eventually_lt_nhds htr)]
        with t ht
      simp [F, not_le.mpr ht]
  have he (t : VolterraInterval 0 h) :
      (∫ s in Ioc 0 (t : ℝ), ((t : ℝ)-s) ^ (α-1) • integrand hh G u t s) =
        ∫ r in Ioc 0 h, F t r := by
    rw [← intervalIntegral.integral_of_le t.property.1]
    have hr := intervalIntegral.integral_comp_sub_left
      (fun r : ℝ => r ^ (α-1) • integrand hh G u t ((t : ℝ)-r))
      (a := (0 : ℝ)) (b := (t : ℝ)) (t : ℝ)
    simp only [sub_sub_cancel, sub_self, sub_zero] at hr
    rw [hr, intervalIntegral.integral_of_le t.property.1]
    have heF : F t = (Iic (t : ℝ)).indicator (fun r => r ^ (α-1) • H t r) := by
      ext r
      simp only [F, indicator_apply, mem_Iic]
      split_ifs <;> simp_all
    rw [heF, setIntegral_indicator measurableSet_Iic]
    have hi : Ioc (0 : ℝ) h ∩ Iic (t : ℝ) = Ioc 0 (t : ℝ) := by
      ext r
      simp only [mem_inter_iff, mem_Ioc, mem_Iic]
      constructor
      · rintro ⟨⟨hr, _⟩, hrt⟩; exact ⟨hr, hrt⟩
      · rintro ⟨hr, hrt⟩; exact ⟨⟨hr, hrt.trans t.property.2⟩, hrt⟩
    rw [hi]
  exact f.continuous.add (hc.congr (fun t => (he t).symm))

/-- The Laplace-discounted mass of the integrable power kernel. -/
def discountMass (α h c : ℝ) : ℝ :=
  ∫ r in Ioc 0 h, r ^ (α-1) * Real.exp (-c*r)

lemma discount_integrable {α h c : ℝ} (ha : 0 < α) (hc : 0 ≤ c) :
    IntegrableOn (fun r => r ^ (α-1) * Real.exp (-c*r)) (Ioc 0 h) := by
  apply (power_integrable ha).mul_bdd (c := 1) (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hc hr.1.le])

lemma discountMass_nonneg {α h c : ℝ} : 0 ≤ discountMass α h c := by
  apply setIntegral_nonneg measurableSet_Ioc
  intro r hr
  exact mul_nonneg (Real.rpow_nonneg hr.1.le _) (Real.exp_pos _).le

/-- Discounting an L1 kernel makes its mass arbitrarily small. -/
lemma discountMass_tendsto (α h : ℝ) (ha : 0 < α) :
    Tendsto (fun n : ℕ => discountMass α h n) atTop (𝓝 0) := by
  have hl := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict (Ioc 0 h)) (f := fun _ => (0 : ℝ)) (fun r : ℝ => r ^ (α-1))
    (fun n => (discount_integrable ha (Nat.cast_nonneg n)).aestronglyMeasurable)
    (power_integrable ha) ?_ ?_
  · simpa [discountMass] using hl
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg hr.1.le _) (Real.exp_pos _).le)]
    apply mul_le_of_le_one_right (Real.rpow_nonneg hr.1.le _)
    exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) n) hr.1.le])
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have ht : Tendsto (fun n : ℕ => (n : ℝ)*r) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const hr.1
    simpa only [Function.comp_apply, mul_zero, neg_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp ht).const_mul (r ^ (α-1))

/-- The scalar exponential convolution estimate, uniformly up to the endpoint. -/
lemma exponential_integral_bound {α h c t : ℝ} (ha : 0 < α) (hc : 0 ≤ c)
    (ht : t ∈ Icc (0 : ℝ) h) :
    (∫ s in Ioc 0 t, (t-s) ^ (α-1) * Real.exp (c*s)) ≤
      Real.exp (c*t) * discountMass α h c := by
  have he : (∫ s in Ioc 0 t, (t-s) ^ (α-1) * Real.exp (c*s)) =
      Real.exp (c*t) * discountMass α t c := by
    rw [← intervalIntegral.integral_of_le ht.1]
    have hr := intervalIntegral.integral_comp_sub_left
      (fun r : ℝ => r ^ (α-1) * Real.exp (c*(t-r))) (a := (0 : ℝ)) (b := t) t
    simp only [sub_sub_cancel, sub_self, sub_zero] at hr
    rw [hr, intervalIntegral.integral_of_le ht.1]
    simp only [discountMass, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r _
    dsimp only
    rw [show c*(t-r) = c*t + (-c*r) by ring, Real.exp_add]
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply setIntegral_mono_set (discount_integrable ha hc) _
    (Filter.Eventually.of_forall (fun r hr => ⟨hr.1, hr.2.trans ht.2⟩))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
  exact mul_nonneg (Real.rpow_nonneg hr.1.le _) (Real.exp_pos _).le

variable (hinv : ‖f - ContinuousMap.const _ x₀‖ + B * h ^ α / α ≤ R)

def next (u : Ball 0 h x₀ R) : Ball 0 h x₀ R :=
  ⟨⟨rhs hh α f G u, continuous_rhs hh hα f G hB hbound u⟩, by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hR : 0 ≤ R := (add_nonneg (norm_nonneg _)
      (div_nonneg (mul_nonneg hB (Real.rpow_nonneg hh _)) hα.le)).trans hinv
    apply (ContinuousMap.norm_le _ hR).mpr
    intro t
    change ‖(f t + ∫ s in Ioc 0 (t : ℝ),
      ((t : ℝ)-s) ^ (α-1) • integrand hh G u t s) - x₀‖ ≤ R
    rw [add_sub_right_comm]
    calc
      _ ≤ ‖f t - x₀‖ + ‖∫ s in Ioc 0 (t : ℝ),
          ((t : ℝ)-s) ^ (α-1) • integrand hh G u t s‖ := norm_add_le _ _
      _ ≤ ‖f - ContinuousMap.const _ x₀‖ + (t : ℝ) ^ α / α * B :=
        add_le_add ((f - ContinuousMap.const _ x₀).norm_coe_le_norm t)
          (integral_bound hh hα G hbound u t)
      _ ≤ ‖f - ContinuousMap.const _ x₀‖ + h ^ α / α * B := by
        gcongr; exact t.property.1; exact t.property.2
      _ ≤ R := by simpa only [mul_div_right_comm, mul_comm B] using hinv⟩

lemma isFixedPt_next_iff (u : Ball 0 h x₀ R) :
    IsFixedPt (next hh hα f G hB hbound hinv) u ↔ IsSolution hh α f G u := by
  constructor
  · intro hu t
    exact (congrArg (fun v : Ball 0 h x₀ R => v.val t) hu).symm
  · intro hu
    apply Subtype.ext
    apply ContinuousMap.ext
    intro t
    exact (hu t).symm

variable {L : ℝ} (hL : 0 ≤ L)
  (hlip : ∀ p (z w : Metric.closedBall x₀ R),
    ‖G (p,z) - G (p,w)‖ ≤ L * ‖(z : E) - (w : E)‖)

include hL hlip in
/-- Exponential weights give a geometric iterate bound for every integrable
power singularity. The discount parameter is chosen only in the proof. -/
lemma iterate_pointwise (c : ℝ) (hc : 0 ≤ c)
    (u v : Ball 0 h x₀ R) (n : ℕ) (t : VolterraInterval 0 h) :
    dist ((((next hh hα f G hB hbound hinv)^[n]) u).val t)
         ((((next hh hα f G hB hbound hinv)^[n]) v).val t) ≤
      Real.exp (c*(t : ℝ)) * (L * discountMass α h c) ^ n * dist u v := by
  let T := next hh hα f G hB hbound hinv
  let q := L * discountMass α h c
  have hq : 0 ≤ q := mul_nonneg hL discountMass_nonneg
  change dist (((T^[n]) u).val t) (((T^[n]) v).val t) ≤
    Real.exp (c*(t : ℝ)) * q ^ n * dist u v
  induction n generalizing t with
  | zero =>
    simp only [iterate_zero_apply, pow_zero, mul_one]
    exact (ContinuousMap.dist_apply_le_dist (f := u.val) (g := v.val) t).trans
      (le_mul_of_one_le_left dist_nonneg
        (Real.one_le_exp_iff.mpr (mul_nonneg hc t.property.1)))
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply', dist_eq_norm]
    change ‖(f t + ∫ s in Ioc 0 (t : ℝ),
      ((t : ℝ)-s) ^ (α-1) • integrand hh G ((T^[n]) u) t s) -
      (f t + ∫ s in Ioc 0 (t : ℝ),
      ((t : ℝ)-s) ^ (α-1) • integrand hh G ((T^[n]) v) t s)‖ ≤ _
    rw [add_sub_add_left_eq_sub, ← integral_sub
      (integrable_integrand hh hα G hbound ((T^[n]) u) t)
      (integrable_integrand hh hα G hbound ((T^[n]) v) t)]
    have hi : IntegrableOn (fun s : ℝ => ((t : ℝ)-s) ^ (α-1) * Real.exp (c*s))
        (Ioc 0 (t : ℝ)) := by
      apply (reflected_power_integrable hα).mul_bdd (c := Real.exp (c*(t : ℝ))) (by fun_prop)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hs.2 hc)
    calc
      _ ≤ ∫ s in Ioc 0 (t : ℝ),
          (((t : ℝ)-s) ^ (α-1) * Real.exp (c*s)) * (L * q ^ n * dist u v) := by
        apply norm_integral_le_of_norm_le (hi.mul_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        rw [← smul_sub, norm_smul,
          Real.norm_of_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)]
        have hs' : s ∈ Icc (0 : ℝ) (t : ℝ) := ⟨hs.1.le, hs.2⟩
        rw [integrand_restriction hh G _ t s hs', integrand_restriction hh G _ t s hs']
        let s' : VolterraInterval 0 h := ⟨s, hs.1.le, hs.2.trans t.property.2⟩
        let p : volterraTriangle 0 h := ⟨((t : ℝ), s), hs.1.le, hs.2, t.property.2⟩
        have he := (hlip p (state ((T^[n]) u) s') (state ((T^[n]) v) s')).trans
          (mul_le_mul_of_nonneg_left
            (by simpa only [state, ← dist_eq_norm] using ih s') hL)
        calc
          _ ≤ ((t : ℝ)-s) ^ (α-1) * (L * (Real.exp (c*s) * q ^ n * dist u v)) :=
            mul_le_mul_of_nonneg_left he (Real.rpow_nonneg (sub_nonneg.mpr hs.2) _)
          _ = _ := by ring
      _ = (∫ s in Ioc 0 (t : ℝ),
          ((t : ℝ)-s) ^ (α-1) * Real.exp (c*s)) * (L * q ^ n * dist u v) :=
        integral_mul_const _ _
      _ ≤ (Real.exp (c*(t : ℝ)) * discountMass α h c) * (L * q ^ n * dist u v) :=
        mul_le_mul_of_nonneg_right (exponential_integral_bound hα hc t.property)
          (mul_nonneg (mul_nonneg hL (pow_nonneg hq n)) dist_nonneg)
      _ = Real.exp (c*(t : ℝ)) * q ^ (n+1) * dist u v := by
        dsimp [q]
        rw [pow_succ]
        ring

include hL hlip in
lemma iterate_bound (c : ℝ) (hc : 0 ≤ c) (u v : Ball 0 h x₀ R) (n : ℕ) :
    dist (((next hh hα f G hB hbound hinv)^[n]) u)
         (((next hh hα f G hB hbound hinv)^[n]) v) ≤
      (Real.exp (c*h) * (L * discountMass α h c) ^ n) * dist u v := by
  change dist ((((next hh hα f G hB hbound hinv)^[n]) u).val)
    ((((next hh hα f G hB hbound hinv)^[n]) v).val) ≤ _
  have hq : 0 ≤ L * discountMass α h c := mul_nonneg hL discountMass_nonneg
  apply (ContinuousMap.dist_le (mul_nonneg
    (mul_nonneg (Real.exp_pos _).le (pow_nonneg hq n)) dist_nonneg)).mpr
  intro t
  apply (iterate_pointwise hh hα f G hB hbound hinv hL hlip c hc u v n t).trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (mul_nonneg hL discountMass_nonneg) n)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left t.property.2 hc)

variable [CompleteSpace E]

include hL hlip in
lemma solvesAndIterates_next (hR : 0 ≤ R) :
    SolvesAndIterates hh α f G (next hh hα f G hB hbound hinv) := by
  let T := next hh hα f G hB hbound hinv
  let : Nonempty (Ball 0 h x₀ R) :=
    ⟨⟨ContinuousMap.const _ x₀, by simpa only [Metric.mem_closedBall, dist_self] using hR⟩⟩
  let : CompleteSpace (Ball 0 h x₀ R) := Metric.isClosed_closedBall.completeSpace_coe
  have hm := (discountMass_tendsto α h hα).const_mul L
  simp only [mul_zero] at hm
  obtain ⟨c, hc⟩ := (hm.eventually (gt_mem_nhds zero_lt_one)).exists
  let q := L * discountMass α h (c : ℝ)
  have hq : 0 ≤ q := mul_nonneg hL discountMass_nonneg
  have hlim : Tendsto (fun n : ℕ => Real.exp ((c : ℝ)*h) * q ^ n) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq hc).const_mul (Real.exp ((c : ℝ)*h))
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds zero_lt_one)).exists
  let K : NNReal := ⟨Real.exp ((c : ℝ)*h) * q ^ n, by positivity⟩
  have hcontract : ContractingWith K (T^[n]) :=
    ⟨hn, LipschitzWith.of_dist_le_mul
      (fun u v => iterate_bound hh hα f G hB hbound hinv hL hlip
        c (Nat.cast_nonneg c) u v n)⟩
  let u := hcontract.fixedPoint (T^[n])
  have hu : IsFixedPt T u := hcontract.isFixedPt_fixedPoint_iterate
  have hconv : ∀ v : Ball 0 h x₀ R,
      Tendsto (fun m => ((T^[m]) v).val) atTop (𝓝 u.val) := by
    intro v
    apply tendsto_iff_dist_tendsto_zero.mpr
    have hz := hlim.mul_const (dist v u)
    simp only [zero_mul] at hz
    apply squeeze_zero (fun _ => dist_nonneg) _ hz
    intro m
    have hb := iterate_bound hh hα f G hB hbound hinv hL hlip
      c (Nat.cast_nonneg c) v u m
    have hfix : (T^[m]) u = u := hu.iterate m
    rw [hfix] at hb
    exact hb
  refine ⟨fun v t => ⟨integrable_integrand hh hα G hbound v t, rfl⟩,
    u, (isFixedPt_next_iff hh hα f G hB hbound hinv u).mp hu, ?_, hconv, ?_⟩
  · intro v hv
    have hv' := (isFixedPt_next_iff hh hα f G hB hbound hinv v).mpr hv
    exact hcontract.fixedPoint_unique (hv'.iterate n)
  · intro v
    apply Metric.tendstoUniformly_iff.mpr
    intro ε hε
    filter_upwards [(Metric.tendsto_nhds.mp (hconv v)) ε hε] with m hm t
    rw [dist_comm]
    exact (ContinuousMap.dist_apply_le_dist t).trans_lt hm

end NonlinearVolterra.WeaklySingular

/-- The full regular-kernel theorem with no smallness assumption. -/
theorem nonlinear_volterra : NonlinearVolterraSpec.InvariantBallTheorem := by
  intro 𝕜 E _ _ _ _ a b R hab hR x₀ f G B L hB hL hbound hlip hinv
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  exact ⟨NonlinearVolterra.next hab f G hB hbound hinv,
    NonlinearVolterra.lipschitz_next hab f G hB hL hbound hlip hinv,
    NonlinearVolterra.solvesAndIterates_next hab f G hB hL hbound hlip hinv hR⟩

/-- Weakly singular existence, uniqueness and Picard convergence on every
interval on which the source's closed-ball estimate holds. -/
theorem nonlinear_volterra_weakly_singular : NonlinearVolterraSpec.WeaklySingularTheorem := by
  intro 𝕜 E _ _ _ _ α h R hα hh hR x₀ f G B L hB hL hbound hlip hinv
  let := NormedSpace.restrictScalars ℝ 𝕜 E
  exact ⟨NonlinearVolterra.WeaklySingular.next hh hα f G hB hbound hinv,
    NonlinearVolterra.WeaklySingular.solvesAndIterates_next hh hα f G hB hbound hinv
      hL hlip hR⟩

end ExpandedFA.PartV
