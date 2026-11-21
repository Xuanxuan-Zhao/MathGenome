import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.ElementaryOrderOperations
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch17.OrderDivisorDefinitions
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch04.Liouville
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

noncomputable section
open Filter Set
open scoped Topology ENNReal
namespace D12Complex.ElementaryOrderOperations
open OrderDivisorDefinitions

lemma entire_continuous {f : ℂ → ℂ} (hf : HolomorphicOn Set.univ f) : Continuous f :=
  continuous_iff_continuousAt.mpr (fun z => (hf.2 z (mem_univ z)).continuousAt)

lemma norm_le_maximumModulus {f : ℂ → ℂ} (hf : HolomorphicOn Set.univ f)
    {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ maximumModulus f r := by
  have hd : Differentiable ℂ f := fun z => hf.2 z (mem_univ z)
  obtain ⟨w, hw, _, hmax⟩ := maximumModulus_attained f hd.continuous r hr
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (Metric.isBounded_ball (x := (0 : ℂ)) (r := r))
    hd.diffContOnCl (fun v hv => hmax v (by simpa [frontier_ball (0 : ℂ) (ne_of_gt hr)] using hv))
  simpa [closure_ball (0 : ℂ) (ne_of_gt hr)] using hz

theorem maximumModulus_tendsto_atTop :
    Specs.D12Complex.Ch17.ElementaryOrderOperations.maximumModulus_tendsto_atTop_type := by
  intro f hf hnc
  apply tendsto_atTop.2
  intro B
  have hunbounded : ∃ z, B < ‖f z‖ := by
    by_contra! h
    exact hnc (Liouville.bounded_entire_constant f (max 0 B) hf (le_max_left _ _)
      (fun z => (h z).trans (le_max_right _ _)))
  obtain ⟨z, hz⟩ := hunbounded
  filter_upwards [eventually_ge_atTop (max 1 ‖z‖)] with r hr
  exact hz.le.trans (norm_le_maximumModulus hf
    (lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hr)) ((le_max_right _ _).trans hr))

theorem translated_maxima_tendsto :
    Specs.D12Complex.Ch17.ElementaryOrderOperations.translated_maxima_tendsto_type := by
  intro f a hf hnc
  refine ⟨maximumModulus_tendsto_atTop f hf hnc,
    maximumModulus_tendsto_atTop (fun z => f z - a)
      ⟨isOpen_univ, fun z _ => (hf.2 z (mem_univ z)).sub_const a⟩ ?_⟩
  rintro ⟨c, hc⟩
  exact hnc ⟨c + a, fun z => sub_eq_iff_eq_add.mp (hc z)⟩

/-- Triangle inequality for actual attained circle maxima. -/
lemma maximumModulus_sub_le (f : ℂ → ℂ) (hf : Continuous f) (a : ℂ)
    (r : ℝ) (hr : 0 < r) :
    maximumModulus (fun z => f z - a) r ≤ maximumModulus f r + ‖a‖ := by
  obtain ⟨z, hz, heq, _⟩ := maximumModulus_attained (fun z => f z - a)
    (hf.sub continuous_const) r hr
  obtain ⟨w, hw, _, hmax⟩ := maximumModulus_attained f hf r hr
  change ‖f z - a‖ = maximumModulus (fun z => f z - a) r at heq
  rw [← heq]
  have h := hmax z hz
  change ‖f z‖ ≤ maximumModulus f r at h
  have := norm_sub_le (f z) a
  linarith

/-- A fixed additive error in maximum modulus disappears in log-log order.
The clipping at e makes this estimate valid even without divergence. -/
lemma growthQuotient_le_of_maximum_le_add (f g : ℂ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    {r : ℝ} (hr : 1 < r) (hfg : maximumModulus f r ≤ maximumModulus g r + C) :
    growthQuotient f r ≤ growthQuotient g r +
      Real.log (1 + Real.log (1 + C)) / Real.log r := by
  let G := max (Real.exp 1) (maximumModulus g r)
  let F := max (Real.exp 1) (maximumModulus f r)
  have he : 1 ≤ Real.exp 1 := (Real.one_lt_exp_iff.mpr zero_lt_one).le
  have hG : 1 ≤ G := he.trans (le_max_left _ _)
  have hF : 0 < F := (Real.exp_pos 1).trans_le (le_max_left _ _)
  have hC1 : 0 < 1 + C := by linarith
  have hlogC : 0 ≤ Real.log (1 + C) := Real.log_nonneg (by linarith)
  have hlogG : 1 ≤ Real.log G := by
    simpa [G] using Real.log_le_log (Real.exp_pos 1) (le_max_left (Real.exp 1) (maximumModulus g r))
  have hFG : F ≤ (1 + C) * G := by
    apply max_le
    · exact (le_max_left _ _).trans (le_mul_of_one_le_left (by linarith : 0 ≤ G) (by linarith))
    · calc
        maximumModulus f r ≤ maximumModulus g r + C := hfg
        _ ≤ G + C := by gcongr; exact le_max_right _ _
        _ ≤ (1 + C) * G := by nlinarith
  have hl : Real.log F ≤ (1 + Real.log (1 + C)) * Real.log G := by
    calc
      _ ≤ Real.log ((1 + C) * G) := Real.log_le_log hF hFG
      _ = Real.log (1 + C) + Real.log G := Real.log_mul hC1.ne' (by linarith)
      _ ≤ _ := by nlinarith
  have hll : Real.log (Real.log F) ≤
      Real.log (1 + Real.log (1 + C)) + Real.log (Real.log G) := by
    calc
      _ ≤ Real.log ((1 + Real.log (1 + C)) * Real.log G) :=
        Real.log_le_log (by
          have := Real.log_le_log (Real.exp_pos 1)
            (le_max_left (Real.exp 1) (maximumModulus f r))
          rw [Real.log_exp] at this
          linarith) hl
      _ = _ := Real.log_mul (by linarith) (by linarith)
  change Real.log (Real.log F) / Real.log r ≤ Real.log (Real.log G) / Real.log r + _
  rw [← add_div]
  exact div_le_div_of_nonneg_right (hll.trans_eq (add_comm _ _)) (Real.log_pos hr).le

lemma order_le_of_maximum_le_add (f g : NonzeroEntireFunction) (C : ℝ) (hC : 0 ≤ C)
    (hfg : ∀ r > 0, maximumModulus f.toFun r ≤ maximumModulus g.toFun r + C) :
    order f ≤ order g := by
  have hlim : Tendsto (fun r : ℝ =>
      ENNReal.ofReal (Real.log (1 + Real.log (1 + C)) / Real.log r)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal
      (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop :
        Tendsto (fun r : ℝ => Real.log (1 + Real.log (1 + C)) / Real.log r) atTop (𝓝 0))
  change limsup (fun r => ENNReal.ofReal (growthQuotient f.toFun r)) atTop ≤
    limsup (fun r => ENNReal.ofReal (growthQuotient g.toFun r)) atTop
  rw [← ENNReal.limsup_add_of_right_tendsto_zero hlim
    (fun r => ENNReal.ofReal (growthQuotient g.toFun r))]
  apply limsup_le_limsup (hu := by isBoundedDefault) (hv := by isBoundedDefault)
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  exact (ENNReal.ofReal_le_ofReal (growthQuotient_le_of_maximum_le_add f.toFun g.toFun C hC hr
    (hfg r (zero_lt_one.trans hr)))).trans ENNReal.ofReal_add_le

theorem order_sub_const :
    Specs.D12Complex.Ch17.ElementaryOrderOperations.order_sub_const_type := by
  intro f g a _ heq
  apply le_antisymm
  · apply order_le_of_maximum_le_add g f ‖a‖ (norm_nonneg a)
    intro r hr
    rw [heq]
    exact maximumModulus_sub_le f.toFun (entire_continuous f.holomorphic) a r hr
  · apply order_le_of_maximum_le_add f g ‖a‖ (norm_nonneg a)
    intro r hr
    have hf : f.toFun = (fun z => g.toFun z - (-a)) := by
      funext z
      rw [heq]
      simp
    rw [hf, ← norm_neg a]
    exact maximumModulus_sub_le g.toFun (entire_continuous g.holomorphic) (-a) r hr

theorem translated_order :
    Specs.D12Complex.Ch17.ElementaryOrderOperations.translated_order_type := by
  intro f a hnc
  have hnz : ∃ z, f.toFun z - a ≠ 0 := by
    by_contra! h
    exact hnc ⟨a, fun z => sub_eq_zero.mp (h z)⟩
  let g : NonzeroEntireFunction := ⟨(fun z => f.toFun z - a),
    ⟨isOpen_univ, fun z _ => (f.holomorphic.2 z (mem_univ z)).sub_const a⟩, hnz⟩
  exact ⟨g, rfl, order_sub_const f g a hnc rfl⟩

theorem polynomial_exp_exists :
    Specs.D12Complex.Ch17.ElementaryOrderOperations.polynomial_exp_exists_type := by
  intro A Q hA
  obtain ⟨g, hg⟩ := polynomial_function_exists A hA
  obtain ⟨z, hz⟩ := g.nonzero
  refine ⟨⟨(fun z => A.eval z * Complex.exp (Q.eval z)),
    ⟨isOpen_univ, fun z _ => A.differentiableAt.mul (Complex.differentiable_exp.differentiableAt.comp z Q.differentiableAt)⟩,
    ⟨z, mul_ne_zero ?_ (Complex.exp_ne_zero _)⟩⟩, rfl⟩
  simpa [hg] using hz

lemma polynomial_circle_bound (P : Polynomial ℂ) (C : ℝ)
    (hb : ∀ r : ℝ, 1 ≤ r → max (Real.exp 1) (maximumModulus P.eval r) ≤ C * r ^ P.natDegree)
    {r : ℝ} (hr : 1 ≤ r) {z : ℂ} (hz : ‖z‖ = r) :
    ‖P.eval z‖ ≤ C * r ^ P.natDegree := by
  exact (norm_le_maximumModulus ⟨isOpen_univ, fun _ _ => P.differentiableAt⟩
    (zero_lt_one.trans_le hr) hz.le).trans ((le_max_right _ _).trans (hb r hr))

theorem polynomial_exp_upper :
    Specs.D12Complex.Ch17.ElementaryOrderOperations.polynomial_exp_upper_type := by
  intro A Q _ hn
  obtain ⟨CA, hCA, hAb⟩ := polynomial_bound A
  obtain ⟨CQ, hCQ, hQb⟩ := polynomial_bound Q
  have hCAp : 0 < CA := (Real.exp_pos _).trans_le hCA
  have hCQp : 0 < CQ := (Real.exp_pos _).trans_le hCQ
  have hlogCA : 1 ≤ Real.log CA := by
    simpa using Real.log_le_log (Real.exp_pos 1) hCA
  refine ⟨Real.log CA + A.natDegree + CQ, by positivity, 1, zero_lt_one, ?_⟩
  intro r hr
  have hrp : 0 < r := zero_lt_one.trans_le hr
  have hrn : 1 ≤ r ^ Q.natDegree := one_le_pow₀ hr
  have hrrn : r ≤ r ^ Q.natDegree := by
    simpa using pow_le_pow_right₀ hr hn
  have hF : Continuous (fun z => A.eval z * Complex.exp (Q.eval z)) :=
    A.continuous.mul (Complex.continuous_exp.comp Q.continuous)
  obtain ⟨z, hz, heq, _⟩ := maximumModulus_attained _ hF r hrp
  have hzn : ‖z‖ = r := by simpa using hz
  have hA := polynomial_circle_bound A CA hAb hr hzn
  have hQ := polynomial_circle_bound Q CQ hQb hr hzn
  have hQre : (Q.eval z).re ≤ CQ * r ^ Q.natDegree := (Complex.re_le_norm _).trans hQ
  have hM : max (Real.exp 1) (maximumModulus (fun z => A.eval z * Complex.exp (Q.eval z)) r) ≤
      CA * r ^ A.natDegree * Real.exp (CQ * r ^ Q.natDegree) := by
    apply max_le
    · calc
        Real.exp 1 ≤ CA := hCA
        _ ≤ CA * r ^ A.natDegree := le_mul_of_one_le_right hCAp.le (one_le_pow₀ hr)
        _ ≤ _ := le_mul_of_one_le_right (by positivity)
          (Real.one_le_exp_iff.mpr (by positivity))
    · change ‖A.eval z * Complex.exp (Q.eval z)‖ = maximumModulus (fun z => A.eval z * Complex.exp (Q.eval z)) r at heq
      rw [← heq, norm_mul, Complex.norm_exp]
      exact mul_le_mul hA (Real.exp_le_exp.mpr hQre) (Real.exp_pos _).le (by positivity)
  calc
    _ ≤ Real.log (CA * r ^ A.natDegree * Real.exp (CQ * r ^ Q.natDegree)) :=
      Real.log_le_log ((Real.exp_pos _).trans_le (le_max_left _ _)) hM
    _ = Real.log CA + (A.natDegree : ℝ) * Real.log r + CQ * r ^ Q.natDegree := by
      rw [Real.log_mul (by positivity) (Real.exp_ne_zero _),
        Real.log_mul hCAp.ne' (pow_pos hrp _).ne', Real.log_pow, Real.log_exp]
    _ ≤ (Real.log CA + A.natDegree + CQ) * r ^ Q.natDegree := by
      have hlogr : Real.log r ≤ r ^ Q.natDegree := (Real.log_le_sub_one_of_pos hrp).trans
        (by linarith)
      have hconst := mul_le_mul_of_nonneg_left hrn (by linarith : 0 ≤ Real.log CA)
      have hterm := mul_le_mul_of_nonneg_left hlogr (Nat.cast_nonneg A.natDegree : (0 : ℝ) ≤ _)
      nlinarith

lemma polynomial_exp_order_of_constant (A Q : Polynomial ℂ) (f : NonzeroEntireFunction)
    (hA : A ≠ 0) (hf : f.toFun = (fun z => A.eval z * Complex.exp (Q.eval z)))
    (hQ : Q.natDegree = 0) : order f = 0 := by
  have hQ' : Q = Polynomial.C (Q.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hQ
  apply order_polynomial (A * Polynomial.C (Complex.exp (Q.coeff 0))) f
    (mul_ne_zero hA (by simp))
  rw [hf, hQ']
  funext z
  simp

/-- Uniform leading-monomial asymptotics, specialized to a fixed unit ray. -/
lemma polynomial_ray_error (P : Polynomial ℂ) (u : ℂ) (hu : ‖u‖ = 1) :
    ∀ᶠ r : ℝ in atTop,
      ‖P.eval ((r : ℂ) * u) - P.leadingCoeff * ((r : ℂ) * u) ^ P.natDegree‖ ≤
        (‖P.leadingCoeff‖ / 2) * r ^ P.natDegree := by
  have ht : Tendsto (fun r : ℝ => (r : ℂ) * u) atTop (Bornology.cobounded ℂ) := by
    apply tendsto_norm_atTop_iff_cobounded.mp
    simpa [norm_mul, hu] using (tendsto_abs_atTop_atTop : Tendsto (fun r : ℝ => |r|) atTop atTop)
  have h := (Polynomial.isEquivalent_cobounded_leading_monomial (P := P)).isLittleO
  have hb := ht.eventually (h.bound (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hb, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  simpa [Pi.sub_apply, norm_mul, norm_pow, hu, Complex.norm_real, abs_of_nonneg hr0,
    div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hr

lemma exists_positive_leading_ray (Q : Polynomial ℂ) (hn : 0 < Q.natDegree) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ Q.leadingCoeff * u ^ Q.natDegree = (‖Q.leadingCoeff‖ : ℂ) := by
  have hlc : Q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr
    (Polynomial.ne_zero_of_natDegree_gt hn)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq ((‖Q.leadingCoeff‖ : ℂ) / Q.leadingCoeff) hn
  have hnorm : ‖u‖ ^ Q.natDegree = 1 := by
    simpa [norm_pow, norm_div, Complex.norm_real, abs_of_nonneg (norm_nonneg _),
      div_self (norm_ne_zero_iff.mpr hlc)] using congrArg norm hu
  refine ⟨u, (pow_eq_one_iff_of_nonneg (norm_nonneg u) hn.ne').mp hnorm, ?_⟩
  rw [hu, mul_div_cancel₀ _ hlc]

lemma polynomial_norm_lower_on_ray (A : Polynomial ℂ) (_hA : A ≠ 0)
    (u : ℂ) (hu : ‖u‖ = 1) :
    ∀ᶠ r : ℝ in atTop, (‖A.leadingCoeff‖ / 2) * r ^ A.natDegree ≤
      ‖A.eval ((r : ℂ) * u)‖ := by
  filter_upwards [polynomial_ray_error A u hu, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  have h := norm_le_norm_add_norm_sub
    (A.eval ((r : ℂ) * u)) (A.leadingCoeff * ((r : ℂ) * u) ^ A.natDegree)
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hu, mul_one] at h
  linarith

lemma polynomial_re_lower_on_positive_ray (Q : Polynomial ℂ) (u : ℂ)
    (hu : ‖u‖ = 1) (hlead : Q.leadingCoeff * u ^ Q.natDegree = (‖Q.leadingCoeff‖ : ℂ)) :
    ∀ᶠ r : ℝ in atTop, (‖Q.leadingCoeff‖ / 2) * r ^ Q.natDegree ≤
      (Q.eval ((r : ℂ) * u)).re := by
  filter_upwards [polynomial_ray_error Q u hu, eventually_ge_atTop (0 : ℝ)] with r hr hr0
  have h := Complex.re_le_norm
    (Q.leadingCoeff * ((r : ℂ) * u) ^ Q.natDegree - Q.eval ((r : ℂ) * u))
  have heq : Q.leadingCoeff * ((r : ℂ) * u) ^ Q.natDegree =
      ((‖Q.leadingCoeff‖ * r ^ Q.natDegree : ℝ) : ℂ) := by
    rw [mul_pow, mul_left_comm, hlead, Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  rw [norm_sub_rev, heq, Complex.sub_re, Complex.ofReal_re] at h
  rw [heq] at hr
  linarith

theorem polynomial_exp_ray_lower :
    Specs.D12Complex.Ch17.ElementaryOrderOperations.polynomial_exp_ray_lower_type := by
  intro A Q hA hn
  obtain ⟨u, hu, hlead⟩ := exists_positive_leading_ray Q hn
  have ha : 0 < ‖A.leadingCoeff‖ / 2 :=
    div_pos (norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hA)) (by norm_num)
  have hq : 0 < ‖Q.leadingCoeff‖ / 2 := div_pos
    (norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt hn)))
    (by norm_num)
  have hev := (polynomial_norm_lower_on_ray A hA u hu).and
    (polynomial_re_lower_on_positive_ray Q u hu hlead)
  obtain ⟨R, hR⟩ := eventually_atTop.1 hev
  refine ⟨u, hu, hlead, ‖Q.leadingCoeff‖ / 2, hq,
    -Real.log (‖A.leadingCoeff‖ / 2), max 1 R, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hrp : 0 < r := zero_lt_one.trans_le hr1
  obtain ⟨hAn, hQre⟩ := hR r ((le_max_right _ _).trans hr)
  have hAnp : 0 < ‖A.eval ((r : ℂ) * u)‖ := (mul_pos ha (pow_pos hrp _)).trans_le hAn
  have hlog := Real.log_le_log (mul_pos ha (pow_pos hrp _)) hAn
  rw [Real.log_mul ha.ne' (pow_pos hrp _).ne', Real.log_pow] at hlog
  rw [norm_mul, Complex.norm_exp, Real.log_mul hAnp.ne' (Real.exp_ne_zero _), Real.log_exp]
  linarith

/-- Two-sided power bounds for log M give an actual limit of the growth
quotient, so the extended-real limsup is determined, including its clipping. -/
lemma growthQuotient_tendsto_of_log_bounds (f : ℂ → ℂ) (n : ℕ) (c C : ℝ)
    (hc : 0 < c) (hC : 0 < C)
    (hb : ∀ᶠ r : ℝ in atTop,
      c * r ^ n ≤ Real.log (max (Real.exp 1) (maximumModulus f r)) ∧
      Real.log (max (Real.exp 1) (maximumModulus f r)) ≤ C * r ^ n) :
    Tendsto (growthQuotient f) atTop (𝓝 (n : ℝ)) := by
  have hlo : Tendsto (fun r : ℝ => (n : ℝ) + Real.log c / Real.log r) atTop (𝓝 (n : ℝ)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop :
        Tendsto (fun r : ℝ => Real.log c / Real.log r) atTop (𝓝 0))
  have hhi : Tendsto (fun r : ℝ => (n : ℝ) + Real.log C / Real.log r) atTop (𝓝 (n : ℝ)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop Real.tendsto_log_atTop :
        Tendsto (fun r : ℝ => Real.log C / Real.log r) atTop (𝓝 0))
  apply hlo.squeeze' hhi
  · filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with r hr hr1
    have hrp : 0 < r := zero_lt_one.trans hr1
    have hlog := Real.log_le_log (mul_pos hc (pow_pos hrp n)) hr.1
    rw [Real.log_mul hc.ne' (pow_pos hrp n).ne', Real.log_pow] at hlog
    have hd := (div_le_div_iff_of_pos_right (Real.log_pos hr1)).2 hlog
    change _ ≤ Real.log (Real.log (max (Real.exp 1) (maximumModulus f r))) / Real.log r
    convert hd using 1
    field_simp [(Real.log_pos hr1).ne']
    ring
  · filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with r hr hr1
    have hrp : 0 < r := zero_lt_one.trans hr1
    have hl : 0 < Real.log (max (Real.exp 1) (maximumModulus f r)) := by
      have h := Real.log_le_log (Real.exp_pos 1) (le_max_left (Real.exp 1) (maximumModulus f r))
      rw [Real.log_exp] at h
      linarith
    have hlog := Real.log_le_log hl hr.2
    rw [Real.log_mul hC.ne' (pow_pos hrp n).ne', Real.log_pow] at hlog
    have hd := (div_le_div_iff_of_pos_right (Real.log_pos hr1)).2 hlog
    change Real.log (Real.log (max (Real.exp 1) (maximumModulus f r))) / Real.log r ≤ _
    convert hd using 1
    field_simp [(Real.log_pos hr1).ne']
    ring

theorem polynomial_exp_order :
    Specs.D12Complex.Ch17.ElementaryOrderOperations.polynomial_exp_order_type := by
  intro A Q f hA hf
  by_cases hn : Q.natDegree = 0
  · simpa only [hn, Nat.cast_zero, order] using polynomial_exp_order_of_constant A Q f hA hf hn
  have hnp : 0 < Q.natDegree := Nat.pos_of_ne_zero hn
  obtain ⟨C, hC, R, hR, hupper⟩ := polynomial_exp_upper A Q hA hnp
  obtain ⟨u, hu, _hlead, c, hc, B, S, hS, hlower⟩ := polynomial_exp_ray_lower A Q hA hnp
  have hpowl : Tendsto (fun r : ℝ => r ^ Q.natDegree) atTop atTop := tendsto_pow_atTop hn
  have hb : ∀ᶠ r : ℝ in atTop,
      (c / 2) * r ^ Q.natDegree ≤ Real.log (max (Real.exp 1) (maximumModulus f.toFun r)) ∧
      Real.log (max (Real.exp 1) (maximumModulus f.toFun r)) ≤ C * r ^ Q.natDegree := by
    filter_upwards [eventually_ge_atTop R, eventually_ge_atTop S, eventually_ge_atTop (1 : ℝ),
      hpowl.eventually_ge_atTop (2 * B / c), polynomial_norm_lower_on_ray A hA u hu]
      with r hrR hrS hr1 hrpow hrA
    have hrp : 0 < r := zero_lt_one.trans_le hr1
    have hpoint : ‖A.eval ((r : ℂ) * u) * Complex.exp (Q.eval ((r : ℂ) * u))‖ ≤
        max (Real.exp 1) (maximumModulus f.toFun r) := by
      rw [← congrFun hf ((r : ℂ) * u)]
      exact (norm_le_maximumModulus f.holomorphic hrp (by
        simp [Complex.norm_real, abs_of_nonneg hrp.le, hu])).trans (le_max_right _ _)
    have hAnp : 0 < ‖A.eval ((r : ℂ) * u)‖ := lt_of_lt_of_le
      (mul_pos (div_pos (norm_pos_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hA))
        (by norm_num)) (pow_pos hrp _)) hrA
    have hFn : 0 < ‖A.eval ((r : ℂ) * u) * Complex.exp (Q.eval ((r : ℂ) * u))‖ := by
      rw [norm_mul, Complex.norm_exp]
      positivity
    have hpointlog := Real.log_le_log hFn hpoint
    have hlow := hlower r hrS
    have hB : B ≤ c / 2 * r ^ Q.natDegree := by
      have := (div_le_iff₀ hc).mp hrpow
      nlinarith
    have hpoly : 0 ≤ (A.natDegree : ℝ) * Real.log r := mul_nonneg (Nat.cast_nonneg _)
      (Real.log_nonneg hr1)
    constructor
    · linarith
    · simpa only [hf, maximumModulus] using hupper r hrR
  have ht := growthQuotient_tendsto_of_log_bounds f.toFun Q.natDegree (c / 2) C
    (by positivity) hC hb
  simpa [order, Specs.D12Complex.Ch17.OrderDivisorDefinitions.order_value, growthQuotient]
    using (ENNReal.tendsto_ofReal ht).limsup_eq

end D12Complex.ElementaryOrderOperations
