import MathGenome.Internal.ComplexAnalysis.Specs.D12Complex.Ch17.BlaschkeProduct
import MathGenome.Internal.ComplexAnalysis.D12Complex.Ch16.HolomorphicProducts
import Mathlib.Topology.MetricSpace.Algebra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FunProp

noncomputable section
open Set Metric Filter
open scoped Topology ComplexConjugate
namespace D12Complex.BlaschkeProduct

abbrev factor := Specs.D12Complex.Ch17.BlaschkeProduct.factor_value
abbrev factors := Specs.D12Complex.Ch17.BlaschkeProduct.factors_value
abbrev product := Specs.D12Complex.Ch17.BlaschkeProduct.product_value
abbrev partialProduct := Specs.D12Complex.Ch17.BlaschkeProduct.partialProduct_value
abbrev Admissible := Specs.D12Complex.Ch17.BlaschkeProduct.Admissible_value

lemma denominator_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    1 - conj a * z ≠ 0 := by
  have h : ‖conj a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg z]
  intro heq
  rw [← sub_eq_zero.mp heq, norm_one] at h
  exact (lt_irrefl _ h)

lemma norm_phase {a : ℂ} (ha : a ≠ 0) : ‖(‖a‖ : ℂ) / a‖ = 1 := by
  simp [norm_ne_zero_iff.mpr ha]

lemma factor_analytic {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (factor a) z := by
  exact analyticAt_const.mul ((analyticAt_const.sub analyticAt_id).div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    (denominator_ne_zero ha hz))

lemma factor_eq_zero_iff {a z : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1)
    (hz : ‖z‖ < 1) : factor a z = 0 ↔ z = a := by
  have hc : (‖a‖ : ℂ) / a ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha0)) ha0
  change ((‖a‖ : ℂ) / a) * ((a-z)/(1-conj a*z)) = 0 ↔ z = a
  rw [mul_eq_zero, or_iff_right hc, div_eq_zero_iff,
    or_iff_left (denominator_ne_zero ha hz), sub_eq_zero]
  exact eq_comm

lemma one_sub_factor {a z : ℂ} (ha : a ≠ 0) (hd : 1 - conj a * z ≠ 0) :
    1 - factor a z = (1 - (‖a‖ : ℂ)) * (1 + ((‖a‖ : ℂ) / a) * z) /
      (1 - conj a * z) := by
  have hc : (‖a‖ : ℂ) ^ 2 = conj a * a := by
    rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  change 1 - (‖a‖ : ℂ) / a * ((a-z)/(1-conj a*z)) = _
  calc
    _ = ((1-conj a*z) - (‖a‖ : ℂ) / a * (a-z)) / (1-conj a*z) := by
      conv_rhs => rw [sub_div, div_self hd, mul_div_assoc]
    _ = _ := by
      congr 1
      field_simp [ha]
      linear_combination z * hc

theorem factor_estimate : Specs.D12Complex.Ch17.BlaschkeProduct.factor_estimate_type := by
  intro a z r ha0 ha hz hr
  have hz1 : ‖z‖ < 1 := hz.trans_lt hr
  have hr0 : 0 ≤ r := (norm_nonneg z).trans hz
  have hn : 0 ≤ 1 - ‖a‖ := sub_nonneg.mpr ha.le
  have hd : 0 < 1 - r := sub_pos.mpr hr
  rw [one_sub_factor ha0 (denominator_ne_zero ha hz1), norm_div, norm_mul]
  have hreal : ‖1 - (‖a‖ : ℂ)‖ = 1 - ‖a‖ := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hn]
  rw [hreal]
  have hnum : ‖1 + (‖a‖ : ℂ) / a * z‖ ≤ 1 + r := by
    calc
      _ ≤ ‖(1 : ℂ)‖ + ‖(‖a‖ : ℂ) / a * z‖ := norm_add_le _ _
      _ = 1 + ‖z‖ := by rw [norm_one, norm_mul, norm_phase ha0, one_mul]
      _ ≤ 1 + r := by linarith
  have hden : 1 - r ≤ ‖1 - conj a * z‖ := by
    have hrev := norm_sub_norm_le (1 : ℂ) (conj a * z)
    rw [norm_one, norm_mul, Complex.norm_conj] at hrev
    have : ‖a‖ * ‖z‖ ≤ r := by nlinarith [norm_nonneg a, norm_nonneg z]
    linarith
  exact div_le_div₀ (mul_nonneg hn (by linarith)) (mul_le_mul_of_nonneg_left hnum hn)
    hd hden

lemma norm_identity (a z : ℂ) :
    ‖1 - conj a * z‖ ^ 2 - ‖a - z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.one_re, Complex.one_im]
  ring

theorem factor_bound : Specs.D12Complex.Ch17.BlaschkeProduct.factor_bound_type := by
  intro a z ha0 ha hz
  have hd := denominator_ne_zero ha hz
  have hsq := norm_identity a z
  have hle : ‖a - z‖ ≤ ‖1 - conj a * z‖ := by
    have hpos : 0 ≤ (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
      apply mul_nonneg <;> nlinarith [norm_nonneg a, norm_nonneg z]
    nlinarith [norm_nonneg (a-z), norm_nonneg (1-conj a*z)]
  change ‖(‖a‖ : ℂ) / a * ((a-z)/(1-conj a*z))‖ ≤ 1
  rw [norm_mul, norm_phase ha0, one_mul, norm_div]
  exact (div_le_one (norm_pos_iff.mpr hd)).mpr hle

lemma factor_order {a z : ℂ} (ha0 : a ≠ 0) (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) :
    analyticOrderAt (factor a) z = if z = a then 1 else 0 := by
  let g : ℂ → ℂ := fun w => -((‖a‖ : ℂ) / a) / (1 - conj a * w)
  have hg : AnalyticAt ℂ g z := analyticAt_const.div
    (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)) (denominator_ne_zero ha hz)
  have hgne : g z ≠ 0 := div_ne_zero
    (neg_ne_zero.mpr (div_ne_zero
      (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha0)) ha0))
    (denominator_ne_zero ha hz)
  have heq : factor a = (fun w => w - a) * g := by
    funext w
    dsimp [factor, Specs.D12Complex.Ch17.BlaschkeProduct.factor_value, g]
    ring
  have hl : AnalyticAt ℂ (fun w : ℂ => w - a) z := by fun_prop
  rw [heq, analyticOrderAt_mul hl hg,
    hg.analyticOrderAt_eq_zero.mpr hgne, add_zero]
  split_ifs with h
  · subst z; exact analyticOrderAt_id_sub_const_self
  · exact analyticOrderAt_id_sub_const_of_ne h

lemma factors_of_none {a : ℕ → Option ℂ} {n : ℕ} (hn : a n = none) :
    factors a n = fun _ => 1 := by
  funext z
  change (a n).elim 1 (fun w => factor w z) = 1
  rw [hn]; rfl

lemma factors_of_some {a : ℕ → Option ℂ} {n : ℕ} {w : ℂ} (hn : a n = some w) :
    factors a n = factor w := by
  funext z
  change (a n).elim 1 (fun w => factor w z) = factor w z
  rw [hn]; rfl

lemma factors_holomorphic {a : ℕ → Option ℂ} (ha : Admissible a) (n : ℕ) :
    HolomorphicOn (ball (0 : ℂ) 1) (factors a n) := by
  refine ⟨isOpen_ball, fun z hz => ?_⟩
  have hz' : ‖z‖ < 1 := by simpa using hz
  cases hn : a n with
  | none => rw [factors_of_none hn]; exact differentiableAt_const 1
  | some w =>
    rw [factors_of_some hn]
    exact (factor_analytic (ha.1 n w hn).2 hz').differentiableAt

lemma factors_bound {a : ℕ → Option ℂ} (ha : Admissible a) (n : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) : ‖factors a n z‖ ≤ 1 := by
  cases hn : a n with
  | none => rw [factors_of_none hn]; simp
  | some w =>
    rw [factors_of_some hn]
    exact factor_bound w z (ha.1 n w hn).1 (ha.1 n w hn).2 hz

lemma factors_zero {a : ℕ → Option ℂ} (ha : Admissible a) (n : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) : factors a n z = 0 ↔ a n = some z := by
  cases hn : a n with
  | none => rw [factors_of_none hn]; simp
  | some w =>
    rw [factors_of_some hn]
    simpa only [Option.some.injEq, eq_comm] using
      factor_eq_zero_iff (ha.1 n w hn).1 (ha.1 n w hn).2 hz

lemma factors_order {a : ℕ → Option ℂ} (ha : Admissible a) (n : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) :
    analyticOrderAt (factors a n) z = if a n = some z then 1 else 0 := by
  cases hn : a n with
  | none =>
    rw [factors_of_none hn]
    simp only [reduceCtorEq, ↓reduceIte]
    exact (analyticAt_const (v := (1 : ℂ))).analyticOrderAt_eq_zero.mpr one_ne_zero
  | some w =>
    rw [factors_of_some hn]
    simpa only [Option.some.injEq, eq_comm] using
      factor_order (ha.1 n w hn).1 (ha.1 n w hn).2 hz

lemma normal_condition {a : ℕ → Option ℂ} (ha : Admissible a) :
    HolomorphicProducts.NormalProductCondition (ball (0 : ℂ) 1) (factors a) := by
  intro K hK hKD
  rcases K.eq_empty_or_nonempty with rfl | hKe
  · simp
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hKe continuous_norm.continuousOn
  have hr : ‖x‖ < 1 := by simpa using hKD hx
  let C : ℝ := (1 + ‖x‖) / (1 - ‖x‖)
  have hb (n : ℕ) (z : ℂ) (hz : z ∈ K) :
      ‖factors a n z - 1‖ ≤ (a n).elim 0 (fun w => 1 - ‖w‖) * C := by
    cases hn : a n with
    | none => simp [factors, Specs.D12Complex.Ch17.BlaschkeProduct.factors_value, hn]
    | some w =>
      simpa [factors, Specs.D12Complex.Ch17.BlaschkeProduct.factors_value, hn,
        norm_sub_rev, C, mul_div_assoc] using
        factor_estimate w z ‖x‖ (ha.1 n w hn).1 (ha.1 n w hn).2 (hmax hz) hr
  have hsup (n : ℕ) :
      sSup ((fun z => ‖factors a n z - 1‖) '' K) ≤
        (a n).elim 0 (fun w => 1 - ‖w‖) * C := by
    apply csSup_le (hKe.image _)
    rintro _ ⟨z, hz, rfl⟩
    exact hb n z hz
  have hnonneg (n : ℕ) : 0 ≤ sSup ((fun z => ‖factors a n z - 1‖) '' K) := by
    obtain ⟨z, hz⟩ := hKe
    exact (norm_nonneg _).trans
      (le_csSup ⟨(a n).elim 0 (fun w => 1 - ‖w‖) * C, by
        rintro _ ⟨w, hw, rfl⟩; exact hb n w hw⟩ (mem_image_of_mem _ hz))
  exact Summable.of_nonneg_of_le hnonneg hsup (ha.2.mul_right C)

lemma product_holomorphic {a : ℕ → Option ℂ} (ha : Admissible a) (m : ℕ) :
    HolomorphicOn (ball (0 : ℂ) 1) (product a m) := by
  have hp := (HolomorphicProducts.holomorphic_product_limit _ _ isOpen_ball
    (factors_holomorphic ha) (normal_condition ha)).2
  refine ⟨isOpen_ball, fun z hz => ?_⟩
  exact (differentiableAt_id.pow m).mul (hp.2 z hz)

lemma product_convergence {a : ℕ → Option ℂ} (ha : Admissible a) (m : ℕ) :
    TendstoLocallyUniformlyOn (partialProduct a m) (product a m) atTop
      (ball (0 : ℂ) 1) := by
  have hp := HolomorphicProducts.holomorphic_product_limit _ _ isOpen_ball
    (factors_holomorphic ha) (normal_condition ha)
  have hc : TendstoUniformlyOn (fun (_ : ℕ) (z : ℂ) => z ^ m) (fun z => z ^ m)
      atTop (ball (0 : ℂ) 1) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    exact Eventually.of_forall (fun n z hz => by simpa using hε)
  have hpc : ContinuousOn (fun z => ∏' n, factors a n z) (ball (0 : ℂ) 1) :=
    fun z hz => (hp.2.2 z hz).continuousAt.continuousWithinAt
  exact hc.tendstoLocallyUniformlyOn.mul₀ hp.1 (by fun_prop) hpc

lemma partial_bound {a : ℕ → Option ℂ} (ha : Admissible a) (m N : ℕ)
    {z : ℂ} (hz : ‖z‖ < 1) : ‖partialProduct a m N z‖ ≤ 1 := by
  change ‖z ^ m * ∏ n ∈ Finset.range N, factors a n z‖ ≤ 1
  rw [norm_mul, norm_pow, norm_prod]
  have hp : (∏ n ∈ Finset.range N, ‖factors a n z‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun n _ => factors_bound ha n hz)
  calc
    _ ≤ ‖z‖ ^ m * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ 1 := by simpa using pow_le_one₀ (norm_nonneg z) hz.le

lemma product_bound {a : ℕ → Option ℂ} (ha : Admissible a) (m : ℕ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : ‖product a m z‖ ≤ 1 := by
  apply le_of_tendsto ((product_convergence ha m).tendsto_at hz).norm
  exact Eventually.of_forall (fun N => partial_bound ha m N (by simpa using hz))

lemma product_zero_iff {a : ℕ → Option ℂ} (ha : Admissible a) (m : ℕ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    product a m z = 0 ↔ (z = 0 ∧ 0 < m) ∨ ∃ n, a n = some z := by
  change z ^ m * (∏' n, factors a n z) = 0 ↔ _
  rw [mul_eq_zero, HolomorphicProducts.product_eq_zero_iff _ _ (normal_condition ha) z hz]
  simp only [factors_zero ha _ (by simpa using hz), pow_eq_zero_iff', Nat.pos_iff_ne_zero]

lemma product_order {a : ℕ → Option ℂ} (ha : Admissible a) (m : ℕ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    {n : ℕ | a n = some z}.Finite ∧
      analyticOrderAt (product a m) z = (if z = 0 then (m : ℕ∞) else 0) +
        ∑' n, if a n = some z then (1 : ℕ∞) else 0 := by
  let u := factors a
  have hu := factors_holomorphic ha
  have hn := normal_condition ha
  have hzu : ∀ n, AnalyticAt ℂ (u n) z :=
    fun n => HolomorphicProducts.analyticAt_of_holomorphic (hu n) hz
  obtain ⟨N, hN⟩ := HolomorphicProducts.tail_nonvanishing_on_compact _ _ isOpen_ball
    hu hn {z} isCompact_singleton (singleton_subset_iff.mpr hz)
  have ht := hN N le_rfl z (mem_singleton z)
  have hnot (n : ℕ) (hn : N ≤ n) : a n ≠ some z := by
    intro heq
    exact ht.1 n hn ((factors_zero ha n (by simpa using hz)).mpr heq)
  have hsupp : {n : ℕ | a n = some z}.Finite := by
    apply (Finset.range N).finite_toSet.subset
    intro n hn
    exact Finset.mem_range.mpr (by by_contra h; exact hnot n (by omega) hn)
  have hta : AnalyticAt ℂ (fun w => ∏' k, u (k + N) w) z :=
    HolomorphicProducts.analyticAt_of_holomorphic
      (HolomorphicProducts.holomorphic_tail_limit _ _ isOpen_ball hu hn N).2 hz
  have htailord : analyticOrderAt (fun w => ∏' k, u (k + N) w) z = 0 :=
    hta.analyticOrderAt_eq_zero.mpr ht.2
  have heq : (fun w => ∏' k, u k w) =ᶠ[𝓝 z]
      (fun w => ∏ k ∈ Finset.range N, u k w) * (fun w => ∏' k, u (k+N) w) := by
    apply eventually_of_mem (isOpen_ball.mem_nhds hz)
    intro w hw
    exact HolomorphicProducts.product_prefix_tail _ _ isOpen_ball hu hn N w hw
  have horder : analyticOrderAt (fun w => ∏' k, u k w) z =
      ∑' n, if a n = some z then (1 : ℕ∞) else 0 := by
    rw [analyticOrderAt_congr heq,
      analyticOrderAt_mul ((Finset.range N).analyticAt_fun_prod (fun k _ => hzu k)) hta,
      htailord, add_zero, HolomorphicProducts.order_partial_product u z hzu N]
    rw [tsum_eq_sum (s := Finset.range N) (fun n hn => ite_eq_right (hnot n (by simpa using hn)))]
    apply Finset.sum_congr rfl
    intro n hn
    exact factors_order ha n (by simpa using hz)
  have hpa : AnalyticAt ℂ (fun w : ℂ => w ^ m) z := by fun_prop
  have hpord : analyticOrderAt (fun w : ℂ => w ^ m) z =
      if z = 0 then (m : ℕ∞) else 0 := by
    split_ifs with hz0
    · subst z
      apply hpa.analyticOrderAt_eq_natCast.mpr
      refine ⟨fun _ => 1, analyticAt_const, one_ne_zero, ?_⟩
      exact Eventually.of_forall (fun w => by simp)
    · exact hpa.analyticOrderAt_eq_zero.mpr (pow_ne_zero m hz0)
  refine ⟨hsupp, ?_⟩
  change analyticOrderAt ((fun w : ℂ => w ^ m) * (fun w => ∏' k, u k w)) z = _
  rw [analyticOrderAt_mul hpa (HolomorphicProducts.analyticAt_of_holomorphic
    (HolomorphicProducts.holomorphic_product_limit _ _ isOpen_ball hu hn).2 hz), hpord, horder]

theorem blaschke_product : Specs.D12Complex.Ch17.BlaschkeProduct.blaschke_product_type := by
  intro a ha m
  refine ⟨product_convergence ha m, product_holomorphic ha m, fun z hz => product_bound ha m hz,
    fun z hz => product_zero_iff ha m hz, fun z hz => product_order ha m hz, ?_⟩
  have hzero (n : ℕ) : a n ≠ some 0 := fun h => (ha.1 n 0 h).1 rfl
  simpa [hzero] using (product_order ha m (z := 0) (by simp)).2

theorem normal_product_condition :
    Specs.D12Complex.Ch17.BlaschkeProduct.normal_product_condition_type := by
  intro a ha
  exact normal_condition ha

theorem finite_admissible : Specs.D12Complex.Ch17.BlaschkeProduct.finite_admissible_type := by
  intro a N hN hv
  refine ⟨hv, summable_of_ne_finset_zero (s := Finset.range N) ?_⟩
  intro n hn
  rw [hN n (by simpa using hn)]
  rfl

theorem finite_product : Specs.D12Complex.Ch17.BlaschkeProduct.finite_product_type := by
  intro a N m hN z
  change z ^ m * (∏' n, factors a n z) = z ^ m * ∏ n ∈ Finset.range N, factors a n z
  congr 1
  apply tprod_eq_prod
  intro n hn
  rw [factors_of_none (hN n (by simpa using hn))]

theorem empty_product : Specs.D12Complex.Ch17.BlaschkeProduct.empty_product_type := by
  intro m
  funext z
  change z ^ m * (∏' n, factors (fun _ => none) n z) = z ^ m
  simp [factors, Specs.D12Complex.Ch17.BlaschkeProduct.factors_value]

end D12Complex.BlaschkeProduct
