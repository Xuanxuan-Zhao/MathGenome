import MathGenome.Internal.ProbabilityFoundations.Specs.ProbabilityFoundations.Ch08.ThreeSeriesVarianceNecessity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Variance necessity in Kolmogorov's three-series theorem, paper.tex:2945–2971.
The convergence hypothesis uses ordered partial sums, permitting conditional
convergence. After truncation, a characteristic-function deficit controls the
variance. Almost sure convergence gives a uniform bound on characteristic
functions of finite tails by dominated convergence in L¹. Independence and an
elementary logarithmic product bound finish the proof. No moment assumption on
the original variables or summability assumption on the means is made. -/

open MeasureTheory Filter
open scoped Topology ENNReal ComplexConjugate

namespace ProbabilityFoundations.Ch08

-- Keep proof helpers distinct from helpers in other chapter modules.
namespace ThreeSeriesVarianceNecessity

/-- A convergent ordered series has terms tending to zero. -/
theorem OrderedSeriesConverges.tendsto_zero {f : ℕ → ℝ}
    (h : OrderedSeriesConverges f) : Tendsto f atTop (𝓝 0) := by
  obtain ⟨l, hl⟩ := h
  have hd := (hl.comp (tendsto_add_atTop_nat 1)).sub hl
  simpa only [Function.comp_def, Finset.sum_range_succ, add_sub_cancel_left,
    sub_self] using hd

/-- Finite modifications preserve ordinary convergence, even when the
series is conditionally convergent. -/
theorem OrderedSeriesConverges.congr_eventually {f g : ℕ → ℝ}
    (h : OrderedSeriesConverges f) (hfg : f =ᶠ[atTop] g) :
    OrderedSeriesConverges g := by
  obtain ⟨l, hl⟩ := h
  obtain ⟨m, hm⟩ := eventually_atTop.mp hfg
  let d := (∑ k ∈ Finset.range m, g k) - ∑ k ∈ Finset.range m, f k
  refine ⟨l + d, (hl.add_const d).congr' ?_⟩
  filter_upwards [eventually_ge_atTop m] with n hn
  have heq : (∑ k ∈ Finset.range n, g k) - ∑ k ∈ Finset.range m, g k =
      (∑ k ∈ Finset.range n, f k) - ∑ k ∈ Finset.range m, f k := by
    rw [Finset.sum_range_sub_sum_range hn, Finset.sum_range_sub_sum_range hn]
    apply Finset.sum_congr rfl
    intro k hk
    exact (hm k (Finset.mem_filter.mp hk).2).symm
  dsimp [d]
  linarith

/-- Measurability is with respect to the original sigma algebra. -/
theorem measurable_symmetricTruncation {Ω : Type*} [MeasurableSpace Ω]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k)) (a : ℝ) (k : ℕ) :
    Measurable (symmetricTruncation a X k) :=
  (hX k).indicator (by simpa only [Real.norm_eq_abs, id_eq] using
    (measurableSet_le (hX k).norm (measurable_const (a := a))))

/-- The deterministic truncation function is measurable. -/
theorem measurable_truncateReal (a : ℝ) :
    Measurable (fun x : ℝ => {y : ℝ | |y| ≤ a}.indicator id x) :=
  measurable_id.indicator (by simpa only [Real.norm_eq_abs, id_eq] using
    (measurableSet_le (measurable_id (α := ℝ)).norm (measurable_const (a := a))))

theorem abs_symmetricTruncation_le {Ω : Type*} (X : ℕ → Ω → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ) (ω : Ω) :
    |symmetricTruncation a X k ω| ≤ a := by
  by_cases h : |X k ω| ≤ a
  · simp [symmetricTruncation, h]
  · simpa [symmetricTruncation, Set.indicator_of_notMem, h] using ha

/-- Bounded truncations have all finite moments, on the given measure. -/
theorem memLp_symmetricTruncation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ k, Measurable (X k)) {a : ℝ} (ha : 0 ≤ a) (k : ℕ) (p : ℝ≥0∞) :
    MemLp (symmetricTruncation a X k) p P := by
  apply MemLp.of_bound (measurable_symmetricTruncation X hX a k).aestronglyMeasurable a
  exact Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs, id_eq] using abs_symmetricTruncation_le X ha k ω)

/-- Independence survives the exact coordinatewise truncation. -/
theorem iIndepFun_symmetricTruncation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (hX : ProbabilityTheory.iIndepFun X P)
    (a : ℝ) : ProbabilityTheory.iIndepFun (symmetricTruncation a X) P := by
  convert hX.comp (fun _ => fun x : ℝ => {y : ℝ | |y| ≤ a}.indicator id x)
    (fun _ => measurable_truncateReal a) using 1
  ext k ω
  by_cases h : |X k ω| ≤ a <;> simp [symmetricTruncation, h]

/-- On each convergent path, truncation changes only finitely many terms. -/
theorem eventually_symmetricTruncation_eq {Ω : Type*} (X : ℕ → Ω → ℝ)
    {a : ℝ} (ha : 0 < a) (ω : Ω)
    (h : OrderedSeriesConverges (fun k => X k ω)) :
    (fun k => X k ω) =ᶠ[atTop] (fun k => symmetricTruncation a X k ω) := by
  have habs : Tendsto (fun k => |X k ω|) atTop (𝓝 0) := by
    simpa only [abs_zero] using (OrderedSeriesConverges.tendsto_zero h).abs
  filter_upwards [(tendsto_order.mp habs).2 a ha] with k hk
  simp [symmetricTruncation, le_of_lt hk]

/-- Almost sure ordered convergence transfers to the bounded truncations.
No independence or integrability assumption is needed for this reduction. -/
theorem ae_orderedSeriesConverges_symmetricTruncation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    {a : ℝ} (ha : 0 < a)
    (h : ∀ᵐ ω ∂P, OrderedSeriesConverges (fun k => X k ω)) :
    ∀ᵐ ω ∂P, OrderedSeriesConverges (fun k => symmetricTruncation a X k ω) := by
  filter_upwards [h] with ω hω
  exact OrderedSeriesConverges.congr_eventually hω
    (eventually_symmetricTruncation_eq X ha ω hω)

/-- An elementary infinite-product criterion. No convergence or positivity
of individual factors is assumed beyond the displayed hypotheses; strict
positivity follows from the positive lower bound on the finite products. -/
theorem summable_one_sub_of_prod_lower_bound
    (u : ℕ → ℝ) (hu0 : ∀ k, 0 ≤ u k) (hu1 : ∀ k, u k ≤ 1)
    (c : ℝ) (hc : 0 < c)
    (hprod : ∀ n, c ≤ ∏ k ∈ Finset.range n, u k) :
    Summable (fun k => 1 - u k) := by
  have hupos (k : ℕ) : 0 < u k := by
    have hp : ∏ j ∈ Finset.range (k + 1), u j ≠ 0 :=
      ne_of_gt (hc.trans_le (hprod (k + 1)))
    exact lt_of_le_of_ne (hu0 k)
      ((Finset.prod_ne_zero_iff.mp hp k (Finset.mem_range.mpr (Nat.lt_succ_self k))).symm)
  refine summable_of_sum_range_le (c := -Real.log c)
    (fun k => sub_nonneg.mpr (hu1 k)) ?_
  intro n
  calc
    ∑ k ∈ Finset.range n, (1 - u k)
        ≤ ∑ k ∈ Finset.range n, -Real.log (u k) := by
      apply Finset.sum_le_sum
      intro k _
      linarith [Real.log_le_sub_one_of_pos (hupos k)]
    _ = -Real.log (∏ k ∈ Finset.range n, u k) := by
      rw [Finset.sum_neg_distrib, Real.log_prod (fun k _ => ne_of_gt (hupos k))]
    _ ≤ -Real.log c := neg_le_neg (Real.log_le_log hc (hprod n))

/-- A summability comparison that permits arbitrary finite initial segments. -/
theorem summable_of_tail_prod_lower_bound
    (v u : ℕ → ℝ) (hv : ∀ k, 0 ≤ v k)
    (hu0 : ∀ k, 0 ≤ u k) (hu1 : ∀ k, u k ≤ 1)
    {d : ℝ} (hd : 0 < d) (hvu : ∀ k, d * v k ≤ 1 - u k)
    (m : ℕ) {c : ℝ} (hc : 0 < c)
    (hprod : ∀ n, c ≤ ∏ k ∈ Finset.range n, u (k + m)) :
    Summable v := by
  have hs := summable_one_sub_of_prod_lower_bound (fun k => u (k + m))
    (fun k => hu0 _) (fun k => hu1 _) c hc hprod
  apply (summable_nat_add_iff m).mp
  have hds : Summable (fun k => d * v (k + m)) :=
    hs.of_nonneg_of_le (fun k => mul_nonneg hd.le (hv _)) (fun k => hvu _)
  exact (summable_mul_left_iff (ne_of_gt hd)).mp hds

/-- Independence converts a local characteristic deficit and a uniform tail
bound into variance summability. The estimates are proved below and applied
in `summable_variance_symmetricTruncation`. -/
theorem summable_variance_of_characteristic_estimates
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k))
    (hInd : ProbabilityTheory.iIndepFun Y P) (t : ℝ)
    {d : ℝ} (hd : 0 < d)
    (hlocal : ∀ k, d * ProbabilityTheory.variance (Y k) P ≤
      1 - ‖charFun (Measure.map (Y k) P) t‖ ^ 2)
    (htail : ∃ m : ℕ, ∀ n : ℕ, (1 / 2 : ℝ) ≤
      ‖charFun (Measure.map (fun ω => ∑ k ∈ Finset.range n, Y (k + m) ω) P) t‖ ^ 2) :
    Summable (fun k => ProbabilityTheory.variance (Y k) P) := by
  obtain ⟨m, hm⟩ := htail
  have hu1 (k : ℕ) : ‖charFun (Measure.map (Y k) P) t‖ ^ 2 ≤ 1 := by
    nlinarith [norm_charFun_le_one (μ := Measure.map (Y k) P) t,
      norm_nonneg (charFun (Measure.map (Y k) P) t)]
  refine summable_of_tail_prod_lower_bound
    (fun k => ProbabilityTheory.variance (Y k) P)
    (fun k => ‖charFun (Measure.map (Y k) P) t‖ ^ 2)
    (fun k => ProbabilityTheory.variance_nonneg _ _) (fun k => sq_nonneg _)
    hu1 hd hlocal m (by norm_num : (0 : ℝ) < 1 / 2) ?_
  intro n
  have hshift : ProbabilityTheory.iIndepFun (fun k => Y (k + m)) P :=
    hInd.precomp (fun _ _ h => Nat.add_right_cancel h)
  have heq := congrFun ((hshift.restrict (Finset.range n)).charFun_map_fun_finsetSum_eq_prod
    (fun k _ => (hY (k + m)).aemeasurable)) t
  simpa only [heq, Finset.prod_apply, norm_prod, ← Finset.prod_pow] using hm n

private noncomputable def expKernel (t x : ℝ) : ℂ :=
  Complex.exp ((t * x : ℝ) * Complex.I)
private lemma norm_expKernel (t x : ℝ) : ‖expKernel t x‖ = 1 := by
  simp [expKernel, Complex.norm_exp]
private lemma measurable_expKernel (t : ℝ) : Measurable (expKernel t) := by
  unfold expKernel
  fun_prop
private lemma integrable_expKernel {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z) (t : ℝ) :
    Integrable (fun ω => expKernel t (Z ω)) P := by
  apply Integrable.of_bound ((measurable_expKernel t).comp hZ).aestronglyMeasurable 1
  exact .of_forall (fun ω => (norm_expKernel t _).le)
private lemma charFun_map_eq {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) {Z : Ω → ℝ} (hZ : Measurable Z) (t : ℝ) :
    charFun (P.map Z) t = ∫ ω, expKernel t (Z ω) ∂P := by
  rw [charFun_apply_real, integral_map hZ.aemeasurable (by fun_prop)]
  simp only [expKernel, Complex.ofReal_mul]

/-- A bounded random variable's characteristic deficit controls its variance.
The independent copy is realized on the genuine probability space `P.prod P`.
Only this one-variable construction is needed; no copied process is assumed. -/
theorem variance_characteristic_deficit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {Z : Ω → ℝ} (hZ : Measurable Z) {a t : ℝ} (_ha : 0 ≤ a)
    (hbound : ∀ ω, |Z ω| ≤ a) (ht : 2 * a * |t| ≤ Real.pi) :
    (4 / Real.pi ^ 2 * t ^ 2) * ProbabilityTheory.variance Z P ≤
      1 - ‖charFun (P.map Z) t‖ ^ 2 := by
  let Q := P.prod P
  let D : Ω × Ω → ℝ := fun p => Z p.1 - Z p.2
  have hm : Measurable D := (hZ.comp measurable_fst).sub (hZ.comp measurable_snd)
  have hL : MemLp Z 2 P := MemLp.of_bound hZ.aestronglyMeasurable a
    (.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hbound ω))
  have hDL : MemLp D 2 Q := (hL.comp_fst P).sub (hL.comp_snd P)
  have hvar : ProbabilityTheory.variance D Q = 2 * ProbabilityTheory.variance Z P := by
    change ProbabilityTheory.variance (fun p : Ω × Ω => Z p.1 + -(Z p.2)) (P.prod P) = _
    simpa only [ProbabilityTheory.variance_neg, Pi.neg_apply, two_mul] using
      (ProbabilityTheory.variance_add_prod hL hL.neg)
  have hmoment : 2 * ProbabilityTheory.variance Z P ≤ ∫ p, D p ^ 2 ∂Q := by
    rw [← hvar]
    exact ProbabilityTheory.variance_le_expectation_sq hDL.aestronglyMeasurable
  have hc : charFun (Q.map D) t =
      charFun (P.map Z) t * conj (charFun (P.map Z) t) := by
    have hi := ProbabilityTheory.indepFun_prod hZ hZ.neg (μ := P) (ν := P)
    have hh := congrFun (hi.charFun_map_fun_add_eq_mul
      (hZ.comp measurable_fst).aemeasurable (hZ.neg.comp measurable_snd).aemeasurable) t
    simp only [Pi.mul_apply, ← Measure.map_map hZ measurable_fst,
      ← Measure.map_map hZ.neg measurable_snd,
      measurePreserving_fst.map_eq, measurePreserving_snd.map_eq] at hh
    have hn : charFun (P.map (fun ω => -Z ω)) t = conj (charFun (P.map Z) t) := by
      have hh := charFun_map_mul_comp (μ := P) hZ.aemeasurable (-1) t
      simpa only [neg_one_mul, charFun_neg] using hh
    change charFun (Q.map D) t = charFun (P.map Z) t * charFun (P.map (fun ω => -Z ω)) t at hh
    rw [hn] at hh
    exact hh
  have hcos : ∫ p, Real.cos (t * D p) ∂Q = ‖charFun (P.map Z) t‖ ^ 2 := by
    have hh := congrArg Complex.re hc
    rw [charFun_map_eq Q hm t] at hh
    have hr := integral_re (integrable_expKernel Q hm t)
    change (∫ p, (expKernel t (D p)).re ∂Q) = (∫ p, expKernel t (D p) ∂Q).re at hr
    rw [← hr] at hh
    simpa only [expKernel, Complex.exp_ofReal_mul_I_re, Complex.mul_conj',
      ← Complex.ofReal_pow, Complex.ofReal_re] using hh
  have hcosInt : Integrable (fun p => Real.cos (t * D p)) Q := by
    simpa [expKernel, Complex.exp_re] using (integrable_expKernel Q hm t).re
  have hineq : ∫ p, Real.cos (t * D p) ∂Q ≤
      ∫ p, 1 - (2 / Real.pi ^ 2 * t ^ 2) * D p ^ 2 ∂Q := by
    apply integral_mono hcosInt ((integrable_const 1).sub (hDL.integrable_sq.const_mul _))
    intro p
    have hb : |t * D p| ≤ Real.pi := calc
      |t * D p| = |t| * |Z p.1 - Z p.2| := abs_mul _ _
      _ ≤ |t| * (|Z p.1| + |Z p.2|) := mul_le_mul_of_nonneg_left (abs_sub _ _) (abs_nonneg _)
      _ ≤ |t| * (a + a) := mul_le_mul_of_nonneg_left (add_le_add (hbound _) (hbound _)) (abs_nonneg _)
      _ = 2 * a * |t| := by ring
      _ ≤ Real.pi := ht
    change Real.cos (t * D p) ≤ 1 - (2 / Real.pi ^ 2 * t ^ 2) * D p ^ 2
    convert Real.cos_le_one_sub_mul_cos_sq hb using 1; ring
  rw [integral_sub (integrable_const 1) (hDL.integrable_sq.const_mul _), integral_const,
    probReal_univ, one_smul, integral_const_mul, hcos] at hineq
  have hpos : 0 ≤ 2 / Real.pi ^ 2 * t ^ 2 := by positivity
  have he : (4 / Real.pi ^ 2 * t ^ 2) * ProbabilityTheory.variance Z P =
      (2 / Real.pi ^ 2 * t ^ 2) * (2 * ProbabilityTheory.variance Z P) := by ring
  rw [he]
  linarith [mul_le_mul_of_nonneg_left hmoment hpos]

private lemma expKernel_add (t x y : ℝ) :
    expKernel t (x + y) = expKernel t x * expKernel t y := by
  unfold expKernel
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma norm_expKernel_sub_one (t x y : ℝ) :
    ‖expKernel t (x - y) - 1‖ = ‖expKernel t x - expKernel t y‖ := by
  have he : (expKernel t (x - y) - 1) * expKernel t y =
      expKernel t x - expKernel t y := by
    rw [sub_mul, one_mul, ← expKernel_add, sub_add_cancel]
  rw [← he, norm_mul, norm_expKernel, mul_one]

/-- Almost sure ordered convergence gives a uniform characteristic bound
for every finite tail, without any moment or independence hypothesis. -/
theorem characteristic_tail_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (hY : ∀ k, Measurable (Y k)) (t : ℝ)
    (hconv : ∀ᵐ ω ∂P, OrderedSeriesConverges (fun k => Y k ω)) :
    ∃ m : ℕ, ∀ n : ℕ, (1 / 2 : ℝ) ≤
      ‖charFun (P.map (fun ω => ∑ k ∈ Finset.range n, Y (k + m) ω)) t‖ ^ 2 := by
  classical
  let S : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, Y k ω
  have hS (n : ℕ) : Measurable (S n) := by
    exact Finset.measurable_sum _ (fun k _ => hY k)
  let L : Ω → ℝ := fun ω => if h : OrderedSeriesConverges (fun k => Y k ω)
    then h.choose else 0
  have hSL : ∀ᵐ ω ∂P, Tendsto (fun n => S n ω) atTop (𝓝 (L ω)) := by
    filter_upwards [hconv] with ω hω
    simpa only [L, dite_eq_left hω] using hω.choose_spec
  let F : ℕ → Ω → ℂ := fun n ω => expKernel t (S n ω)
  let G : Ω → ℂ := fun ω => expKernel t (L ω)
  have hF (n : ℕ) : AEStronglyMeasurable (F n) P :=
    ((measurable_expKernel t).comp (hS n)).aestronglyMeasurable
  have hFG : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (𝓝 (G ω)) := by
    filter_upwards [hSL] with ω hω
    exact (by unfold expKernel; fun_prop : Continuous (expKernel t)).continuousAt.tendsto.comp hω
  have hG : AEStronglyMeasurable G P := aestronglyMeasurable_of_tendsto_ae atTop hF hFG
  have hGI : Integrable G P := Integrable.of_bound hG 1
    (.of_forall (fun ω => (norm_expKernel t _).le))
  have hFI (n : ℕ) : Integrable (F n) P := integrable_expKernel P (hS n) t
  have hlim : Tendsto (fun n => ∫ ω, ‖F n ω - G ω‖ ∂P) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := P)
      (F := fun n ω => ‖F n ω - G ω‖) (f := fun _ => (0 : ℝ)) (fun _ => (2 : ℝ))
      (fun n => ((hF n).sub hG).norm) (integrable_const 2)
      (fun n => .of_forall (fun ω => by
        simpa only [Real.norm_eq_abs, abs_norm, F, G, norm_expKernel, show (1 : ℝ) + 1 = 2 by norm_num] using
          norm_sub_le (F n ω) (G ω))) ?_
    · simpa only [integral_zero] using hh
    · filter_upwards [hFG] with ω hω
      simpa only [sub_self, norm_zero] using (hω.sub_const (G ω)).norm
  obtain ⟨m, hm⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 (1 / 8) (by norm_num))
  refine ⟨m, fun n => ?_⟩
  let T : Ω → ℝ := fun ω => ∑ k ∈ Finset.range n, Y (k + m) ω
  have hT : Measurable T := Finset.measurable_sum _ (fun k _ => hY _)
  have hTS (ω : Ω) : T ω = S (n + m) ω - S m ω := by
    dsimp [T, S]
    rw [Nat.add_comm n m, Finset.sum_range_add]
    simp only [add_sub_cancel_left, Nat.add_comm m]
  have hdiff : ‖charFun (P.map T) t - 1‖ ≤
      (∫ ω, ‖F (n + m) ω - G ω‖ ∂P) + ∫ ω, ‖F m ω - G ω‖ ∂P := by
    have hc1 : (∫ _ : Ω, (1 : ℂ) ∂P) = 1 := by simp
    rw [charFun_map_eq P hT t, ← hc1]
    rw [← integral_sub (integrable_expKernel P hT t) (integrable_const 1)]
    apply (norm_integral_le_integral_norm _).trans
    have hadd := integral_add ((hFI (n + m)).sub hGI).norm ((hFI m).sub hGI).norm
    simp only [Pi.sub_apply] at hadd
    rw [← hadd]
    apply integral_mono ((integrable_expKernel P hT t).sub (integrable_const 1)).norm
      (((hFI (n + m)).sub hGI).norm.add ((hFI m).sub hGI).norm)
    intro ω
    change ‖expKernel t (T ω) - 1‖ ≤ ‖F (n + m) ω - G ω‖ + ‖F m ω - G ω‖
    rw [hTS, norm_expKernel_sub_one]
    simpa only [F, norm_sub_rev (G ω) (F m ω)] using
      norm_sub_le_norm_sub_add_norm_sub (F (n + m) ω) (G ω) (F m ω)
  have hsmall : ‖charFun (P.map T) t - 1‖ < 1 / 4 := by
    linarith [hm (n + m) (Nat.le_add_left m n), hm m le_rfl]
  have hnorm : 3 / 4 < ‖charFun (P.map T) t‖ := by
    have hh := norm_sub_norm_le (1 : ℂ) (charFun (P.map T) t)
    rw [norm_one, norm_sub_rev] at hh
    linarith
  change (1 / 2 : ℝ) ≤ ‖charFun (P.map T) t‖ ^ 2
  nlinarith [sq_nonneg (‖charFun (P.map T) t‖ - 3 / 4)]

end ThreeSeriesVarianceNecessity

open ThreeSeriesVarianceNecessity

/-- The variance necessity stage of Kolmogorov's three-series theorem.
Only ordinary almost sure convergence of the original ordered series is assumed. -/
theorem summable_variance_symmetricTruncation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hInd : ProbabilityTheory.iIndepFun X P) (a : ℝ) (ha : 0 < a)
    (hconv : ∀ᵐ ω ∂P, OrderedSeriesConverges (fun k => X k ω)) :
    Summable (fun k => ProbabilityTheory.variance (symmetricTruncation a X k) P) := by
  let Y := symmetricTruncation a X
  have hY (k : ℕ) : Measurable (Y k) := measurable_symmetricTruncation X hX a k
  have hYInd : ProbabilityTheory.iIndepFun Y P := iIndepFun_symmetricTruncation P X hInd a
  have hYconv : ∀ᵐ ω ∂P, OrderedSeriesConverges (fun k => Y k ω) :=
    ae_orderedSeriesConverges_symmetricTruncation P X ha hconv
  let t : ℝ := 1 / (2 * a)
  have htpos : 0 < t := by dsimp [t]; positivity
  have ht : 2 * a * |t| ≤ Real.pi := by
    rw [abs_of_pos htpos]
    have he : 2 * a * t = 1 := by dsimp [t]; field_simp
    rw [he]
    linarith [Real.two_le_pi]
  exact summable_variance_of_characteristic_estimates P Y hY hYInd t
    (d := 4 / Real.pi ^ 2 * t ^ 2) (by positivity)
    (fun k => variance_characteristic_deficit P (hY k) ha.le
      (abs_symmetricTruncation_le X ha.le k) ht)
    (characteristic_tail_lower_bound P Y hY t hYconv)
end ProbabilityFoundations.Ch08
