import MathGenome.Internal.DiscreteMarkovMartingales.Specs.P207.Martingale.StrongMaximal
import MathGenome.Internal.DiscreteMarkovMartingales.P207.Martingale.WeakMaximal
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.LpOrder
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Doob's strong inequality, paper.tex §5.2 (p207:W27).

After deriving the earlier p-th moments by conditional-expectation contraction,
we use a discrete running-maximum potential. For `Z k = max_{j ≤ k} X j`,
Young's inequality gives
  (p-1) Z_{k+1}^p ≤ p X_{k+1} Z_{k+1}^{p-1}
    + (p-1) Z_k^p - p X_{k+1} Z_k^{p-1}.
The last product has expectation at least that of `X_k Z_k^{p-1}` by the
submartingale property and the pull-out identity. Induction gives
  (p-1) E Z_n^p ≤ p E[X_n Z_n^{p-1}].
A scaled application of Young's inequality yields the sharp moment bound;
taking the p-th root includes the zero-moment case without division.

This is a pathwise proof of the same source conclusion. See also Acciaio,
Beiglböck, Penkner, Schachermayer and Temme, "A trajectorial interpretation
of Doob's martingale inequalities", §2, Proposition 2.1,
https://arxiv.org/abs/1202.0447. The implementation proves its deterministic
inequalities directly and only requires almost-sure nonnegativity.
-/

open MeasureTheory
open scoped MeasureTheory

universe u
namespace P207
variable {Ω : Type u} [m : MeasurableSpace Ω]

omit m in
/-- The finite maximum obeys the usual running-maximum recursion. -/
theorem finiteMax_zero (X : ℕ → Ω → ℝ) : finiteMax X 0 = X 0 := by
  funext ω
  simp [finiteMax, Finset.range_one]

omit m in
theorem finiteMax_succ (X : ℕ → Ω → ℝ) (k : ℕ) :
    finiteMax X (k + 1) = fun ω => max (finiteMax X k ω) (X (k + 1) ω) := by
  funext ω
  simp [finiteMax, Finset.range_add_one, Finset.sup'_insert, max_comm]

/-- Young's inequality in the form used for the running-maximum potential. -/
private theorem young_rpow {p a b : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    p * (a * b ^ (p - 1)) ≤ a ^ p + (p - 1) * b ^ p := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hp1 : p - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hy := Real.young_inequality_of_nonneg ha (Real.rpow_nonneg hb (p - 1))
    (Real.HolderConjugate.conjExponent hp)
  rw [← Real.rpow_mul hb] at hy
  have he : (p - 1) * Real.conjExponent p = p := by
    unfold Real.conjExponent
    field_simp
  rw [he] at hy
  have he' : b ^ p / Real.conjExponent p = (p - 1) * b ^ p / p := by
    unfold Real.conjExponent
    field_simp
  rw [he'] at hy
  have := (mul_le_mul_of_nonneg_left hy hp0.le)
  field_simp at this
  nlinarith

/-- Integrability of mixed powers follows from the two p-th moments. -/
private theorem integrable_mul_rpow {μ : Measure Ω} {p : ℝ} (hp : 1 < p)
    {f g : Ω → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal p) μ) :
    Integrable (fun ω => f ω * |g ω| ^ (p - 1)) μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hf' : Integrable (fun ω => |f ω| ^ p) μ := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using
      (integrable_norm_rpow_iff hf.aestronglyMeasurable
        (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top).2 hf
  have hg' : Integrable (fun ω => |g ω| ^ p) μ := by
    simpa only [Real.norm_eq_abs, ENNReal.toReal_ofReal hp0.le] using
      (integrable_norm_rpow_iff hg.aestronglyMeasurable
        (ne_of_gt (ENNReal.ofReal_pos.mpr hp0)) ENNReal.ofReal_ne_top).2 hg
  apply ((hf'.add (hg'.const_mul (p - 1))).div_const p).mono'
  · simpa only [Real.norm_eq_abs, Pi.mul_apply] using hf.aestronglyMeasurable.fun_mul
      (hg.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable
  · filter_upwards with ω
    simp only [Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg (abs_nonneg (g ω)) (p - 1))]
    apply (le_div_iff₀ hp0).mpr
    change |f ω| * |g ω| ^ (p - 1) * p ≤ |f ω| ^ p + (p - 1) * |g ω| ^ p
    nlinarith [young_rpow hp (abs_nonneg (f ω)) (abs_nonneg (g ω))]

/-- Terminal Lp membership controls every preceding nonnegative value. -/
theorem memLp_of_submartingaleUpTo (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ)
    (h : IsSubmartingaleUpTo X ℱ μ n)
    (hnonneg : ∀ k, k ≤ n → 0 ≤ᵐ[μ] X k)
    (p : ℝ) (hp : 1 < p) (hLp : MemLp (X n) (ENNReal.ofReal p) μ)
    (k : ℕ) (hk : k ≤ n) : MemLp (X k) (ENNReal.ofReal p) μ := by
  have hp' : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using (ENNReal.ofReal_le_ofReal hp.le)
  have hext := (submartingale_iff_library μ ℱ _).mp (constant_extension μ ℱ X n h)
  have hle : X k ≤ᵐ[μ] μ[X n | ℱ k] := by
    simpa only [min_eq_left hk, min_self] using hext.ae_le_condExp hk
  apply (hLp.condExp (m := ℱ k) hp').mono' ((h.1 k hk).mono (ℱ.le k) le_rfl).aestronglyMeasurable
  filter_upwards [hnonneg k hk, hle] with ω h0 hle
  simpa only [Real.norm_of_nonneg h0] using hle

/-- In particular, the finite maximum has its p-th moment; no earlier moment
hypothesis has been added. -/
theorem memLp_finiteMax_of_submartingaleUpTo (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ)
    (h : IsSubmartingaleUpTo X ℱ μ n)
    (hnonneg : ∀ k, k ≤ n → 0 ≤ᵐ[μ] X k)
    (p : ℝ) (hp : 1 < p) (hLp : MemLp (X n) (ENNReal.ofReal p) μ) :
    ∀ k, k ≤ n → MemLp (finiteMax X k) (ENNReal.ofReal p) μ := by
  intro k
  induction k with
  | zero =>
    intro hk
    rw [finiteMax_zero]
    exact memLp_of_submartingaleUpTo μ ℱ X n h hnonneg p hp hLp 0 hk
  | succ k ih =>
    intro hk
    rw [finiteMax_succ]
    exact (ih (Nat.le_trans (Nat.le_succ k) hk)).sup
      (memLp_of_submartingaleUpTo μ ℱ X n h hnonneg p hp hLp (k + 1) hk)

private theorem mul_rpow_sub_one {x p : ℝ} (hx : 0 ≤ x) (hp : 1 < p) :
    x * x ^ (p - 1) = x ^ p := by
  have h := Real.rpow_one_add' hx (y := p - 1) (by linarith : 1 + (p - 1) ≠ 0)
  simpa only [add_sub_cancel] using h.symm

/-- A deterministic one-step running-maximum inequality. -/
private theorem max_rpow_step {p a y : ℝ} (hp : 1 < p) (ha : 0 ≤ a) (hy : 0 ≤ y) :
    (p - 1) * (max a y) ^ p ≤
      p * (y * (max a y) ^ (p - 1)) + (p - 1) * a ^ p -
        p * (y * a ^ (p - 1)) := by
  rcases le_total y a with hya | hay
  · rw [max_eq_left hya]
    linarith
  · rw [max_eq_right hay, mul_rpow_sub_one hy hp]
    nlinarith [young_rpow hp hy ha]

private theorem integrable_mul_rpow_nonneg {μ : Measure Ω} {p : ℝ} (hp : 1 < p)
    {f g : Ω → ℝ} (hf : MemLp f (ENNReal.ofReal p) μ)
    (hg : MemLp g (ENNReal.ofReal p) μ) (hg0 : 0 ≤ᵐ[μ] g) :
    Integrable (fun ω => f ω * g ω ^ (p - 1)) μ := by
  apply (integrable_mul_rpow hp hf hg).congr
  filter_upwards [hg0] with ω hω
  rw [abs_of_nonneg hω]

private theorem integrable_rpow_nonneg {μ : Measure Ω} {p : ℝ} (hp : 0 < p)
    {g : Ω → ℝ} (hg : MemLp g (ENNReal.ofReal p) μ) (hg0 : 0 ≤ᵐ[μ] g) :
    Integrable (fun ω => g ω ^ p) μ := by
  have hi : Integrable (fun ω => ‖g ω‖ ^ p) μ := by
    simpa only [ENNReal.toReal_ofReal hp.le] using
      (integrable_norm_rpow_iff hg.aestronglyMeasurable
        (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top).2 hg
  apply hi.congr
  filter_upwards [hg0] with ω hω
  rw [Real.norm_of_nonneg hω]

omit m in
theorem le_finiteMax (X : ℕ → Ω → ℝ) {k n : ℕ} (hk : k ≤ n) (ω : Ω) :
    X k ω ≤ finiteMax X n ω := by
  exact Finset.le_sup' (fun k => X k ω) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))

theorem measurable_finiteMax (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ)
    (h : ∀ k, k ≤ n → Measurable[ℱ k] (X k)) : Measurable[ℱ n] (finiteMax X n) := by
  let : MeasurableSpace Ω := ℱ n
  exact Finset.measurable_range_sup'' fun k hk => (h k hk).mono (ℱ.mono hk) le_rfl

/-- The predictable multiplier may be unbounded: the actual product
integrability assumptions suffice for the pull-out identity. -/
private theorem integral_mul_le_of_condExp_le (μ : Measure Ω)
    {m' : MeasurableSpace Ω} (hm : m' ≤ m) [SigmaFinite (μ.trim hm)]
    {w f g : Ω → ℝ} (hw : StronglyMeasurable[m'] w) (hw0 : 0 ≤ᵐ[μ] w)
    (hg : Integrable g μ) (hwf : Integrable (w * f) μ) (hwg : Integrable (w * g) μ)
    (hle : f ≤ᵐ[μ] μ[g | m']) :
    (∫ ω, w ω * f ω ∂μ) ≤ ∫ ω, w ω * g ω ∂μ := by
  have heq := condExp_mul_of_stronglyMeasurable_left hw hwg hg
  have hi : Integrable (w * μ[g | m']) μ := integrable_condExp.congr heq
  calc
    (∫ ω, w ω * f ω ∂μ) ≤ ∫ ω, w ω * μ[g | m'] ω ∂μ := by
      apply integral_mono_ae hwf hi
      filter_upwards [hw0, hle] with ω h0 hω
      exact mul_le_mul_of_nonneg_left hω h0
    _ = ∫ ω, w ω * g ω ∂μ := by
      exact (integral_congr_ae heq).symm.trans (integral_condExp hm)

/-- The mixed-moment form of the sharp maximal inequality. Its proof uses
the deterministic maximum recursion and nonnegative predictable multipliers. -/
private theorem maximal_mixed_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ)
    (h : IsSubmartingaleUpTo X ℱ μ n)
    (hnonneg : ∀ k, k ≤ n → 0 ≤ᵐ[μ] X k)
    (p : ℝ) (hp : 1 < p) (hLp : MemLp (X n) (ENNReal.ofReal p) μ) :
    (p - 1) * (∫ ω, finiteMax X n ω ^ p ∂μ) ≤
      p * (∫ ω, X n ω * finiteMax X n ω ^ (p - 1) ∂μ) := by
  let Z := finiteMax X
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hZ0 : ∀ k, k ≤ n → 0 ≤ᵐ[μ] Z k := by
    intro k _
    filter_upwards [hnonneg 0 (Nat.zero_le n)] with ω hω
    exact hω.trans (le_finiteMax X (Nat.zero_le k) ω)
  have hZLp := memLp_finiteMax_of_submartingaleUpTo μ ℱ X n h hnonneg p hp hLp
  have hXLp := memLp_of_submartingaleUpTo μ ℱ X n h hnonneg p hp hLp
  have hpow : ∀ k, k ≤ n → Integrable (fun ω => Z k ω ^ p) μ :=
    fun k hk => integrable_rpow_nonneg hp0 (hZLp k hk) (hZ0 k hk)
  have hprod : ∀ i j, i ≤ n → j ≤ n →
      Integrable (fun ω => X i ω * Z j ω ^ (p - 1)) μ :=
    fun i j hi hj => integrable_mul_rpow_nonneg hp (hXLp i hi) (hZLp j hj) (hZ0 j hj)
  have hclaim : ∀ k, k ≤ n → (p - 1) * (∫ ω, Z k ω ^ p ∂μ) ≤
      p * (∫ ω, X k ω * Z k ω ^ (p - 1) ∂μ) := by
    intro k
    induction k with
    | zero =>
      intro hk
      have heq : (∫ ω, X 0 ω * Z 0 ω ^ (p - 1) ∂μ) = ∫ ω, Z 0 ω ^ p ∂μ := by
        apply integral_congr_ae
        filter_upwards [hnonneg 0 hk] with ω hω
        change X 0 ω * finiteMax X 0 ω ^ (p - 1) = finiteMax X 0 ω ^ p
        rw [finiteMax_zero]
        exact mul_rpow_sub_one hω hp
      rw [heq]
      have hpos : 0 ≤ ∫ ω, Z 0 ω ^ p ∂μ :=
        integral_nonneg_of_ae ((hZ0 0 hk).mono fun _ hω => Real.rpow_nonneg hω _)
      nlinarith
    | succ k ih =>
      intro hk
      have hk' : k ≤ n := (Nat.le_succ k).trans hk
      have hweight : (∫ ω, X k ω * Z k ω ^ (p - 1) ∂μ) ≤
          ∫ ω, X (k + 1) ω * Z k ω ^ (p - 1) ∂μ := by
        have hw : StronglyMeasurable[ℱ k] (fun ω => Z k ω ^ (p - 1)) :=
          ((measurable_finiteMax ℱ X k (fun j hj => h.1 j (hj.trans hk'))).pow_const _).stronglyMeasurable
        have hi := integral_mul_le_of_condExp_le μ (ℱ.le k) hw
          ((hZ0 k hk').mono fun _ hω => Real.rpow_nonneg hω _)
          (h.2.1 (k + 1) hk)
          (by simpa only [Pi.mul_def, mul_comm] using hprod k k hk' hk')
          (by simpa only [Pi.mul_def, mul_comm] using hprod (k + 1) k hk hk')
          (h.2.2 k (Nat.lt_of_succ_le hk))
        simpa only [mul_comm] using hi
      have hi1 := (hprod (k + 1) (k + 1) hk hk).const_mul p
      have hi2 := (hpow k hk').const_mul (p - 1)
      have hi3 := (hprod (k + 1) k hk hk').const_mul p
      have hstep := integral_mono_ae ((hpow (k + 1) hk).const_mul (p - 1))
        ((hi1.fun_add hi2).sub hi3) (by
          filter_upwards [hZ0 k hk', hnonneg (k + 1) hk] with ω hω hnext
          change (p - 1) * Z (k + 1) ω ^ p ≤
            p * (X (k + 1) ω * Z (k + 1) ω ^ (p - 1)) +
              (p - 1) * Z k ω ^ p - p * (X (k + 1) ω * Z k ω ^ (p - 1))
          simpa only [Z, finiteMax_succ] using max_rpow_step hp hω hnext)
      simp only [Pi.sub_apply] at hstep
      simp only [integral_sub (hi1.fun_add hi2) hi3, integral_add hi1 hi2,
        integral_const_mul] at hstep
      have hprev := ih hk'
      nlinarith
  exact hclaim n le_rfl

/-- The p-th moment version, with the sharp factor `(p/(p-1))^p`. -/
private theorem maximal_power_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ)
    (h : IsSubmartingaleUpTo X ℱ μ n)
    (hnonneg : ∀ k, k ≤ n → 0 ≤ᵐ[μ] X k)
    (p : ℝ) (hp : 1 < p) (hLp : MemLp (X n) (ENNReal.ofReal p) μ) :
    (∫ ω, finiteMax X n ω ^ p ∂μ) ≤
      (p / (p - 1)) ^ p * (∫ ω, X n ω ^ p ∂μ) := by
  let Z := finiteMax X n
  let q := p / (p - 1)
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hqp : q * (p - 1) = p := by dsimp [q]; field_simp
  have hZ0 : 0 ≤ᵐ[μ] Z := (hnonneg 0 (Nat.zero_le n)).mono fun ω hω =>
    hω.trans (le_finiteMax X (Nat.zero_le n) ω)
  have hZLp := memLp_finiteMax_of_submartingaleUpTo μ ℱ X n h hnonneg p hp hLp n le_rfl
  have hiX := integrable_rpow_nonneg hp0 hLp (hnonneg n le_rfl)
  have hiZ := integrable_rpow_nonneg hp0 hZLp hZ0
  have hiXZ := integrable_mul_rpow_nonneg hp hLp hZLp hZ0
  have hi1 := hiX.const_mul (q ^ p)
  have hi2 := hiZ.const_mul (p - 1)
  have hy := integral_mono_ae (hiXZ.const_mul (p * q)) (hi1.fun_add hi2) (by
    filter_upwards [hnonneg n le_rfl, hZ0] with ω hX hZ
    have hpoint := young_rpow hp (mul_nonneg hq0 hX) hZ
    rw [Real.mul_rpow hq0 hX] at hpoint
    change (p * q) * (X n ω * Z ω ^ (p - 1)) ≤
      q ^ p * X n ω ^ p + (p - 1) * Z ω ^ p
    nlinarith)
  simp only [integral_add hi1 hi2, integral_const_mul] at hy
  have hmix := maximal_mixed_moment μ ℱ X n h hnonneg p hp hLp
  have hscaled := mul_le_mul_of_nonneg_left hmix hq0
  change (∫ ω, Z ω ^ p ∂μ) ≤ q ^ p * (∫ ω, X n ω ^ p ∂μ)
  change q * ((p - 1) * (∫ ω, Z ω ^ p ∂μ)) ≤
    q * (p * (∫ ω, X n ω * Z ω ^ (p - 1) ∂μ)) at hscaled
  change p * q * (∫ ω, X n ω * Z ω ^ (p - 1) ∂μ) ≤
    q ^ p * (∫ ω, X n ω ^ p ∂μ) + (p - 1) * (∫ ω, Z ω ^ p ∂μ) at hy
  rw [← mul_assoc, hqp] at hscaled
  nlinarith only [hy, hscaled]

private theorem lpNorm_nonneg_eq (μ : Measure Ω) {f : Ω → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) μ) (hf0 : 0 ≤ᵐ[μ] f) :
    lpNorm f (ENNReal.ofReal p) μ = (∫ ω, f ω ^ p ∂μ) ^ p⁻¹ := by
  rw [lpNorm_eq_integral_norm_rpow_toReal
    (ne_of_gt (ENNReal.ofReal_pos.mpr hp)) ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  congr 1
  apply integral_congr_ae
  filter_upwards [hf0] with ω hω
  rw [Real.norm_of_nonneg hω]

/-- Doob's sharp finite-horizon Lp inequality, including membership of the
maximum and almost-sure nonnegativity. -/
theorem strong_maximal (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (n : ℕ)
    (h : IsSubmartingaleUpTo X ℱ μ n)
    (hnonneg : ∀ k, k ≤ n → 0 ≤ᵐ[μ] X k)
    (p : ℝ) (hp : 1 < p) (hLp : MemLp (X n) (ENNReal.ofReal p) μ) :
    MemLp (finiteMax X n) (ENNReal.ofReal p) μ ∧
    lpNorm (finiteMax X n) (ENNReal.ofReal p) μ ≤
      (p / (p - 1)) * lpNorm (X n) (ENNReal.ofReal p) μ := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  have hq0 : 0 ≤ p / (p - 1) := by positivity
  have hZ0 : 0 ≤ᵐ[μ] finiteMax X n := (hnonneg 0 (Nat.zero_le n)).mono fun ω hω =>
    hω.trans (le_finiteMax X (Nat.zero_le n) ω)
  have hZLp := memLp_finiteMax_of_submartingaleUpTo μ ℱ X n h hnonneg p hp hLp n le_rfl
  refine ⟨hZLp, ?_⟩
  rw [lpNorm_nonneg_eq μ hp0 hZLp hZ0,
    lpNorm_nonneg_eq μ hp0 hLp (hnonneg n le_rfl)]
  have hXZ := maximal_power_moment μ ℱ X n h hnonneg p hp hLp
  have hXpos : 0 ≤ ∫ ω, X n ω ^ p ∂μ :=
    integral_nonneg_of_ae ((hnonneg n le_rfl).mono fun _ hω => Real.rpow_nonneg hω _)
  have hZpos : 0 ≤ ∫ ω, finiteMax X n ω ^ p ∂μ :=
    integral_nonneg_of_ae (hZ0.mono fun _ hω => Real.rpow_nonneg hω _)
  have hroot := Real.rpow_le_rpow hZpos hXZ (inv_nonneg.mpr hp0.le)
  rwa [Real.mul_rpow (Real.rpow_nonneg hq0 p) hXpos,
    Real.rpow_rpow_inv hq0 hp0.ne'] at hroot

/-- Conditional Jensen for absolute value turns any finite real martingale
into a nonnegative finite submartingale. -/
theorem abs_submartingaleUpTo (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (n : ℕ)
    (h : IsMartingaleUpTo M ℱ μ n) :
    IsSubmartingaleUpTo (fun k ω => |M k ω|) ℱ μ n := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    let : MeasurableSpace Ω := ℱ k
    simpa only [Real.norm_eq_abs] using (h.1 k hk).norm
  · intro k hk
    exact (h.2.1 k hk).abs
  · intro k hk
    have hJ := abs_condExp_ae_le_condExp_abs (μ := μ) (m := ℱ k) (M (k + 1))
    filter_upwards [h.2.2 k hk, hJ] with ω heq hineq
    simpa only [Pi.abs_apply, Pi.abs_def, heq] using hineq

/-- The real martingale form of the same sharp bound. -/
theorem strong_maximal_martingale (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (M : ℕ → Ω → ℝ) (n : ℕ)
    (h : IsMartingaleUpTo M ℱ μ n)
    (p : ℝ) (hp : 1 < p) (hLp : MemLp (M n) (ENNReal.ofReal p) μ) :
    MemLp (finiteMax (fun k ω => |M k ω|) n) (ENNReal.ofReal p) μ ∧
    lpNorm (finiteMax (fun k ω => |M k ω|) n) (ENNReal.ofReal p) μ ≤
      (p / (p - 1)) * lpNorm (M n) (ENNReal.ofReal p) μ := by
  have hs := strong_maximal μ ℱ (fun k ω => |M k ω|) n
    (abs_submartingaleUpTo μ ℱ M n h)
    (fun k _ => Filter.Eventually.of_forall fun ω => abs_nonneg (M k ω)) p hp
    (by simpa only [Real.norm_eq_abs] using hLp.norm)
  simpa only [lpNorm_fun_abs hLp.aestronglyMeasurable] using hs

end P207
