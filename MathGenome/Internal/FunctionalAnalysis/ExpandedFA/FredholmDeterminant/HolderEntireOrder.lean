import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FredholmDeterminant.HolderEntireOrder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.HolderDeterminantBound
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FredholmDeterminant.ClassicalEntireSeries
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open MeasureTheory Filter
open scoped Topology
namespace ExpandedFA.FredholmDeterminant.HolderEntireOrder

/-- The supremum in the order definition is the actual disk maximum. -/
theorem diskMaximum_identification : Spec.DiskMaximumIdentification := by
  intro f hf r hr
  obtain ⟨z, hz, heq, hmax⟩ := (isCompact_closedBall (0 : ℂ) r).exists_sSup_image_eq_and_ge
    ⟨0, by simpa using hr⟩ hf.norm.continuousOn
  exact ⟨z, by simpa using hz, heq, fun w hw => hmax w (by simpa using hw)⟩

lemma diskMaximum_le {f : ℂ → ℂ} {r B : ℝ} (hr : 0 ≤ r)
    (h : ∀ z : ℂ, ‖z‖ ≤ r → ‖f z‖ ≤ B) : Spec.diskMaximum f r ≤ B := by
  apply csSup_le
  · exact ⟨‖f 0‖, 0, by simpa using hr, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact h z (by simpa using hz)

/-- An exponential growth bound implies the source's log-log order bound. -/
lemma order_le_of_growth {f : ℂ → ℂ} {ρ C : ℝ}
    (hρ : 0 ≤ ρ) (hC : 1 ≤ C)
    (h : ∀ r : ℝ, 1 ≤ r → ∀ z : ℂ, ‖z‖ ≤ r →
      ‖f z‖ ≤ Real.exp (C * r ^ ρ)) : Spec.entireOrder f ≤ (ρ : EReal) := by
  have hbound : ∀ᶠ r : ℝ in atTop,
      Spec.orderQuotient f r ≤ ρ + Real.log C / Real.log r := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
    have hr0 : 0 < r := lt_trans zero_lt_one hr
    have hlog : 0 < Real.log r := Real.log_pos hr
    have hCr : 1 ≤ C * r ^ ρ := by
      exact one_le_mul_of_one_le_of_one_le hC (Real.one_le_rpow hr.le hρ)
    have hm : max (Real.exp 1) (Spec.diskMaximum f r) ≤ Real.exp (C * r ^ ρ) :=
      max_le (Real.exp_le_exp.mpr hCr) (diskMaximum_le hr0.le (h r hr.le))
    have hm0 : 0 < max (Real.exp 1) (Spec.diskMaximum f r) :=
      (Real.exp_pos 1).trans_le (le_max_left _ _)
    have hml : 1 ≤ Real.log (max (Real.exp 1) (Spec.diskMaximum f r)) := by
      simpa using Real.log_le_log (Real.exp_pos 1) (le_max_left (Real.exp 1) (Spec.diskMaximum f r))
    have hh := Real.log_le_log (lt_of_lt_of_le zero_lt_one hml)
      (show Real.log (max (Real.exp 1) (Spec.diskMaximum f r)) ≤ C * r ^ ρ by
        simpa using Real.log_le_log hm0 hm)
    rw [Real.log_mul (by linarith : C ≠ 0) (ne_of_gt (Real.rpow_pos_of_pos hr0 ρ)),
      Real.log_rpow hr0] at hh
    unfold Spec.orderQuotient
    apply (div_le_iff₀ hlog).mpr
    calc
      _ ≤ Real.log C + ρ * Real.log r := hh
      _ = (ρ + Real.log C / Real.log r) * Real.log r := by field_simp; ring
  have ht : Tendsto (fun r : ℝ => ρ + Real.log C / Real.log r) atTop (𝓝 ρ) := by
    simpa using tendsto_const_nhds.add
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.log C) atTop (𝓝 (Real.log C))).div_atTop
        Real.tendsto_log_atTop)
  have htE : Tendsto (fun r : ℝ => ((ρ + Real.log C / Real.log r : ℝ) : EReal))
      atTop (𝓝 (ρ : EReal)) := EReal.tendsto_coe.mpr ht
  exact (limsup_le_limsup (hbound.mono fun _ hr => EReal.coe_le_coe_iff.mpr hr)).trans_eq
    htE.limsup_eq

lemma entireOrder_nonneg (f : ℂ → ℂ) : 0 ≤ Spec.entireOrder f := by
  refine le_limsup_of_frequently_le ?_ (isBoundedUnder_of ⟨⊤, fun _ => le_top⟩)
  apply Filter.Eventually.frequently
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with r hr
  apply EReal.coe_nonneg.mpr
  apply div_nonneg _ (Real.log_pos hr).le
  apply Real.log_nonneg
  simpa using Real.log_le_log (Real.exp_pos 1)
    (le_max_left (Real.exp 1) (Spec.diskMaximum f r))

/-- The disk supremum for the original Fredholm function is attained. -/
lemma fredholm_diskMaximum_attained (a b : ℝ)
    (μ : Measure (Spec.Interval a b)) [IsFiniteMeasure μ]
    (k : C(Spec.Interval a b × Spec.Interval a b, ℂ)) (r : ℝ) (hr : 0 ≤ r) :
    ∃ z : ℂ, ‖z‖ ≤ r ∧
      Spec.diskMaximum (ClassicalDefinitions.Spec.FredholmDeterminantValue μ k) r =
        ‖ClassicalDefinitions.Spec.FredholmDeterminantValue μ k z‖ ∧
      ∀ w : ℂ, ‖w‖ ≤ r →
        ‖ClassicalDefinitions.Spec.FredholmDeterminantValue μ k w‖ ≤
          ‖ClassicalDefinitions.Spec.FredholmDeterminantValue μ k z‖ :=
  diskMaximum_identification _ (ClassicalEntireSeries.entire_functions μ k).1.continuous r hr

/-- A geometric majorant for a power series with fractional-factorial decay. -/
lemma powerSeries_growth {d : ℕ → ℂ} {β C A : ℝ}
    (hβ : 0 < β) (hC : 1 ≤ C) (hA : 1 ≤ A)
    (hd : ∀ n, ‖d n‖ ≤ C * A ^ n / (n.factorial : ℝ) ^ β) :
    ∃ G : ℝ, 1 ≤ G ∧ ∀ r : ℝ, 1 ≤ r → ∀ z : ℂ, ‖z‖ ≤ r →
      ‖∑' n : ℕ, z ^ n * d n‖ ≤ Real.exp (G * r ^ (1 / β)) := by
  let ρ := 1 / β
  let G := 2 * C + β * (2 * A) ^ ρ
  have hρ : 0 < ρ := one_div_pos.mpr hβ
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  refine ⟨G, by dsimp [G]; have hp := mul_nonneg hβ.le (Real.rpow_nonneg (by positivity : 0 ≤ 2 * A) ρ); linarith, ?_⟩
  intro r hr z hz
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let s := (2 * A * r) ^ ρ
  have hs : 0 < s := Real.rpow_pos_of_pos (by positivity) _
  have hspow : s ^ β = 2 * A * r := by
    rw [show s ^ β = ((2 * A * r) ^ ρ) ^ β from rfl,
      ← Real.rpow_mul (by positivity)]
    simp [ρ, ne_of_gt hβ]
  have hterm (n : ℕ) : ‖z ^ n * d n‖ ≤
      C * Real.exp (β * s) * (1 / 2 : ℝ) ^ n := by
    have hfact : 0 < (n.factorial : ℝ) := by positivity
    have he := Real.rpow_le_rpow (by positivity : 0 ≤ s ^ n / (n.factorial : ℝ))
      (Real.pow_div_factorial_le_exp s hs.le n) hβ.le
    rw [Real.div_rpow (by positivity) hfact.le,
      ← Real.rpow_natCast_mul hs.le, mul_comm (n : ℝ) β,
      Real.rpow_mul_natCast hs.le, hspow, ← Real.exp_mul, mul_comm s β] at he
    calc
      ‖z ^ n * d n‖ = ‖z‖ ^ n * ‖d n‖ := by simp
      _ ≤ r ^ n * (C * A ^ n / (n.factorial : ℝ) ^ β) := by gcongr; exact hd n
      _ = C * (1 / 2 : ℝ) ^ n *
          ((2 * A * r) ^ n / (n.factorial : ℝ) ^ β) := by
        rw [mul_pow, mul_pow]
        have htwo : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
        calc
          _ = C * ((1 / 2 : ℝ) ^ n * 2 ^ n) * A ^ n * r ^ n /
              (n.factorial : ℝ) ^ β := by rw [htwo]; ring
          _ = _ := by ring
      _ ≤ C * (1 / 2 : ℝ) ^ n * Real.exp (β * s) :=
        mul_le_mul_of_nonneg_left he (by positivity)
      _ = _ := by ring
  have hg : HasSum (fun n : ℕ => C * Real.exp (β * s) * (1 / 2 : ℝ) ^ n)
      (2 * C * Real.exp (β * s)) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (C * Real.exp (β * s)) using 1; ring
  calc
    ‖∑' n : ℕ, z ^ n * d n‖ ≤ 2 * C * Real.exp (β * s) :=
      tsum_of_norm_bounded hg hterm
    _ ≤ Real.exp (2 * C) * Real.exp (β * s) := by
      exact mul_le_mul_of_nonneg_right (le_trans (by linarith : 2 * C ≤ 2 * C + 1) (Real.add_one_le_exp (2 * C))) (Real.exp_pos _).le
    _ = Real.exp (2 * C + β * s) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (G * r ^ ρ) := by
      apply Real.exp_le_exp.mpr
      have hrr : 1 ≤ r ^ ρ := Real.one_le_rpow hr hρ.le
      have hsr : s = (2 * A) ^ ρ * r ^ ρ := Real.mul_rpow (by positivity) hr0.le
      rw [hsr]
      dsimp [G]
      nlinarith

lemma nat_le_two_pow_real (n : ℕ) : (n : ℝ) ≤ 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Nat.cast_add_one, pow_succ]
    have hp : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    linarith

/-- Elementary estimates on the factorial and on the n-1 successive gaps. -/
lemma coarse_weight_bound {K α : ℝ} (hK : 1 ≤ K) (hα : 0 < α) (hα1 : α ≤ 1)
    (n : ℕ) (hn : 2 ≤ n) :
    K ^ (2 * n) / (n.factorial : ℝ) * (n : ℝ) ^ ((n : ℝ) / 2) *
        (K / ((n - 1 : ℕ) : ℝ)) ^ (α * ((n - 1 : ℕ) : ℝ)) ≤
      (Real.exp (3 * Real.log K + 1 + 2 * Real.log 2)) ^ n /
        (n.factorial : ℝ) ^ (α + 1 / 2) := by
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hnm : (0 : ℝ) < ((n-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n-1 by omega)
  have hnmval : ((n-1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ n by omega)]; norm_num
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hln : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hlK : 0 ≤ Real.log K := Real.log_nonneg hK
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hFhi : Real.log (n.factorial : ℝ) ≤ (n : ℝ) * Real.log n := by
    have hfhi : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    simpa [Real.log_pow] using Real.log_le_log hf hfhi
  have hFlo : (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
    have hh := Real.log_le_log (by positivity : 0 < (n : ℝ) ^ n / (n.factorial : ℝ))
      (Real.pow_div_factorial_le_exp (n : ℝ) hn0.le n)
    rw [Real.log_div (by positivity) hf.ne', Real.log_pow, Real.log_exp] at hh
    linarith
  have hlogn : Real.log n ≤ (n : ℝ) * Real.log 2 := by
    simpa [Real.log_pow] using Real.log_le_log hn0 (nat_le_two_pow_real n)
  have hloggap : Real.log n - Real.log 2 ≤ Real.log ((n-1 : ℕ) : ℝ) := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hh := Real.log_le_log (by positivity : (0 : ℝ) < (n : ℝ) / 2)
      (show (n : ℝ) / 2 ≤ ((n-1 : ℕ) : ℝ) by rw [hnmval]; linarith)
    rwa [Real.log_div hn0.ne' (by norm_num)] at hh
  have hαn : α * ((n : ℝ) - 1) ≤ n := by nlinarith
  have hkpart : α * ((n : ℝ) - 1) * Real.log K ≤ (n : ℝ) * Real.log K :=
    mul_le_mul_of_nonneg_right hαn hlK
  have hFpart : (α - 1 / 2) * Real.log (n.factorial : ℝ) ≤
      (α - 1 / 2) * ((n : ℝ) * Real.log n) + (n : ℝ) / 2 := by
    have hδ : 0 ≤ (n : ℝ) * Real.log n - Real.log (n.factorial : ℝ) := sub_nonneg.mpr hFhi
    have hδn : (n : ℝ) * Real.log n - Real.log (n.factorial : ℝ) ≤ n := by linarith
    nlinarith [mul_nonneg hα.le hδ]
  have hgpart : α * (n : ℝ) * Real.log n -
      α * ((n : ℝ)-1) * Real.log ((n-1 : ℕ) : ℝ) ≤ 2 * (n : ℝ) * Real.log 2 := by
    have hg := mul_le_mul_of_nonneg_left hloggap (by positivity : 0 ≤ α * ((n : ℝ)-1))
    have han := mul_le_mul_of_nonneg_right hα1 hln
    have ha2 := mul_le_mul_of_nonneg_right hαn hl2.le
    nlinarith
  apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
  simp (disch := positivity) only [Real.log_mul,
    Real.log_div, Real.log_pow,
    Real.log_rpow hn0, Real.log_rpow (div_pos hK0 hnm), Real.log_rpow hf,
    Real.log_exp]
  rw [hnmval] at hgpart ⊢
  push_cast
  nlinarith

/-- Positive comparison constants avoid excluding zero mass or vanishing bounds. -/
lemma coefficient_factorial_bound {a b : ℝ} (hab : a < b)
    (μ : Measure (Spec.Interval a b)) [IsFiniteMeasure μ]
    (k : C(Spec.Interval a b × Spec.Interval a b, ℂ)) (M H α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1)
    (hM : HolderDeterminantBound.Spec.Bounded k M)
    (hH : HolderDeterminantBound.Spec.HolderSecond k H α ∨
      HolderDeterminantBound.Spec.HolderFirst k H α) :
    ∃ C A : ℝ, 1 ≤ C ∧ 1 ≤ A ∧ ∀ n,
      ‖ClassicalDefinitions.Spec.DeterminantTermValue μ k 1 n‖ ≤
        C * A ^ n / (n.factorial : ℝ) ^ (α + 1 / 2) := by
  let m := μ.real Set.univ
  let L := b-a
  let K := 1 + |m| + |M| + |H| + |L|
  have hK : 1 ≤ K := by dsimp [K]; linarith [abs_nonneg m, abs_nonneg M, abs_nonneg H, abs_nonneg L]
  have hmK : |m| ≤ K := by dsimp [K]; linarith [abs_nonneg M, abs_nonneg H, abs_nonneg L]
  have hMK : |M| ≤ K := by dsimp [K]; linarith [abs_nonneg m, abs_nonneg H, abs_nonneg L]
  have hHK : |H| ≤ K := by dsimp [K]; linarith [abs_nonneg m, abs_nonneg M, abs_nonneg L]
  have hLK : L ≤ K := by dsimp [K]; linarith [abs_nonneg m, abs_nonneg M, abs_nonneg H, le_abs_self L]
  let A := Real.exp (3 * Real.log K + 1 + 2 * Real.log 2)
  have hA : 1 ≤ A := by
    apply Real.one_le_exp_iff.mpr
    have := Real.log_nonneg hK
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  let d : ℕ → ℂ := ClassicalDefinitions.Spec.DeterminantTermValue μ k 1
  have hlarge (n : ℕ) (hn : 2 ≤ n) : ‖d n‖ ≤ A ^ n / (n.factorial : ℝ) ^ (α + 1 / 2) := by
    have hnm : (0 : ℝ) < ((n-1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n-1 by omega)
    have hK0 : 0 ≤ K := le_trans zero_le_one hK
    have hL : 0 ≤ L := sub_nonneg.mpr hab.le
    have hb := HolderDeterminantBound.coefficient_bound a b hab μ k M H α hα hα1 hM hH n hn
    have hgap : 0 ≤ (L / ((n-1 : ℕ) : ℝ)) ^ (α * ((n-1 : ℕ) : ℝ)) :=
      Real.rpow_nonneg (div_nonneg hL hnm.le) _
    dsimp only [L] at hgap
    have hpow : K * K ^ (n-1) = K ^ n := by
      rw [← pow_succ']
      congr 1
      omega
    calc
      ‖d n‖ ≤ m ^ n / (n.factorial : ℝ) *
          HolderDeterminantBound.Spec.bound a b M H α n := hb
      _ ≤ |m ^ n / (n.factorial : ℝ) *
          HolderDeterminantBound.Spec.bound a b M H α n| := le_abs_self _
      _ = |m| ^ n / (n.factorial : ℝ) * (n : ℝ) ^ ((n : ℝ) / 2) *
          |M| * |H| ^ (n-1) * (L / ((n-1 : ℕ) : ℝ)) ^ (α * ((n-1 : ℕ) : ℝ)) := by
        simp only [HolderDeterminantBound.Spec.bound, abs_mul, abs_div, abs_pow,
          abs_of_nonneg (Nat.cast_nonneg n.factorial : (0 : ℝ) ≤ _), abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ _) ((n : ℝ) / 2)),
          abs_of_nonneg hgap]
        dsimp only [L]
        ring
      _ ≤ K ^ n / (n.factorial : ℝ) * (n : ℝ) ^ ((n : ℝ) / 2) *
          K * K ^ (n-1) * (K / ((n-1 : ℕ) : ℝ)) ^ (α * ((n-1 : ℕ) : ℝ)) := by
        gcongr
      _ = K ^ (2*n) / (n.factorial : ℝ) * (n : ℝ) ^ ((n : ℝ) / 2) *
          (K / ((n-1 : ℕ) : ℝ)) ^ (α * ((n-1 : ℕ) : ℝ)) := by
        rw [two_mul, pow_add]
        calc
          _ = K ^ n * (K * K ^ (n-1)) / (n.factorial : ℝ) *
              (n : ℝ) ^ ((n : ℝ) / 2) *
              (K / ((n-1 : ℕ) : ℝ)) ^ (α * ((n-1 : ℕ) : ℝ)) := by ring
          _ = _ := by rw [hpow]
      _ ≤ _ := coarse_weight_bound hK hα hα1 n hn
  let C := 1 + ‖d 0‖ + ‖d 1‖
  have hC : 1 ≤ C := by dsimp [C]; linarith [norm_nonneg (d 0), norm_nonneg (d 1)]
  refine ⟨C, A, hC, hA, ?_⟩
  intro n
  change ‖d n‖ ≤ _
  rcases n with _ | n
  · simpa using (show ‖d 0‖ ≤ C by dsimp [C]; linarith [norm_nonneg (d 1)])
  rcases n with _ | n
  · simp only [Nat.reduceAdd, Nat.factorial_one, Nat.cast_one, Real.one_rpow, pow_one, div_one]
    have hd1 : ‖d 1‖ ≤ C := by dsimp [C]; linarith [norm_nonneg (d 0)]
    exact hd1.trans (le_mul_of_one_le_right (by linarith) hA)
  · exact (hlarge (n+2) (by omega)).trans
      (div_le_div_of_nonneg_right
        (le_mul_of_one_le_left (by positivity) hC) (by positivity))

/-- The source bound on entire-function order, for either Holder variable. -/
theorem order_bound : Spec.OrderBound := by
  intro a b hab μ _ k M H α hα hα1 hM hH
  obtain ⟨C, A, hC, hA, hd⟩ := coefficient_factorial_bound hab μ k M H α hα hα1 hM hH
  obtain ⟨G, hG, hg⟩ := powerSeries_growth (by linarith : 0 < α + 1 / 2) hC hA hd
  apply order_le_of_growth (by positivity : 0 ≤ 1 / (α + 1 / 2)) hG
  intro r hr z hz
  have heq : ClassicalDefinitions.Spec.FredholmDeterminantValue μ k z =
      ∑' n : ℕ, z ^ n * ClassicalDefinitions.Spec.DeterminantTermValue μ k 1 n := by
    apply tsum_congr
    intro n
    exact HolderDeterminantBound.coefficient_identification a b μ k z n
  rw [heq]
  exact hg r hr z hz

/-- A zero Holder constant gives a determinant polynomial of degree at most one. -/
theorem zero_holder_polynomial : Spec.ZeroHolderPolynomial := by
  intro a b hab μ _ k M α hα hα1 hM hH z
  have ht (n : ℕ) (hn : 2 ≤ n) :
      ClassicalDefinitions.Spec.DeterminantTermValue μ k z n = 0 := by
    have hb := HolderDeterminantBound.coefficient_bound a b hab μ k M 0 α hα hα1 hM hH n hn
    have hz1 : ClassicalDefinitions.Spec.DeterminantTermValue μ k 1 n = 0 := by
      apply norm_le_zero_iff.mp
      simpa [HolderDeterminantBound.Spec.bound, zero_pow (by omega : n-1 ≠ 0)] using hb
    rw [HolderDeterminantBound.coefficient_identification a b μ k z n, hz1, mul_zero]
  change (∑' n, ClassicalDefinitions.Spec.DeterminantTermValue μ k z n) = _
  rw [tsum_eq_sum (s := Finset.range 2) (fun n hn => ht n (by simpa only [Finset.mem_range, not_lt] using hn))]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [(ClassicalDefinitions.zeroth_terms μ k).2.2.1 z,
    HolderDeterminantBound.coefficient_identification a b μ k z 1, pow_one]

/-- A kernel bounded by zero has Fredholm determinant identically one. -/
theorem zero_bound_constant : Spec.ZeroBoundConstant := by
  intro a b μ k hM z
  have hk : k = 0 := by
    ext p
    exact norm_le_zero_iff.mp (hM p.1 p.2)
  have ht (n : ℕ) (hn : n ≠ 0) :
      ClassicalDefinitions.Spec.DeterminantTermValue μ k z n = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hmatrix (t : Fin (j+1) → Spec.Interval a b) :
        ClassicalDefinitions.Spec.KernelMatrixValue k (j+1) t = 0 := by
      ext i l
      change k (t i, t l) = 0
      rw [hk]
      rfl
    change (-z) ^ (j+1) / ((j+1).factorial : ℂ) *
      (∫ t, (ClassicalDefinitions.Spec.KernelMatrixValue k (j+1) t).det
        ∂ClassicalDefinitions.Spec.MeasurePowerValue μ (j+1)) = 0
    simp only [hmatrix, Matrix.det_zero, integral_zero, mul_zero]
  change (∑' n, ClassicalDefinitions.Spec.DeterminantTermValue μ k z n) = 1
  rw [tsum_eq_single 0 ht]
  exact (ClassicalDefinitions.zeroth_terms μ k).2.2.1 z

/-- The complete improved Fredholm bound, retaining the exact gap estimate. -/
theorem improved_fredholm_bound : Spec.FullImprovedFredholmBound :=
  ⟨HolderDeterminantBound.second_variable_bound,
    HolderDeterminantBound.first_variable_bound,
    HolderDeterminantBound.coefficient_identification,
    HolderDeterminantBound.coefficient_bound, order_bound⟩

end ExpandedFA.FredholmDeterminant.HolderEntireOrder
